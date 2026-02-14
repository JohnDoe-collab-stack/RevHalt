use anyhow::Result;
use lagguard_core::{types::ModelJson, model::Model, analyze::detect_lag};
use lagguard_por::dpor::explore_cells;

fn main() -> Result<()> {
    let path = std::env::args().nth(1).expect("usage: lagc <model.json>");
    let data = std::fs::read_to_string(path)?;
    let mj: ModelJson = serde_json::from_str(&data)?;
    let model = Model::from_json(mj)?;

    println!("Loaded model with {} events.", model.events.len());

    // build cells
    println!("Exploring state space (horizon=200)...");
    let cells = explore_cells(&model, 200)?;
    println!("Found {} cells.", cells.len());

    // sigma paths: MVP = take sigma.step_path if present, else empty
    let sigma_paths: Vec<Vec<String>> = model.sigma.iter()
        .map(|s| s.step_path.clone().unwrap_or_default())
        .collect();

    match detect_lag(&model, &cells, &sigma_paths) {
        Ok(()) => { 
            println!("✅ LagFreeSigma (MVP)"); 
            // Emit cert if requested (mock for now)
        }
        Err(w) => {
            println!("❌ LagWitness");
            println!("cell swap = {:?}, x={}, x'={}, sigma#={}", w.cell.swap, w.x, w.x_prime, w.sigma_index);
            // Serialize full witness to file for inspection
             let witness_json = serde_json::json!({
                "version": "0.1",
                "result": "LagWitness",
                "cell": {
                    "p": w.cell.p,
                    "q": w.cell.q,
                    "swap": w.cell.swap
                },
                "states": {
                    "x": w.x,
                    "x_prime": w.x_prime
                },
                "sigma_index": w.sigma_index,
                "explain": "Lag detected."
            });
            println!("{}", serde_json::to_string_pretty(&witness_json)?);
            std::process::exit(2);
        }
    }
    Ok(())
}
