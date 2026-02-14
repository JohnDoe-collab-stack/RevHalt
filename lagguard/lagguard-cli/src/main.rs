use anyhow::{Context, Result};
use lagguard_core::{types::ModelJson, model::Model, analyze::detect_lag};
use lagguard_por::dpor::explore_cells;
use std::env;
use std::fs;

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: lagc <model.json>");
        std::process::exit(1);
    }
    let path = &args[1];
    
    let data = fs::read_to_string(path).with_context(|| format!("Failed to read {}", path))?;
    let mj: ModelJson = serde_json::from_str(&data).context("Failed to parse JSON")?;
    let model = Model::from_json(mj).context("Failed to build Model")?;

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
        }
        Err(w) => {
            println!("❌ LagWitness");
            println!("cell swap = {:?}, x={}, x'={}, sigma#={}", w.cell.swap, w.x, w.x_prime, w.sigma_index);
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
