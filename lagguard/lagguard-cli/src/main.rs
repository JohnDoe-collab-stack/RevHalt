use anyhow::{Context, Result};
use lagguard_core::{
    types::ModelJson, 
    model::Model, 
    analyze::detect_lag,
    hb::hb_closure,
    sigma::build_sigma_paths,
    report::to_report
};
use lagguard_por::dpor::explore_cells_with_hb;
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

    // 1. Build HB Closure
    println!("Building HB transitive closure...");
    let hb = hb_closure(model.events.len(), &model.hb);

    // 2. Explore cells
    println!("Exploring state space (horizon=500)...");
    let cells = explore_cells_with_hb(&model, &hb, 500)?;
    println!("Found {} cells.", cells.len());

    // 3. Auto-generate Sigma (writes + sync)
    // Note: we can also include explicit sigma from model if desired, but request says "Sigma auto"
    let mut sigma_paths = build_sigma_paths(&model);
    // Add explicit ones too
    for s in &model.sigma {
        if let Some(p) = &s.step_path {
            if !p.is_empty() { sigma_paths.push(p.clone()); }
        }
    }

    println!("Using {} sigma probe kinds.", sigma_paths.len());

    // 4. Detect Lag
    match detect_lag(&model, &cells, &sigma_paths) {
        Ok(()) => { 
            println!("✅ LagFreeSigma (on abstract model)"); 
        }
        Err(w) => {
            println!("❌ LagWitness detected");
            println!("Swap: {:?} <-> {:?}", w.cell.swap.0, w.cell.swap.1);
            
            let report = to_report(&w);
            let report_json = serde_json::to_string_pretty(&report)?;
            
            fs::write("witness.json", report_json).context("Failed to write witness.json")?;
            println!("Written witness.json");
            std::process::exit(2);
        }
    }
    Ok(())
}
