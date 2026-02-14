use crate::analyze::LagWitness;
use serde::Serialize;

#[derive(Serialize)]
pub struct WitnessReport {
    pub kind: &'static str,
    pub swap: (String,String),
    pub x: u32,
    pub x_prime: u32,
    pub y: u32,
    pub sigma_index: usize,
    pub note: String,
}

pub fn to_report(w: &LagWitness) -> WitnessReport {
    WitnessReport {
        kind: "LagWitness",
        swap: (w.cell.swap.0.clone(), w.cell.swap.1.clone()),
        x: w.x,
        x_prime: w.x_prime,
        y: w.y,
        sigma_index: w.sigma_index,
        note: "Holonomy relates x~x' now, but Sigma step differs => LagEventΣ witness".to_string()
    }
}
