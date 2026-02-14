use crate::{model::Model, types::*};

pub fn build_sigma_paths(model: &Model) -> Vec<Vec<EventId>> {
    let mut out = Vec::new();
    for e in &model.events {
        // policy: steps = writes + unlock/commit
        let is_crit = !e.writes.is_empty() || e.kind == "Unlock" || e.kind == "Commit";
        if is_crit {
            out.push(vec![e.id.clone()]);
        }
    }
    out
}
