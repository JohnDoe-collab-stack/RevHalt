use lagguard_core::model::Model;
use lagguard_core::types::*;

pub fn indep(model: &Model, a: &EventId, b: &EventId) -> bool {
    // HB check: if direct edge exists, not independent strategies usually assume HB check is top level
    // DPOR rule often implies if e, f are co-enabled, they are not HB related.
    // So we primarily check read/write conflicts.
    
    // Safety check HB:
    if hb_edge(model, a, b) || hb_edge(model, b, a) { return false; }

    let ia = model.event_index.get(a).unwrap();
    let ib = model.event_index.get(b).unwrap();
    let ea = &model.events[*ia];
    let eb = &model.events[*ib];

    // W(a) disjoint (R(b) U W(b))
    for r in &ea.writes {
        if eb.reads.contains(r) || eb.writes.contains(r) { return false; }
    }
    
    // W(b) disjoint (R(a) U W(a))
    for r in &eb.writes {
        if ea.reads.contains(r) || ea.writes.contains(r) { return false; }
    }
    
    true
}

fn hb_edge(model: &Model, a: &EventId, b: &EventId) -> bool {
    let ia = *model.event_index.get(a).unwrap();
    let ib = *model.event_index.get(b).unwrap();
    model.hb.iter().any(|&(x,y)| x==ia && y==ib)
}
