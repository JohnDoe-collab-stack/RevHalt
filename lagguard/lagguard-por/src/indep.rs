use lagguard_core::{model::Model, types::*, hb::HbClosure};

pub fn indep(hb: &HbClosure, model: &Model, a: &EventId, b: &EventId) -> bool {
    let ia = model.event_index[a];
    let ib = model.event_index[b];
    
    // Check reachability in closure
    if hb.reaches(ia, ib) || hb.reaches(ib, ia) { return false; }

    let ea = &model.events[ia];
    let eb = &model.events[ib];

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
