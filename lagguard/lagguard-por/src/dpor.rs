use lagguard_core::{model::Model, analyze::Cell, types::EventId, hb::HbClosure, prefix::Prefix};
use crate::indep::indep;
use anyhow::Result;
use std::collections::{HashSet, VecDeque, HashMap};

#[derive(Clone)]
struct Node {
    prefix_obj: Prefix, // bitset state
    trace: Vec<EventId>,
}

fn enabled(model: &Model, prefix: &Prefix) -> Vec<EventId> {
    let mut out = Vec::new();
    // iterate all events, check if not done AND all predecessors done
    for (i, e) in model.events.iter().enumerate() {
        if prefix.test(i) { continue; }
        
        let mut ready = true;
        // check if all HB predecessors are in prefix
        // Optimization: precompute predecessors or use closure?
        // Closure is heavy for just one step check, use direct edges from model.hb
        for &(u, v) in &model.hb {
            if v == i {
                if !prefix.test(u) {
                    ready = false; 
                    break;
                }
            }
        }
        if ready {
            out.push(e.id.clone());
        }
    }
    out
}

pub fn explore_cells_with_hb(model: &Model, hb: &HbClosure, horizon: usize) -> Result<Vec<Cell>> {
    let mut cells: Vec<Cell> = Vec::new();
    let n_ev = model.events.len();

    let mut q = VecDeque::new();
    q.push_back(Node { prefix_obj: Prefix::empty(n_ev), trace: vec![] });

    // seen prefixes to pruning (simple state visiting)
    let mut seen = HashSet::<Prefix>::new();
    
    let mut count = 0;
    while let Some(node) = q.pop_back() {
        if node.trace.len() >= horizon { continue; }
        if !seen.insert(node.prefix_obj.clone()) { continue; }
        
        count += 1;
        if count > 50000 { break; } // Safety

        let en = enabled(model, &node.prefix_obj);

        for eid in en {
            let mut next = node.clone();
            let e_idx = model.event_index[&eid];
            next.prefix_obj.set(e_idx);
            next.trace.push(eid.clone());

            let t = &next.trace;
            if t.len() >= 2 {
                let a = &t[t.len()-2];
                let b = &t[t.len()-1];
                if indep(hb, model, a, b) {
                    // Canon prefixes
                    // src = prefix before a,b
                    // But here node.prefix_obj includes a,b.
                    // We can re-construct src bitset by unsetting a and b
                    let mut src_p = next.prefix_obj.clone();
                    // clearing bits is tricky with simple set(), need unset. 
                    // Re-make from previous step? 
                    // Easier: logic is (node) -> +a -> (next). 
                    // We stand at (node) which has `a` enabled? No, wait.
                    // trace is [... a, b]. 
                    // `node` was prefix before `b`. `node` has `a` done.
                    // `prev_node` (parent of node) had neither done.
                    // Let's compute src ID properly:
                    //   src = current_prefix \ {a, b}
                    //   tgt = current_prefix
                    // We need a proper Prefix::unset or copy
                    // For MVP string ID:
                    
                    // Actually, cells are defined on valid execution prefixes.
                    // We found a trace ending in ... ab.
                    // The "cell" starts at state (trace without a,b).
                    // This state must exist and be reachable.
                    
                    // Let's rely on the prefix logic:
                    let src_id = "pfx_dynamic".to_string(); // Placeholder for MVP logic complexity
                    let tgt_id = next.prefix_obj.id(); // This is K

                    cells.push(Cell {
                        src: src_id, 
                        tgt: tgt_id,
                        p: vec![a.clone(), b.clone()],
                        q: vec![b.clone(), a.clone()],
                        swap: (a.clone(), b.clone()),
                    });
                }
            }
            q.push_back(next);
        }
    }

    // Dedup
    cells.sort_by(|c1,c2| (c1.p.clone(), c1.q.clone()).cmp(&(c2.p.clone(), c2.q.clone())));
    cells.dedup_by(|a,b| a.p==b.p && a.q==b.q);
    Ok(cells)
}
