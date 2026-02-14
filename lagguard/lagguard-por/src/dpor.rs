use lagguard_core::{model::Model, analyze::Cell, types::EventId};
use crate::indep::indep;
use anyhow::Result;
use std::collections::{HashSet, VecDeque};

#[derive(Clone)]
struct Node {
    config: HashSet<EventId>, // events executed
    trace: Vec<EventId>,
}

fn enabled(model: &Model, config: &HashSet<EventId>) -> Vec<EventId> {
    // enabled = events not in config whose HB predecessors are all in config
    let mut out = Vec::new();
    'ev: for e in &model.events {
        if config.contains(&e.id) { continue; }
        // check hb predecessors: for any (pred -> e), pred must be in config
        let ie = model.event_index[&e.id];
        for &(ip, iq) in &model.hb {
            if iq == ie {
                let pred_id = &model.events[ip].id;
                if !config.contains(pred_id) { continue 'ev; }
            }
        }
        out.push(e.id.clone());
    }
    out
}

// MVP exploration: BFS/DFS with bounded horizon, record adjacent indep swaps from traces
pub fn explore_cells(model: &Model, horizon: usize) -> Result<Vec<Cell>> {
    let mut cells: Vec<Cell> = Vec::new();

    let mut q = VecDeque::new();
    q.push_back(Node { config: HashSet::new(), trace: vec![] });

    // simple visited (config hash) to avoid repeats; MVP can be coarse
    // We use sorted vec of event IDs as key for visited
    let mut seen = HashSet::<Vec<EventId>>::new();
    
    // Keep track of total states explored to prevent infinite loops if horizon doesn't bite
    let mut count = 0;
    
    while let Some(node) = q.pop_back() {
        if node.trace.len() >= horizon { continue; }

        let mut key = node.config.iter().cloned().collect::<Vec<_>>();
        key.sort();
        if !seen.insert(key) { continue; }
        
        count += 1;
        if count > 100000 { break; } // Safety cap

        let en = enabled(model, &node.config);

        for e in en {
            let mut next = node.clone();
            next.config.insert(e.clone());
            next.trace.push(e.clone());

            // collect adjacent indep swap cells from the new trace
            let t = &next.trace;
            if t.len() >= 2 {
                let a = &t[t.len()-2];
                let b = &t[t.len()-1];
                if indep(model, a, b) {
                    // cell at local prefix: p=[a,b], q=[b,a]
                    cells.push(Cell {
                        src: "pfxH".to_string(), // MVP: you can synthesize prefix ids later
                        tgt: "pfxK".to_string(),
                        p: vec![a.clone(), b.clone()],
                        q: vec![b.clone(), a.clone()],
                        swap: (a.clone(), b.clone()),
                    });
                }
            }

            q.push_back(next);
        }
    }

    // Deduplicate cells by (swap,p,q)
    cells.sort_by(|c1,c2| (c1.p.clone(), c1.q.clone()).cmp(&(c2.p.clone(), c2.q.clone())));
    cells.dedup_by(|a,b| a.p==b.p && a.q==b.q);
    Ok(cells)
}
