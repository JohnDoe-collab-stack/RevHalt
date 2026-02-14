use crate::model::{EventId, Model, RelationEncoding, StateId, SigmaEvent};
use crate::relation::Rel;
use std::collections::{HashMap, HashSet};

pub struct Analysis<'a> {
    model: &'a Model,
    post_relations: HashMap<EventId, Rel>,
    pub state_space_size: usize,
}

impl<'a> Analysis<'a> {
    pub fn new(model: &'a Model) -> Self {
        let mut post_relations = HashMap::new();
        // Determine state space size. model.post usually contains sparse pairs.
        // We need to know N. For now, we assume implicit N or derive it from Max StateId + 1.
        // Or strictly from AbstractDomain definition.
        // Let's guess max state id from posts + 1 for MVP safety, or use a fixed size if known.
        let mut max_id = 0;
        for p in &model.post {
            match &p.relation {
                RelationEncoding::SparsePairs { pairs } => {
                    for &(src, dst) in pairs {
                        if src > max_id { max_id = src; }
                        if dst > max_id { max_id = dst; }
                    }
                }
                RelationEncoding::BitMatrix { rows, width } => {
                     // approximation
                     max_id = *width - 1; 
                }
            }
        }
        let size = max_id + 1;

        for p in &model.post {
             match &p.relation {
                RelationEncoding::SparsePairs { pairs } => {
                    post_relations.insert(p.event.clone(), Rel::from_pairs(size, pairs));
                }
                _ => unimplemented!("BitMatrix import not yet implemented"),
            }
        }

        Analysis {
            model,
            post_relations,
            state_space_size: size,
        }
    }

    pub fn compute_tr(&self, path: &[EventId]) -> Option<Rel> {
        let mut tr = Rel::id(self.state_space_size);
        for e in path {
            if let Some(rel) = self.post_relations.get(e) {
                tr = tr.compose(rel)?;
            } else {
                // Identity for events without explicit post? Or Error?
                // Assume identity for unlisted events (e.g. pure control flow without state effect?)
                // Spec says "Post defined for each event".
                // We'll return None or warn. For now, assume identity if missing is dangerous but maybe intended for filtered models.
                // Let's error.
                return None; 
            }
        }
        Some(tr)
    }

    pub fn compute_hol(&self, p: &[EventId], q: &[EventId]) -> Option<Rel> {
        let tr_p = self.compute_tr(p)?;
        let tr_q = self.compute_tr(q)?;
        let tr_q_t = tr_q.transpose();
        tr_p.compose(&tr_q_t)
    }

    // Check if x and x' have same Sigma compatibility
    // compatible(sigma, x) = exists y, Tr(sigma)[x, y]
    pub fn compare_sigma(&self, x: StateId, x_prime: StateId) -> Option<String> {
        for sigma in &self.model.sigma {
            // Assume single step sigma for now as per "sigma_events"
            // If sigma is a path, we need compute_tr(&[sigma.id]).
            // Model has sigma as "SigmaEvent", which links to an event ID or is abstract?
            // "SigmaEvent { id: "sigma0", kind: "Write", ... }"
            // This usually refers to a hypothetical step. In the model `events`, are these included?
            // Or are they separate "future tests"?
            // Spec 8.1 says: "pour chaque sigma, Compatible(stepSigma, x)".
            // Let's assume there's a Post relation for sigma.id as well.
            
            // We need to find if there is ANY transition from x valid for sigma.
            // compatible(x) = !row(Tr(sigma))[x].is_empty() (if targeting "any" valid state or fiber target)
            // "Compatible(stepSigma, x) = exists y, Tr(stepSigma) x y"
            
            // Note: if model.sigma references IDs in model.events or model.post, we use them.
            if let Some(rel) = self.post_relations.get(&sigma.id) {
                // Check if row x has any bit set
                let mut x_compat = false;
                 if let Some(row) = rel.rows.get(x) {
                     if row.any() { x_compat = true; }
                 }

                let mut x_prime_compat = false;
                 if let Some(row) = rel.rows.get(x_prime) {
                     if row.any() { x_prime_compat = true; }
                 }

                if x_compat != x_prime_compat {
                    return Some(sigma.id.clone());
                }
            }
        }
        None
    }

    // Returns (sigma_id, x, x') if lag detected
    pub fn detect_lag_on_cell(&self, p: &[EventId], q: &[EventId], fiber: &[StateId]) -> Option<(String, StateId, StateId)> {
        let hol = self.compute_hol(p, q)?;
        
        for &x in fiber {
            // Find all x' such that Hol(x, x')
            if let Some(row) = hol.rows.get(x) {
                for x_prime in 0..self.state_space_size {
                    if row.get(x_prime).unwrap_or(false) {
                        if x != x_prime {
                             // Check sigma compatibility
                             if let Some(sigma_id) = self.compare_sigma(x, x_prime) {
                                 return Some((sigma_id, x, x_prime));
                             }
                        }
                    }
                }
            }
        }
        None
    }
}
