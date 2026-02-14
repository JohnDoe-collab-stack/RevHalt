use crate::types::*;
use std::hash::{Hash, Hasher};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Prefix {
    pub done: Vec<u64>, // bitset events
}

impl Prefix {
    pub fn empty(n_events: usize) -> Self {
        Self { done: vec![0u64; (n_events+63)/64] }
    }
    pub fn set(&mut self, eidx: usize) { self.done[eidx>>6] |= 1u64<<(eidx&63); }
    pub fn test(&self, eidx: usize) -> bool { ((self.done[eidx>>6]>>(eidx&63))&1)==1 }
    
    pub fn id(&self) -> PrefixId {
        use std::collections::hash_map::DefaultHasher;
        let mut h = DefaultHasher::new();
        self.done.hash(&mut h);
        format!("h{:016x}", h.finish())
    }
}
