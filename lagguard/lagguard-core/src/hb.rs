use std::collections::VecDeque;

#[derive(Clone, Debug)]
pub struct HbClosure {
    // reach[i] = bitset des sommets atteignables depuis i
    pub n: usize,
    pub reach: Vec<Vec<u64>>,
}

fn bitset_new(n: usize) -> Vec<u64> { vec![0u64; (n+63)/64] }
fn bitset_set(bs: &mut [u64], j: usize) { bs[j>>6] |= 1u64<<(j&63); }
fn bitset_test(bs: &[u64], j: usize) -> bool { ((bs[j>>6]>>(j&63))&1)==1 }
fn bitset_or_inplace(a: &mut [u64], b: &[u64]) { for (x,y) in a.iter_mut().zip(b) { *x |= *y; } }

pub fn hb_closure(n: usize, edges: &[(usize,usize)]) -> HbClosure {
    // adjacency + indegree
    let mut out = vec![vec![]; n];
    let mut indeg = vec![0usize; n];
    for &(u,v) in edges {
        out[u].push(v);
        indeg[v] += 1;
    }
    // topo
    let mut q = VecDeque::new();
    for i in 0..n { if indeg[i]==0 { q.push_back(i); } }
    let mut topo = Vec::with_capacity(n);
    while let Some(u) = q.pop_front() {
        topo.push(u);
        for &v in &out[u] {
            indeg[v]-=1;
            if indeg[v]==0 { q.push_back(v); }
        }
    }

    // reachability: process reverse topo
    let mut reach = (0..n).map(|_| bitset_new(n)).collect::<Vec<_>>();
    for &u in topo.iter().rev() {
        for &v in &out[u] {
            bitset_set(&mut reach[u], v);
            // u reaches whatever v reaches
            let rv = reach[v].clone();
            bitset_or_inplace(&mut reach[u], &rv);
        }
    }

    HbClosure { n, reach }
}

impl HbClosure {
    pub fn reaches(&self, a: usize, b: usize) -> bool { bitset_test(&self.reach[a], b) }
}
