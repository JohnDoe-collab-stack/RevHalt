use crate::{model::Model, rel::{Rel, BitRow}, fiber::fiber_all, types::*};

#[derive(Clone, Debug)]
pub struct Cell {
    pub src: PrefixId,
    pub tgt: PrefixId,
    pub p: Vec<EventId>,
    pub q: Vec<EventId>,
    pub swap: (EventId, EventId),
}

pub fn tr_path(model: &Model, p: &[EventId], src_f: &BitRow, tgt_f: &BitRow) -> Rel {
    let mut r = Rel::id(model.n);
    for e in p {
        let pe = model.post_of(e);
        r = Rel::comp(&r, pe);
    }
    r.restrict(src_f, tgt_f);
    r
}

pub fn holonomy(tr_p: &Rel, tr_q: &Rel) -> Rel {
    let tr_q_t = tr_q.transpose();
    Rel::comp(tr_p, &tr_q_t)
}

pub fn compatible(tr_step: &Rel, x: usize) -> bool {
    !tr_step.rows[x].is_empty()
}

#[derive(Clone, Debug)]
pub struct Sig {
    pub bits: Vec<u64>, // bitset length = |Σ|
}

impl Sig {
    pub fn new(m: usize) -> Self {
        let blocks = (m + 63)/64;
        Self { bits: vec![0u64; blocks] }
    }
    pub fn set(&mut self, i: usize, v: bool) {
        let b = i >> 6;
        let k = i & 63;
        if v { self.bits[b] |= 1u64<<k; } else { self.bits[b] &= !(1u64<<k); }
    }
    pub fn eq(&self, other: &Sig) -> bool { self.bits == other.bits }
}

pub fn sig_sigma(model: &Model, sigma_paths: &[Vec<EventId>], fiber: &BitRow, x: usize) -> Sig {
    let mut s = Sig::new(sigma_paths.len());
    for (i, step) in sigma_paths.iter().enumerate() {
        let tr = tr_path(model, step, fiber, fiber); // step part d’un h et revient sur même fibre (MVP)
        s.set(i, compatible(&tr, x));
    }
    s
}

#[derive(Clone, Debug)]
pub struct LagWitness {
    pub cell: Cell,
    pub x: u32,
    pub x_prime: u32,
    pub y: u32,
    pub sigma_index: usize,
}

pub fn detect_lag(
    model: &Model,
    cells: &[Cell],
    sigma_paths: &[Vec<EventId>],
) -> Result<(), LagWitness> {

    let fiber = fiber_all(&model.domain); // MVP: même fibre partout
    // précompute signatures
    let n = model.n;
    let mut sigs: Vec<Sig> = Vec::with_capacity(n);
    for x in 0..n { sigs.push(sig_sigma(model, sigma_paths, &fiber, x)); }

    for cell in cells {
        let trp = tr_path(model, &cell.p, &fiber, &fiber);
        let trq = tr_path(model, &cell.q, &fiber, &fiber);
        let hol = holonomy(&trp, &trq);

        for x in fiber.iter_ones() {
            let row = &hol.rows[x];
            for xp in row.iter_ones() {
                if xp == x { continue; }
                if !fiber.test(xp) { continue; }
                if !sigs[x].eq(&sigs[xp]) {
                    // find which sigma differs
                    let mut idx = 0usize;
                    'outer: for b in 0..sigs[x].bits.len() {
                        let diff = sigs[x].bits[b] ^ sigs[xp].bits[b];
                        if diff != 0 {
                            let k = diff.trailing_zeros() as usize;
                            idx = (b<<6) + k;
                            break 'outer;
                        }
                    }
                    // witness y: pick any y satisfying Tr(p)x y and Tr(q)xp y
                    // implement by scanning y in 0..n
                    let mut y_w = None;
                    for y in 0..n {
                        if trp.rows[x].test(y) && trq.rows[xp].test(y) {
                            y_w = Some(y as u32);
                            break;
                        }
                    }
                    let y = y_w.unwrap_or(0);
                    return Err(LagWitness {
                        cell: cell.clone(),
                        x: x as u32,
                        x_prime: xp as u32,
                        y,
                        sigma_index: idx,
                    });
                }
            }
        }
    }
    Ok(())
}
