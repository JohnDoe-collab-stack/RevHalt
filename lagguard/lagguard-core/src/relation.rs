use bit_vec::BitVec;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Rel {
    pub width: usize,
    pub height: usize,
    pub rows: Vec<BitVec>,
}

impl Rel {
    pub fn new(width: usize, height: usize) -> Self {
        Rel {
            width,
            height,
            rows: vec![BitVec::from_elem(width, false); height],
        }
    }

    pub fn id(size: usize) -> Self {
        let mut rel = Rel::new(size, size);
        for i in 0..size {
            rel.rows[i].set(i, true);
        }
        rel
    }

    pub fn set(&mut self, row: usize, col: usize, val: bool) {
        if row < self.height && col < self.width {
            self.rows[row].set(col, val);
        }
    }

    pub fn get(&self, row: usize, col: usize) -> bool {
        if row < self.height && col < self.width {
            self.rows[row].get(col).unwrap_or(false)
        } else {
            false
        }
    }

    pub fn compose(&self, other: &Rel) -> Option<Rel> {
        if self.width != other.height {
            return None;
        }
        let mut result = Rel::new(other.width, self.height);
        
        for i in 0..self.height {
            for j in 0..self.width {
                if self.get(i, j) {
                    // result[i] |= other[j]
                    let other_row = &other.rows[j];
                    result.rows[i].union(other_row);
                }
            }
        }
        Some(result)
    }

    pub fn transpose(&self) -> Rel {
        let mut result = Rel::new(self.height, self.width);
        for i in 0..self.height {
            for j in 0..self.width {
                if self.get(i, j) {
                    result.set(j, i, true);
                }
            }
        }
        result
    }

    pub fn from_pairs(size: usize, pairs: &[(usize, usize)]) -> Self {
        let mut rel = Rel::new(size, size);
        for &(src, dst) in pairs {
            rel.set(src, dst, true);
        }
        rel
    }
