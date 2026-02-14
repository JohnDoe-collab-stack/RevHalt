#[derive(Clone, Debug)]
pub struct BitRow {
    blocks: Vec<u64>, // ceil(n/64)
}

impl BitRow {
    pub fn new(n: usize) -> Self {
        let m = (n + 63) / 64;
        Self { blocks: vec![0u64; m] }
    }
    #[inline] pub fn set(&mut self, j: usize) {
        self.blocks[j >> 6] |= 1u64 << (j & 63);
    }
    #[inline] pub fn test(&self, j: usize) -> bool {
        (self.blocks[j >> 6] >> (j & 63)) & 1 == 1
    }
    #[inline] pub fn and_inplace(&mut self, other: &BitRow) {
        for (a,b) in self.blocks.iter_mut().zip(other.blocks.iter()) { *a &= *b; }
    }
    #[inline] pub fn or_inplace(&mut self, other: &BitRow) {
        for (a,b) in self.blocks.iter_mut().zip(other.blocks.iter()) { *a |= *b; }
    }
    #[inline] pub fn is_empty(&self) -> bool { self.blocks.iter().all(|&x| x==0) }
    pub fn iter_ones(&self) -> impl Iterator<Item=usize> + '_ {
        self.blocks.iter().enumerate().flat_map(|(bi, &w)| {
            let mut x = w;
            std::iter::from_fn(move || {
                if x == 0 { return None; }
                let t = x.trailing_zeros() as usize;
                x &= x - 1;
                Some((bi<<6) + t)
            })
        })
    }
}

#[derive(Clone, Debug)]
pub struct Rel {
    pub n: usize,
    pub rows: Vec<BitRow>,
}

impl Rel {
    pub fn empty(n: usize) -> Self {
        Self { n, rows: (0..n).map(|_| BitRow::new(n)).collect() }
    }
    pub fn id(n: usize) -> Self {
        let mut r = Self::empty(n);
        for i in 0..n { r.rows[i].set(i); }
        r
    }
    pub fn set(&mut self, i: usize, j: usize) { self.rows[i].set(j); }

    pub fn transpose(&self) -> Rel {
        let mut t = Rel::empty(self.n);
        for i in 0..self.n {
            for j in self.rows[i].iter_ones() {
                if j < self.n { t.set(j, i); }
            }
        }
        t
    }

    // Composition relationnelle: (A ∘ B)[i,k] = ∃j A[i,j]∧B[j,k]
    // Dense bitset: row_i = OR_{j in A.row(i)} B.row(j)
    pub fn comp(a: &Rel, b: &Rel) -> Rel {
        assert_eq!(a.n, b.n);
        let n = a.n;
        let mut out = Rel::empty(n);
        for i in 0..n {
            let mut row = BitRow::new(n);
            for j in a.rows[i].iter_ones() {
                row.or_inplace(&b.rows[j]);
            }
            out.rows[i] = row;
        }
        out
    }

    // Restriction: zero rows/cols en dehors des fibres
    pub fn restrict(&mut self, src: &BitRow, tgt: &BitRow) {
        // kill rows not in src
        for i in 0..self.n {
            if !src.test(i) {
                self.rows[i] = BitRow::new(self.n);
            } else {
                // and with tgt as column mask
                self.rows[i].and_inplace(tgt);
            }
        }
    }
}
