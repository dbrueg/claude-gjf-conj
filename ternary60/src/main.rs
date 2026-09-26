//! Witten index of the N=1 SVOA attached to a self-dual ternary code, and the TMF test
//! 24/gcd(24,k) | I(C) for length n = 12k (k = 5: 24 | I at length 60).
//!
//! Model (see ../notes/ternary-code-index.md):
//!   L_C = (1/√3){y ∈ Z^n : y mod 3 ∈ C}, V_{L_C} ⊃ V_{√3Z}^{⊗n} with diagonal N=1 structure, c = n.
//!   RR character = cwe_C(η, 0, e^{-iπ/3}η)/η^n  (after normalising a full-weight word to 1), so
//!       I(C) = Σ_{ε ∈ C ∩ {1,2}^n} (−1)^{d(ε,ε0)/3}  =  Σ_{A ⊂ [n], 1_A ∈ C'} (−1)^{|A|/3},
//!   C' = diag(ε0)·C ∋ 1.  I(C) = 0 when C has no full-weight word.
//!
//! Vectors in F_3^n are bitsliced: (a, b) = (positions with value 1, positions with value 2).
//! Only std is used (no crates), so the build needs no network.

use std::collections::HashMap;
use std::env;
use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::thread;

// ------------------------------------------------------------------------------------------
// F_3 vectors
// ------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct V {
    a: u128,
    b: u128,
}

impl V {
    const ZERO: V = V { a: 0, b: 0 };
    #[inline(always)]
    fn add(self, o: V) -> V {
        let t = (self.a | o.b) ^ (self.b | o.a);
        V { a: (self.b | o.b) ^ t, b: (self.a | o.a) ^ t }
    }
    #[inline(always)]
    fn neg(self) -> V {
        V { a: self.b, b: self.a }
    }
    #[inline(always)]
    fn sub(self, o: V) -> V {
        self.add(o.neg())
    }
    fn scale(self, s: u8) -> V {
        match s % 3 {
            0 => V::ZERO,
            1 => self,
            _ => self.neg(),
        }
    }
    fn get(&self, i: usize) -> u8 {
        if (self.a >> i) & 1 == 1 {
            1
        } else if (self.b >> i) & 1 == 1 {
            2
        } else {
            0
        }
    }
    fn set(&mut self, i: usize, v: u8) {
        let m = 1u128 << i;
        self.a &= !m;
        self.b &= !m;
        match v % 3 {
            1 => self.a |= m,
            2 => self.b |= m,
            _ => {}
        }
    }
    fn wt(&self) -> u32 {
        (self.a | self.b).count_ones()
    }
    fn dot(self, o: V) -> u8 {
        let p = (self.a & o.a).count_ones() + (self.b & o.b).count_ones();
        let q = (self.a & o.b).count_ones() + (self.b & o.a).count_ones();
        ((p + 2 * q) % 3) as u8
    }
    fn to_string(&self, n: usize) -> String {
        (0..n).map(|i| char::from(b'0' + self.get(i))).collect()
    }
    fn from_str(s: &str) -> V {
        let mut v = V::ZERO;
        for (i, ch) in s.chars().enumerate() {
            let d = ch.to_digit(10).expect("digit") as u8;
            v.set(i, d % 3);
        }
        v
    }
    /// multiply coordinate i by 2 wherever mask bit i is set
    fn flip_signs(self, mask: u128) -> V {
        V { a: (self.a & !mask) | (self.b & mask), b: (self.b & !mask) | (self.a & mask) }
    }
    fn permute(self, perm: &[usize]) -> V {
        // new coordinate perm[i] gets old coordinate i
        let mut w = V::ZERO;
        for (i, &p) in perm.iter().enumerate() {
            w.set(p, self.get(i));
        }
        w
    }
}

/// 64-bit bitsliced vector (redundancy part in the Gray-code loops)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct W {
    a: u64,
    b: u64,
}
impl W {
    const ZERO: W = W { a: 0, b: 0 };
    #[inline(always)]
    fn add(self, o: W) -> W {
        let t = (self.a | o.b) ^ (self.b | o.a);
        W { a: (self.b | o.b) ^ t, b: (self.a | o.a) ^ t }
    }
    #[inline(always)]
    fn sub(self, o: W) -> W {
        self.add(W { a: o.b, b: o.a })
    }
}

fn mask(n: usize) -> u128 {
    if n == 128 {
        !0
    } else {
        (1u128 << n) - 1
    }
}

// ------------------------------------------------------------------------------------------
// Linear algebra
// ------------------------------------------------------------------------------------------

/// Reduced row echelon form. Returns (rows, pivot columns).
fn rref(n: usize, rows_in: &[V]) -> (Vec<V>, Vec<usize>) {
    let mut rows: Vec<V> = rows_in.iter().copied().filter(|r| r.wt() > 0).collect();
    let mut piv = Vec::new();
    let mut r = 0;
    for c in 0..n {
        if r == rows.len() {
            break;
        }
        let mut found = None;
        for i in r..rows.len() {
            if rows[i].get(c) != 0 {
                found = Some(i);
                break;
            }
        }
        if let Some(i) = found {
            rows.swap(r, i);
            if rows[r].get(c) == 2 {
                rows[r] = rows[r].neg();
            }
            let pr = rows[r];
            for j in 0..rows.len() {
                if j != r {
                    let x = rows[j].get(c);
                    if x != 0 {
                        rows[j] = rows[j].sub(pr.scale(x));
                    }
                }
            }
            piv.push(c);
            r += 1;
        }
    }
    rows.truncate(r);
    (rows, piv)
}

#[derive(Clone)]
struct Code {
    n: usize,
    rows: Vec<V>, // basis
}

impl Code {
    fn new(n: usize, rows: Vec<V>) -> Code {
        let (r, _) = rref(n, &rows);
        Code { n, rows: r }
    }
    fn dim(&self) -> usize {
        self.rows.len()
    }
    fn is_self_orthogonal(&self) -> bool {
        for i in 0..self.rows.len() {
            for j in i..self.rows.len() {
                if self.rows[i].dot(self.rows[j]) != 0 {
                    return false;
                }
            }
        }
        true
    }
    fn is_self_dual(&self) -> bool {
        2 * self.dim() == self.n && self.is_self_orthogonal()
    }
    fn contains(&self, v: V) -> bool {
        let mut rows = self.rows.clone();
        rows.push(v);
        rref(self.n, &rows).0.len() == self.dim()
    }
    fn direct_sum(&self, o: &Code) -> Code {
        let mut rows = self.rows.clone();
        for r in &o.rows {
            rows.push(V { a: r.a << self.n, b: r.b << self.n });
        }
        Code::new(self.n + o.n, rows)
    }
    fn flip_signs(&self, m: u128) -> Code {
        Code::new(self.n, self.rows.iter().map(|r| r.flip_signs(m)).collect())
    }
    fn permute(&self, perm: &[usize]) -> Code {
        Code::new(self.n, self.rows.iter().map(|r| r.permute(perm)).collect())
    }
    /// systematic data: pivots, non-pivot columns, redundancy rows A_i (bit j = column np[j])
    fn systematic(&self) -> (Vec<V>, Vec<usize>, Vec<usize>, Vec<W>) {
        let (rows, piv) = rref(self.n, &self.rows);
        let np: Vec<usize> = (0..self.n).filter(|c| !piv.contains(c)).collect();
        assert!(np.len() <= 64);
        let mut a = Vec::new();
        for r in &rows {
            let mut w = W::ZERO;
            for (j, &c) in np.iter().enumerate() {
                match r.get(c) {
                    1 => w.a |= 1u64 << j,
                    2 => w.b |= 1u64 << j,
                    _ => {}
                }
            }
            a.push(w);
        }
        (rows, piv, np, a)
    }
    fn to_text(&self) -> String {
        self.rows.iter().map(|r| r.to_string(self.n)).collect::<Vec<_>>().join("\n") + "\n"
    }
    fn from_text(s: &str) -> Code {
        let rows: Vec<&str> = s.lines().map(|l| l.trim()).filter(|l| !l.is_empty() && !l.starts_with('#')).collect();
        let n = rows[0].len();
        Code::new(n, rows.iter().map(|r| V::from_str(r)).collect())
    }
}

// ------------------------------------------------------------------------------------------
// Index computation
// ------------------------------------------------------------------------------------------

/// Find one full-weight codeword (entries in {1,2}) by Gray code over m ∈ {1,2}^k.
fn find_full_weight(code: &Code) -> Option<V> {
    let (rows, _piv, np, a) = code.systematic();
    let k = rows.len();
    let fullr: u64 = if np.len() == 64 { !0 } else { (1u64 << np.len()) - 1 };
    // m = all ones: s = Σ A_i
    let mut s = W::ZERO;
    for ai in &a {
        s = s.add(*ai);
    }
    let mut m2: u64 = 0; // bits where m_i = 2
    let reconstruct = |m2: u64| -> V {
        let mut c = V::ZERO;
        for i in 0..k {
            let coef = if (m2 >> i) & 1 == 1 { 2 } else { 1 };
            c = c.add(rows[i].scale(coef));
        }
        c
    };
    if (s.a | s.b) == fullr {
        return Some(reconstruct(m2));
    }
    let total: u64 = 1u64 << k;
    for j in 1..total {
        let i = j.trailing_zeros() as usize;
        if (m2 >> i) & 1 == 0 {
            s = s.add(a[i]);
        } else {
            s = s.sub(a[i]);
        }
        m2 ^= 1u64 << i;
        if (s.a | s.b) == fullr {
            return Some(reconstruct(m2));
        }
    }
    None
}

#[derive(Debug, Clone)]
struct IndexResult {
    n: usize,
    nfull: u64,        // number of full-weight codewords = |B(C')|
    index: i128,       // Witten index (sign fixed by ε0 ↦ +1)
    hist: Vec<u64>,    // hist[w] = #{A ∈ B(C') : |A| = w}
    #[allow(dead_code)]
    eps0: Option<V>,
}

/// Count B(C') = {A : 1_A ∈ C'} for a code C' ∋ 1 (all-ones), weighted by (−1)^{|A|/3}.
/// Uses complement symmetry A ↔ [n]\A (needs n ≡ 0 mod 6) and threads over prefixes.
fn count_binary_words(code: &Code, threads: usize) -> Vec<u64> {
    let n = code.n;
    let (rows, piv, _np, a) = code.systematic();
    let k = rows.len();
    assert!(k >= 2 && k <= 63);
    // all-ones must be in the code: its info part is all-ones and redundancy all-ones
    let _ = piv;
    // fix info bit k-1 to 0 (complement symmetry), prefix bits: next T bits
    let t_bits = std::cmp::min(10, k.saturating_sub(12));
    let low = k - 1 - t_bits; // Gray-coded low bits: 0..low
    let ntasks = 1usize << t_bits;
    let next = AtomicUsize::new(0);
    let result = Mutex::new(vec![0u64; n + 1]);
    thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| {
                let mut hist = vec![0u64; n + 1];
                loop {
                    let task = next.fetch_add(1, Ordering::Relaxed);
                    if task >= ntasks {
                        break;
                    }
                    let mut s = W::ZERO;
                    let mut m: u64 = 0;
                    for tb in 0..t_bits {
                        if (task >> tb) & 1 == 1 {
                            let i = low + tb;
                            s = s.add(a[i]);
                            m |= 1u64 << i;
                        }
                    }
                    if s.b == 0 {
                        let w = m.count_ones() + s.a.count_ones();
                        hist[w as usize] += 1;
                    }
                    let total: u64 = 1u64 << low;
                    for j in 1..total {
                        let i = j.trailing_zeros() as usize;
                        let bit = 1u64 << i;
                        if m & bit == 0 {
                            s = s.add(a[i]);
                        } else {
                            s = s.sub(a[i]);
                        }
                        m ^= bit;
                        if s.b == 0 {
                            let w = m.count_ones() + s.a.count_ones();
                            hist[w as usize] += 1;
                        }
                    }
                }
                let mut r = result.lock().unwrap();
                for (x, y) in r.iter_mut().zip(hist.iter()) {
                    *x += *y;
                }
            });
        }
    });
    let half = result.into_inner().unwrap();
    // double via complement: A ↦ [n]\A has weight n - |A|
    let mut hist = vec![0u64; n + 1];
    for w in 0..=n {
        hist[w] += half[w];
        hist[n - w] += half[w];
    }
    hist
}

fn index_of(code: &Code, threads: usize) -> IndexResult {
    let n = code.n;
    assert!(code.is_self_dual(), "code is not self-dual");
    let eps0 = find_full_weight(code);
    let Some(e0) = eps0 else {
        return IndexResult { n, nfull: 0, index: 0, hist: vec![0; n + 1], eps0: None };
    };
    assert_eq!(n % 12, 0, "full-weight word forces 3 | n");
    let c2 = code.flip_signs(e0.b);
    let ones = V { a: mask(n), b: 0 };
    assert!(c2.contains(ones), "normalised code must contain all-ones");
    let hist = count_binary_words(&c2, threads);
    let mut index: i128 = 0;
    let mut nfull: u64 = 0;
    for (w, &h) in hist.iter().enumerate() {
        if h == 0 {
            continue;
        }
        assert_eq!(w % 3, 0, "weight of a codeword not divisible by 3");
        nfull += h;
        if w % 6 == 0 {
            index += h as i128;
        } else {
            index -= h as i128;
        }
    }
    IndexResult { n, nfull, index, hist, eps0 }
}

/// Independent brute force over all 3^k codewords (small k only):
/// I = Σ_{ε full weight} (−1)^{d(ε,ε0)/3}, ε0 = first full-weight word found.
fn index_brute(code: &Code) -> (u64, i128) {
    let k = code.dim();
    assert!(k <= 20);
    let rows = &code.rows;
    let full = mask(code.n);
    let mut digits = vec![0u8; k];
    let mut c = V::ZERO;
    let mut e0: Option<V> = None;
    let mut nfull = 0u64;
    let mut idx: i128 = 0;
    let total = 3u64.pow(k as u32);
    for step in 0..total {
        if step > 0 {
            // increment base-3 counter, update c
            let mut i = 0;
            loop {
                if digits[i] < 2 {
                    digits[i] += 1;
                    c = c.add(rows[i]);
                    break;
                } else {
                    digits[i] = 0;
                    c = c.add(rows[i]); // 2+1 = 0: adding once more returns to 0 multiple
                    i += 1;
                }
            }
        }
        if (c.a | c.b) == full {
            nfull += 1;
            let r = *e0.get_or_insert(c);
            let d = (c.b ^ r.b).count_ones();
            assert_eq!(d % 3, 0);
            idx += if (d / 3) % 2 == 0 { 1 } else { -1 };
        }
    }
    (nfull, idx)
}

// ------------------------------------------------------------------------------------------
// Constructions
// ------------------------------------------------------------------------------------------

fn legendre(a: i64, p: i64) -> i64 {
    let a = ((a % p) + p) % p;
    if a == 0 {
        return 0;
    }
    let mut r: i64 = 1;
    let mut base = a;
    let mut e = (p - 1) / 2;
    while e > 0 {
        if e & 1 == 1 {
            r = r * base % p;
        }
        base = base * base % p;
        e >>= 1;
    }
    if r == 1 {
        1
    } else {
        -1
    }
}

fn f3(x: i64) -> u8 {
    (((x % 3) + 3) % 3) as u8
}

fn tetracode() -> Code {
    Code::new(4, vec![V::from_str("1110"), V::from_str("0121")])
}

/// Pless symmetry code P(q), q ≡ 2 mod 3 an odd prime: [I_{q+1} | S], S the Paley conference matrix.
fn pless(q: i64) -> Code {
    let m = (q + 1) as usize;
    let n = 2 * m;
    let chi_m1 = legendre(-1, q);
    let mut rows = Vec::new();
    for i in 0..m {
        let mut v = V::ZERO;
        v.set(i, 1);
        for j in 0..m {
            let s: i64 = if i == 0 && j == 0 {
                0
            } else if i == 0 {
                1
            } else if j == 0 {
                chi_m1
            } else {
                legendre(j as i64 - i as i64, q)
            };
            v.set(m + j, f3(s));
        }
        rows.push(v);
    }
    Code::new(n, rows)
}

/// Extended quadratic residue code of length p+1 (p prime, 3 a QR mod p): search idempotent
/// e = α + β Σ_Q x^r + γ Σ_N x^r of rank (p+1)/2 and extension sign making it self-dual.
fn xqr(p: i64) -> Code {
    let pu = p as usize;
    assert_eq!(legendre(3, p), 1, "3 must be a QR mod p");
    let mut found: Option<Code> = None;
    'outer: for al in 0..3u8 {
        for be in 0..3u8 {
            for ga in 0..3u8 {
                let mut e = V::ZERO;
                for j in 0..pu {
                    let c = if j == 0 {
                        al
                    } else if legendre(j as i64, p) == 1 {
                        be
                    } else {
                        ga
                    };
                    e.set(j, c);
                }
                let shifts: Vec<V> = (0..pu)
                    .map(|s| {
                        let mut w = V::ZERO;
                        for j in 0..pu {
                            w.set((j + s) % pu, e.get(j));
                        }
                        w
                    })
                    .collect();
                let (basis, _) = rref(pu, &shifts);
                if basis.len() != (pu + 1) / 2 {
                    continue;
                }
                for sign in [1u8, 2u8] {
                    let ext: Vec<V> = basis
                        .iter()
                        .map(|r| {
                            let mut w = *r;
                            let s: u32 = (r.a.count_ones() + 2 * r.b.count_ones()) % 3;
                            w.set(pu, ((s as u8) * sign) % 3);
                            w
                        })
                        .collect();
                    let c = Code::new(pu + 1, ext);
                    if c.is_self_dual() {
                        found = Some(c);
                        break 'outer;
                    }
                }
            }
        }
    }
    found.expect("no self-dual extended QR code found")
}

// ------------------------------------------------------------------------------------------
// Random self-dual codes: symmetric Kneser-neighbour walk (stationary = uniform on self-dual codes)
// ------------------------------------------------------------------------------------------

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        // splitmix64
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn trit(&mut self) -> u8 {
        loop {
            let r = (self.next() >> 62) as u8;
            if r < 3 {
                return r;
            }
        }
    }
    fn below(&mut self, m: u64) -> u64 {
        self.next() % m
    }
}

fn random_vec(n: usize, rng: &mut Rng) -> V {
    let mut v = V::ZERO;
    for i in 0..n {
        v.set(i, rng.trit());
    }
    v
}

/// One neighbour step: uniform isotropic x ∉ C; C' = (C ∩ x^⊥) + <x>.
fn neighbor_step(code: &Code, rng: &mut Rng) -> Code {
    let n = code.n;
    loop {
        let x = random_vec(n, rng);
        if x.wt() == 0 || x.dot(x) != 0 {
            continue;
        }
        let d: Vec<u8> = code.rows.iter().map(|g| g.dot(x)).collect();
        let Some(j) = d.iter().position(|&v| v != 0) else { continue };
        let gj = code.rows[j];
        let dj = d[j];
        let mut rows = Vec::with_capacity(code.rows.len());
        for (i, g) in code.rows.iter().enumerate() {
            if i != j {
                rows.push(g.sub(gj.scale((d[i] * dj) % 3)));
            }
        }
        rows.push(x);
        let c = Code::new(n, rows);
        debug_assert!(c.is_self_dual());
        return c;
    }
}

fn random_monomial(code: &Code, rng: &mut Rng) -> Code {
    let n = code.n;
    let mut perm: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        let j = rng.below((i + 1) as u64) as usize;
        perm.swap(i, j);
    }
    let mut sg: u128 = 0;
    for i in 0..n {
        if rng.next() & 1 == 1 {
            sg |= 1u128 << i;
        }
    }
    code.permute(&perm).flip_signs(sg)
}


// ------------------------------------------------------------------------------------------
// Batch mode (one code per thread), restricted walks, double circulant codes
// ------------------------------------------------------------------------------------------

/// Basis of D^⊥ for a code D given by rows (any), length n.
fn dual_basis(n: usize, rows: &[V]) -> Vec<V> {
    let (r, piv) = rref(n, rows);
    let mut out = Vec::new();
    for j in 0..n {
        if piv.contains(&j) {
            continue;
        }
        let mut v = V::ZERO;
        v.set(j, 1);
        for (i, &p) in piv.iter().enumerate() {
            let x = r[i].get(j);
            if x != 0 {
                v.set(p, (3 - x) % 3);
            }
        }
        out.push(v);
    }
    out
}

fn random_in_span(basis: &[V], rng: &mut Rng) -> V {
    let mut v = V::ZERO;
    for b in basis {
        v = v.add(b.scale(rng.trit()));
    }
    v
}

/// Random self-dual code containing the self-orthogonal code D (greedy isotropic extension).
fn extend_to_self_dual(n: usize, d: &[V], rng: &mut Rng) -> Code {
    let mut cur: Vec<V> = rref(n, d).0;
    while 2 * cur.len() < n {
        let perp = dual_basis(n, &cur);
        loop {
            let x = random_in_span(&perp, rng);
            if x.wt() == 0 || x.dot(x) != 0 {
                continue;
            }
            let mut t = cur.clone();
            t.push(x);
            let (r, _) = rref(n, &t);
            if r.len() > cur.len() {
                cur = r;
                break;
            }
        }
    }
    let c = Code::new(n, cur);
    assert!(c.is_self_dual());
    c
}

/// Neighbour step that keeps the subcode D: x uniform isotropic in D^⊥ \ C.
fn neighbor_step_keep(code: &Code, dperp: &[V], rng: &mut Rng) -> Code {
    let n = code.n;
    loop {
        let x = random_in_span(dperp, rng);
        if x.wt() == 0 || x.dot(x) != 0 {
            continue;
        }
        let d: Vec<u8> = code.rows.iter().map(|g| g.dot(x)).collect();
        let Some(j) = d.iter().position(|&v| v != 0) else { continue };
        let gj = code.rows[j];
        let dj = d[j];
        let mut rows = Vec::with_capacity(code.rows.len());
        for (i, g) in code.rows.iter().enumerate() {
            if i != j {
                rows.push(g.sub(gj.scale((d[i] * dj) % 3)));
            }
        }
        rows.push(x);
        return Code::new(n, rows);
    }
}

/// Subcode families used to bias the hunt towards structured codes.
fn subcode(n: usize, kind: &str) -> Vec<V> {
    let mut rows = Vec::new();
    match kind {
        "none" => {}
        "ones" => rows.push(V { a: mask(n), b: 0 }),
        "triples" => {
            // C_3^{n/3}: 1 on disjoint triples (lattice contains (A_2 x Z)^{n/3})
            for t in 0..n / 3 {
                let mut v = V::ZERO;
                for i in 0..3 {
                    v.set(3 * t + i, 1);
                }
                rows.push(v);
            }
        }
        "halftriples" => {
            for t in 0..n / 6 {
                let mut v = V::ZERO;
                for i in 0..3 {
                    v.set(3 * t + i, 1);
                }
                rows.push(v);
            }
        }
        "golay" => {
            for r in &golay().rows {
                rows.push(*r);
            }
        }
        "tetra" => {
            for r in &tetracode().rows {
                rows.push(*r);
            }
        }
        "hexads" => {
            // six disjoint weight-6 all-ones blocks
            for t in 0..n / 6 {
                let mut v = V::ZERO;
                for i in 0..6 {
                    v.set(6 * t + i, 1);
                }
                rows.push(v);
            }
        }
        other => panic!("unknown subcode {other}"),
    }
    rows
}

/// Parallel batch: each thread runs its own restricted chain; single-threaded index per code.
fn batch(n: usize, per_thread: usize, seed: u64, thin: usize, kind: &str) {
    let th = threads();
    let d = subcode(n, kind);
    let md = tmf_modulus(n);
    let stats = Mutex::new((HashMap::<i128, u64>::new(), 0u64, 0u64, Vec::<String>::new()));
    thread::scope(|sc| {
        for t in 0..th {
            let d = d.clone();
            let stats = &stats;
            sc.spawn(move || {
                let mut rng = Rng(seed.wrapping_mul(0x51_7cc1_b727_220a).wrapping_add(t as u64 * 7919));
                let dperp = dual_basis(n, &d);
                let mut c = if d.is_empty() { repeat_sum(&tetracode(), n / 4) } else { extend_to_self_dual(n, &d, &mut rng) };
                for _ in 0..(2 * n) {
                    c = if d.is_empty() { neighbor_step(&c, &mut rng) } else { neighbor_step_keep(&c, &dperp, &mut rng) };
                }
                let mut local: HashMap<i128, u64> = HashMap::new();
                let mut nviol = 0u64;
                let mut nzero_full = 0u64;
                let mut viol_files = Vec::new();
                for i in 0..per_thread {
                    for _ in 0..thin {
                        c = if d.is_empty() { neighbor_step(&c, &mut rng) } else { neighbor_step_keep(&c, &dperp, &mut rng) };
                    }
                    let r = index_of(&c, 1);
                    if r.nfull == 0 {
                        nzero_full += 1;
                    }
                    *local.entry(r.index.rem_euclid(48)).or_default() += 1;
                    if r.index % md != 0 || r.index % 24 != 0 {
                        nviol += 1;
                        let f = format!("violation_batch_n{n}_{kind}_s{seed}_t{t}_{i}.txt");
                        fs::write(&f, c.to_text()).unwrap();
                        viol_files.push(format!("{f} I={}", r.index));
                    }
                }
                let mut g = stats.lock().unwrap();
                for (k, v) in local {
                    *g.0.entry(k).or_default() += v;
                }
                g.1 += nviol;
                g.2 += nzero_full;
                g.3.extend(viol_files);
            });
        }
    });
    let (res, nviol, nzero, files) = stats.into_inner().unwrap();
    let mut rs: Vec<_> = res.into_iter().collect();
    rs.sort();
    println!(
        "SUMMARY batch n={n} subcode={kind} codes={} thin={thin} seed={seed} tmf_mod={md} no_full_weight={nzero} violations(24∤I)={nviol} residues_mod48={:?}",
        per_thread * th,
        rs
    );
    for f in files {
        println!("VIOLATION {f}");
    }
}

/// Random pure double circulant self-dual code [I_m | circ(a)], circ(a)circ(a)^T = -I.
fn random_double_circulant(m: usize, rng: &mut Rng) -> Code {
    loop {
        let mut a = vec![0u8; m];
        for x in a.iter_mut() {
            *x = rng.trit();
        }
        let mut ok = true;
        // autocorrelation
        for s in 0..=(m / 2) {
            let mut acc = 0u32;
            for j in 0..m {
                acc += (a[j] as u32) * (a[(j + s) % m] as u32);
            }
            let want = if s == 0 { 2 } else { 0 };
            if acc % 3 != want {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        let mut rows = Vec::new();
        for i in 0..m {
            let mut v = V::ZERO;
            v.set(i, 1);
            for j in 0..m {
                v.set(m + j, a[(j + m - i) % m]);
            }
            rows.push(v);
        }
        let c = Code::new(2 * m, rows);
        assert!(c.is_self_dual());
        return c;
    }
}


// ------------------------------------------------------------------------------------------
// Neighbour identity:  I(C) + I(C') = 4 F(D),  D = C ∩ C',  with GJF's global sign (−1)^{n_1}
// ------------------------------------------------------------------------------------------

/// Signed count Σ_{c ∈ span(rows), c full weight} (−1)^{n_1(c)} and the unsigned count,
/// for an arbitrary linear code (dim r ≤ 40, n − r ≤ 64).
fn signed_full(n: usize, rows_in: &[V]) -> (u64, i128) {
    let (rows, piv) = rref(n, rows_in);
    let r = rows.len();
    assert!(r <= 40 && n - r <= 64);
    let np: Vec<usize> = (0..n).filter(|c| !piv.contains(c)).collect();
    let mut a = Vec::new();
    for row in &rows {
        let mut w = W::ZERO;
        for (j, &c) in np.iter().enumerate() {
            match row.get(c) {
                1 => w.a |= 1u64 << j,
                2 => w.b |= 1u64 << j,
                _ => {}
            }
        }
        a.push(w);
    }
    let fullr: u64 = if np.len() == 64 { !0 } else { (1u64 << np.len()) - 1 };
    let mut s = W::ZERO;
    for ai in &a {
        s = s.add(*ai);
    }
    let mut m2: u64 = 0; // info coordinates equal to 2
    let mut cnt = 0u64;
    let mut sg: i128 = 0;
    let mut visit = |s: W, m2: u64| {
        if (s.a | s.b) == fullr {
            cnt += 1;
            let n1 = (r as u32 - m2.count_ones()) + s.a.count_ones();
            sg += if n1 % 2 == 0 { 1 } else { -1 };
        }
    };
    if r == 0 {
        return (0, 0);
    }
    visit(s, m2);
    let total: u64 = 1u64 << r;
    for j in 1..total {
        let i = j.trailing_zeros() as usize;
        if (m2 >> i) & 1 == 0 {
            s = s.add(a[i]);
        } else {
            s = s.sub(a[i]);
        }
        m2 ^= 1u64 << i;
        visit(s, m2);
    }
    (cnt, sg)
}

/// Random neighbour of C together with D = C ∩ x^⊥.
fn random_neighbor_with_d(code: &Code, rng: &mut Rng) -> (Code, Vec<V>) {
    let n = code.n;
    loop {
        let x = random_vec(n, rng);
        if x.wt() == 0 || x.dot(x) != 0 {
            continue;
        }
        let d: Vec<u8> = code.rows.iter().map(|g| g.dot(x)).collect();
        let Some(j) = d.iter().position(|&v| v != 0) else { continue };
        let gj = code.rows[j];
        let dj = d[j];
        let mut drows = Vec::new();
        for (i, g) in code.rows.iter().enumerate() {
            if i != j {
                drows.push(g.sub(gj.scale((d[i] * dj) % 3)));
            }
        }
        let mut rows = drows.clone();
        rows.push(x);
        return (Code::new(n, rows), drows);
    }
}

fn neighbor_identity(n: usize, pairs: usize, seed: u64) {
    let mut rng = Rng(seed);
    let mut c = repeat_sum(&tetracode(), n / 4);
    for _ in 0..(2 * n) {
        c = neighbor_step(&c, &mut rng);
    }
    let mut ok_all = true;
    let mut min_v2_fd = u32::MAX;
    for p in 0..pairs {
        let (c2, drows) = random_neighbor_with_d(&c, &mut rng);
        assert!(c2.is_self_dual());
        let (_, i1) = signed_full(n, &c.rows);
        let (_, i2) = signed_full(n, &c2.rows);
        let (nd, fd) = signed_full(n, &drows);
        let ident = i1 + i2 == 4 * fd;
        let even = fd % 2 == 0;
        // cross-check |I| against the independent fast routine
        let chk = index_of(&c, threads()).index.abs() == i1.abs();
        ok_all &= ident && even && chk;
        if fd != 0 {
            min_v2_fd = min_v2_fd.min(fd.trailing_zeros());
        }
        println!(
            "pair {p}: n={n} I(C)={i1} I(C')={i2} F(D)={fd} (#full in D={nd})  I+I'=4F(D): {ident}  F(D) even: {even}  |I| matches index_of: {chk}  I mod 8={} I' mod 8={}",
            i1.rem_euclid(8),
            i2.rem_euclid(8)
        );
        c = c2;
    }
    println!("SUMMARY neighbor identity n={n} pairs={pairs}: all hold = {ok_all}; min 2-adic valuation of nonzero F(D) = {min_v2_fd}");
    if !ok_all {
        std::process::exit(1);
    }
}


// ------------------------------------------------------------------------------------------
// Signed 2-design check:  Σ_{ε maximal} s(ε) ε_i ε_j = I δ_ij   (second proof, ternary-code-index.md §1B)
// ------------------------------------------------------------------------------------------

/// All A ⊂ [n] with 1_A ∈ C' (C' ∋ 1), as coordinate bitmasks. Single-threaded Gray code.
fn collect_binary_words(code: &Code) -> Vec<u128> {
    let (rows, piv, np, a) = code.systematic();
    let k = rows.len();
    let expand = |m: u64, sa: u64| -> u128 {
        let mut x: u128 = 0;
        for i in 0..k {
            if (m >> i) & 1 == 1 {
                x |= 1u128 << piv[i];
            }
        }
        for (j, &c) in np.iter().enumerate() {
            if (sa >> j) & 1 == 1 {
                x |= 1u128 << c;
            }
        }
        x
    };
    let mut out = Vec::new();
    let mut s = W::ZERO;
    let mut m: u64 = 0;
    out.push(0u128);
    let total: u64 = 1u64 << k;
    for j in 1..total {
        let i = j.trailing_zeros() as usize;
        let bit = 1u64 << i;
        if m & bit == 0 {
            s = s.add(a[i]);
        } else {
            s = s.sub(a[i]);
        }
        m ^= bit;
        if s.b == 0 {
            out.push(expand(m, s.a));
        }
    }
    out
}

fn design_check(label: &str, code: &Code) -> bool {
    let n = code.n;
    let Some(e0) = find_full_weight(code) else {
        println!("{label}: no maximal codewords (I = 0), design identity trivial");
        return true;
    };
    let c2 = code.flip_signs(e0.b);
    let words = collect_binary_words(&c2);
    // ε_i = +1 off A, −1 on A;  s(ε) = (−1)^{|A|}
    let mut idx: i128 = 0;
    let mut pair = vec![0i128; n * n];
    for &am in &words {
        let s: i128 = if am.count_ones() % 2 == 0 { 1 } else { -1 };
        idx += s;
        for i in 0..n {
            let ei: i128 = if (am >> i) & 1 == 1 { -1 } else { 1 };
            for j in (i + 1)..n {
                let ej: i128 = if (am >> j) & 1 == 1 { -1 } else { 1 };
                pair[i * n + j] += s * ei * ej;
            }
        }
    }
    let max_off = (0..n).flat_map(|i| ((i + 1)..n).map(move |j| (i, j))).map(|(i, j)| pair[i * n + j].abs()).max().unwrap();
    // triple (0,1,2): Σ_{ε0=ε1=ε2} s = I/4
    let mut trip: i128 = 0;
    for &am in &words {
        let t = am & 0b111;
        if t == 0 || t == 0b111 {
            trip += if am.count_ones() % 2 == 0 { 1 } else { -1 };
        }
    }
    // Step 3 with ε0 = 1, y = ±e_0: x = 1 ± 3 e_0; Σ s (ε·x)^2 = I |x|^2
    let mut ok3 = true;
    for sgn in [1i128, -1] {
        let mut lhs: i128 = 0;
        for &am in &words {
            let s: i128 = if am.count_ones() % 2 == 0 { 1 } else { -1 };
            let dot1: i128 = n as i128 - 2 * am.count_ones() as i128; // ε·1
            let e0: i128 = if am & 1 == 1 { -1 } else { 1 };
            let d = dot1 + 3 * sgn * e0;
            lhs += s * d * d;
        }
        let x2: i128 = (n as i128 - 1) + (1 + 3 * sgn) * (1 + 3 * sgn);
        ok3 &= lhs == idx * x2;
    }
    let ok = max_off == 0 && 4 * trip == idx && idx % 8 == 0 && idx % 3 == 0 && ok3;
    println!(
        "{label}: n={n} maximal={} I={idx}  max_{{i<j}}|Σ s ε_i ε_j|={max_off}  triple*4={}  step3 ok={ok3}  => {}",
        words.len(),
        4 * trip,
        if ok { "DESIGN IDENTITY HOLDS" } else { "FAIL" }
    );
    ok
}


/// All Kneser neighbours of C (one per hyperplane D ⊂ C), with GJF-signed indices.
fn all_neighbors(label: &str, code: &Code, seed: u64) -> bool {
    let n = code.n;
    let k = code.dim();
    let mut rng = Rng(seed);
    let (_, i0) = signed_full(n, &code.rows);
    let mut hist: HashMap<i128, u64> = HashMap::new();
    let mut total: i128 = 0;
    let mut count = 0u64;
    let mut ok = true;
    // hyperplanes D = {Σ m_i g_i : λ·m = 0}, λ ∈ (F_3^k \ 0)/±  (first nonzero coordinate = 1)
    let nl = 3u64.pow(k as u32);
    for code_l in 1..nl {
        let mut lam = vec![0u8; k];
        let mut t = code_l;
        for x in lam.iter_mut() {
            *x = (t % 3) as u8;
            t /= 3;
        }
        if lam[lam.iter().position(|&x| x != 0).unwrap()] != 1 {
            continue;
        }
        let j = lam.iter().position(|&x| x != 0).unwrap();
        let mut drows = Vec::new();
        for i in 0..k {
            if i != j {
                // g_i - λ_i λ_j^{-1} g_j  (λ_j = 1)
                drows.push(code.rows[i].sub(code.rows[j].scale(lam[i])));
            }
        }
        let dperp = dual_basis(n, &drows);
        let c2 = loop {
            let x = random_in_span(&dperp, &mut rng);
            if x.dot(x) != 0 || code.contains(x) {
                continue;
            }
            let mut r = drows.clone();
            r.push(x);
            break Code::new(n, r);
        };
        assert!(c2.is_self_dual());
        let (_, i1) = signed_full(n, &c2.rows);
        let (_, fd) = signed_full(n, &drows);
        ok &= i0 + i1 == 4 * fd && fd % 2 == 0;
        *hist.entry(i1).or_default() += 1;
        total += i1;
        count += 1;
    }
    let mut hs: Vec<_> = hist.into_iter().collect();
    hs.sort();
    let pred = (3i128.pow((k - 1) as u32) - 3) / 2 * i0;
    ok &= total == pred && count == (3u64.pow(k as u32) - 1) / 2;
    println!("{label}: n={n} Index={i0} neighbours={count} index histogram={:?}  sum={total}  predicted ((3^(k-1)-3)/2)*Index={pred}  (★) on all: {}", hs, if ok { "true" } else { "FALSE" });
    ok
}

// ------------------------------------------------------------------------------------------
// Driver
// ------------------------------------------------------------------------------------------

fn tmf_modulus(n: usize) -> i128 {
    if n % 12 != 0 {
        return 1;
    }
    let k = (n / 12) as i128;
    fn gcd(a: i128, b: i128) -> i128 {
        if b == 0 {
            a
        } else {
            gcd(b, a % b)
        }
    }
    24 / gcd(24, k)
}

fn report(label: &str, r: &IndexResult) -> String {
    let md = tmf_modulus(r.n);
    let ok = r.index % md == 0;
    let hist: Vec<String> = r
        .hist
        .iter()
        .enumerate()
        .filter(|(_, &h)| h > 0)
        .map(|(w, h)| format!("{}:{}", w, h))
        .collect();
    format!(
        "{label} n={} full_weight={} I={} |I|mod24={} tmf_mod={} {} B_hist=[{}]",
        r.n,
        r.nfull,
        r.index,
        r.index.rem_euclid(24),
        md,
        if ok { "OK" } else { "VIOLATION" },
        hist.join(" ")
    )
}

fn golay() -> Code {
    pless(5)
}

fn repeat_sum(c: &Code, times: usize) -> Code {
    let mut s = c.clone();
    for _ in 1..times {
        s = s.direct_sum(c);
    }
    s
}

fn threads() -> usize {
    thread::available_parallelism().map(|x| x.get()).unwrap_or(8)
}

fn selftest() {
    let th = threads();
    // bitsliced arithmetic table
    for x in 0..3u8 {
        for y in 0..3u8 {
            let mut a = V::ZERO;
            a.set(0, x);
            let mut b = V::ZERO;
            b.set(0, y);
            assert_eq!(a.add(b).get(0), (x + y) % 3);
            assert_eq!(a.sub(b).get(0), (3 + x - y) % 3);
            assert_eq!(a.dot(b), (x * y) % 3);
        }
    }
    println!("[selftest] F_3 bitsliced arithmetic OK");
    let t = tetracode();
    assert!(t.is_self_dual());
    let g = golay();
    assert!(g.is_self_dual());
    let x12 = xqr(11);
    assert!(x12.is_self_dual());
    let mut rng = Rng(12345);
    // fast vs brute on small codes, incl. random monomial images and random walks
    let mut cases: Vec<(String, Code)> = vec![
        ("tetracode^3".into(), repeat_sum(&t, 3)),
        ("golay=P(5)".into(), g.clone()),
        ("XQR(11)".into(), x12.clone()),
        ("P(11)".into(), pless(11)),
        ("XQR(23)".into(), xqr(23)),
        ("golay+golay".into(), g.direct_sum(&g)),
        ("golay+tetra^3".into(), g.direct_sum(&repeat_sum(&t, 3))),
    ];
    for i in 0..6 {
        let mut c = repeat_sum(&t, 6);
        for _ in 0..40 {
            c = neighbor_step(&c, &mut rng);
        }
        cases.push((format!("rand24#{i}"), random_monomial(&c, &mut rng)));
    }
    for i in 0..4 {
        let mut c = repeat_sum(&t, 3);
        for _ in 0..30 {
            c = neighbor_step(&c, &mut rng);
        }
        cases.push((format!("rand12#{i}"), c));
    }
    for (name, c) in &cases {
        assert!(c.is_self_dual(), "{name} not self-dual");
        let r = index_of(c, th);
        let (nf, ib) = index_brute(c);
        let agree = nf == r.nfull && (ib == r.index || ib == -r.index);
        println!("[selftest] {:<14} fast: full={} I={}   brute: full={} I={}   {}", name, r.nfull, r.index, nf, ib, if agree { "agree" } else { "DISAGREE" });
        assert!(agree);
    }
    // multiplicativity under direct sums
    let r1 = index_of(&g, th).index;
    let r2 = index_of(&g.direct_sum(&g), th).index;
    assert_eq!(r2.abs(), r1 * r1);
    println!("[selftest] ALL SELFTESTS PASSED");
}


/// All codewords of weight 1..=wmax (both signs) of a self-dual code, via two complementary
/// information sets: a word of weight w has weight <= w/2 on one of them.
fn low_weight_words(code: &Code, wmax: u32) -> Vec<V> {
    let n = code.n;
    let (_, piv) = rref(n, &code.rows);
    let rest: Vec<usize> = (0..n).filter(|c| !piv.contains(c)).collect();
    let mut out: std::collections::HashSet<(u128, u128)> = std::collections::HashSet::new();
    for order in [piv.iter().chain(rest.iter()).cloned().collect::<Vec<usize>>(),
                  rest.iter().chain(piv.iter()).cloned().collect::<Vec<usize>>()] {
        // perm: old coordinate order[j] -> new coordinate j
        let mut perm = vec![0usize; n];
        for (j, &c) in order.iter().enumerate() {
            perm[c] = j;
        }
        let pc = code.permute(&perm);
        let (rows, p2) = rref(n, &pc.rows);
        assert_eq!(p2.len() * 2, n, "not an information set");
        let mut inv = vec![0usize; n];
        for (i, &q) in perm.iter().enumerate() {
            inv[q] = i;
        }
        let t = (wmax / 2) as usize;
        // depth-first over subsets of rows with signs
        fn rec(rows: &[V], start: usize, left: usize, cur: V, wmax: u32, inv: &[usize],
               out: &mut std::collections::HashSet<(u128, u128)>) {
            for i in start..rows.len() {
                for sgn in [false, true] {
                    let r = if sgn { rows[i].neg() } else { rows[i] };
                    let x = cur.add(r);
                    if x.wt() <= wmax {
                        let y = x.permute(inv);
                        out.insert((y.a, y.b));
                    }
                    if left > 1 {
                        rec(rows, i + 1, left - 1, x, wmax, inv, out);
                    }
                }
            }
        }
        rec(&rows, 0, t, V::ZERO, wmax, &inv, &mut out);
    }
    let mut v: Vec<V> = out.into_iter().map(|(a, b)| V { a, b }).collect();
    v.sort_by_key(|x| (x.wt(), x.a, x.b));
    v
}

/// R_σ(E) = Σ_{c∈E} Π_{singletons} φ(c_i) Π_{blocks} λ(|supp c ∩ β|), φ = (0,−1,1), λ = (0,−2,0,0,1),
/// by full enumeration of E (meet in the middle over the generator rows; E need not be self-dual).
fn rsigma(code: &Code, blocks: &[Vec<usize>], threads: usize) -> i128 {
    let n = code.n;
    let rows = &code.rows;
    let k = rows.len();
    let k1 = k / 2;
    let span_of = |rs: &[V]| -> Vec<V> {
        let mut out = vec![V::ZERO];
        for r in rs {
            let mut nx = Vec::with_capacity(out.len() * 3);
            for &x in &out {
                nx.push(x);
                nx.push(x.add(*r));
                nx.push(x.add(r.neg()));
            }
            out = nx;
        }
        out
    };
    let a = span_of(&rows[..k1]);
    let b = span_of(&rows[k1..]);
    let mut bmask: Vec<u128> = Vec::new();
    let mut inb: u128 = 0;
    for bl in blocks {
        let mut m = 0u128;
        for &i in bl {
            m |= 1u128 << i;
        }
        inb |= m;
        bmask.push(m);
    }
    let smask = mask(n) & !inb;
    let chunk = (a.len() + threads - 1) / threads;
    let total: i128 = std::thread::scope(|sc| {
        let mut hs = Vec::new();
        for t in 0..threads {
            let a = &a;
            let b = &b;
            let bmask = &bmask;
            hs.push(sc.spawn(move || {
                let mut acc: i128 = 0;
                let lo = t * chunk;
                let hi = ((t + 1) * chunk).min(a.len());
                for i in lo..hi {
                    let x0 = a[i];
                    for &y in b.iter() {
                        let x = x0.add(y);
                        let sup = x.a | x.b;
                        if sup & smask != smask {
                            continue;
                        }
                        let mut w: i128 = if (x.a & smask).count_ones() % 2 == 1 { -1 } else { 1 };
                        for &m in bmask.iter() {
                            match (sup & m).count_ones() {
                                1 => w *= -2,
                                4 => {}
                                _ => {
                                    w = 0;
                                    break;
                                }
                            }
                        }
                        acc += w;
                    }
                }
                acc
            }));
        }
        hs.into_iter().map(|h| h.join().unwrap()).sum()
    });
    total
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let th = threads();
    let cmd = args.get(1).map(|s| s.as_str()).unwrap_or("help");
    match cmd {
        "selftest" => selftest(),
        "rsigma" => {
            // rsigma <file> <blocks as a,b,c,d;e,f,g,h;...>  (blocks may be empty: "-")
            let txt = fs::read_to_string(&args[2]).expect("read");
            let c = Code::from_text(&txt);
            let blocks: Vec<Vec<usize>> = if args[3] == "-" { vec![] } else {
                args[3].split(';').map(|b| b.split(',').map(|x| x.parse().unwrap()).collect()).collect() };
            println!("R={}", rsigma(&c, &blocks, th));
        }
        "words" => {
            // words <file> <wmax>: all codewords of weight <= wmax, one per line
            let txt = fs::read_to_string(&args[2]).expect("read");
            let c = Code::from_text(&txt);
            assert!(c.is_self_dual());
            let wmax: u32 = args[3].parse().unwrap();
            let ws = low_weight_words(&c, wmax);
            let mut s = String::new();
            for w in &ws {
                s.push_str(&w.to_string(c.n));
                s.push('\n');
            }
            print!("{}", s);
        }
        "index" => {
            // index <file>
            let txt = fs::read_to_string(&args[2]).expect("read");
            let c = Code::from_text(&txt);
            let r = index_of(&c, th);
            println!("{}", report(&args[2], &r));
        }
        "pless" => {
            let q: i64 = args[2].parse().unwrap();
            let c = pless(q);
            assert!(c.is_self_dual());
            let r = index_of(&c, th);
            println!("{}", report(&format!("P({q})"), &r));
            if let Some(out) = args.get(3) {
                fs::write(out, c.to_text()).unwrap();
            }
        }
        "xqr" => {
            let p: i64 = args[2].parse().unwrap();
            let c = xqr(p);
            let r = index_of(&c, th);
            println!("{}", report(&format!("XQR({p})"), &r));
            if let Some(out) = args.get(3) {
                fs::write(out, c.to_text()).unwrap();
            }
        }
        "random" => {
            // random <n> <count> <seed> [steps]
            let n: usize = args[2].parse().unwrap();
            let count: usize = args[3].parse().unwrap();
            let seed: u64 = args[4].parse().unwrap();
            let steps: usize = args.get(5).map(|s| s.parse().unwrap()).unwrap_or(3 * n / 2);
            assert_eq!(n % 4, 0);
            let mut bad = 0;
            let mut residues: HashMap<i128, usize> = HashMap::new();
            for i in 0..count {
                let mut rng = Rng(seed.wrapping_mul(1_000_003).wrapping_add(i as u64));
                let mut c = repeat_sum(&tetracode(), n / 4);
                for _ in 0..steps {
                    c = neighbor_step(&c, &mut rng);
                }
                let r = index_of(&c, th);
                let md = tmf_modulus(n);
                if r.index % md != 0 {
                    bad += 1;
                    let fname = format!("violation_n{}_seed{}_{}.txt", n, seed, i);
                    fs::write(&fname, c.to_text()).unwrap();
                }
                *residues.entry(r.index.rem_euclid(24)).or_default() += 1;
                println!("{}", report(&format!("random(seed={seed},i={i},steps={steps})"), &r));
            }
            let mut rs: Vec<_> = residues.into_iter().collect();
            rs.sort();
            println!("SUMMARY random n={n} count={count} violations={bad} residues_mod24={:?}", rs);
        }
        "walk" => {
            // walk <start: golay5|golay2|...> <count> <seed> <steps>: few neighbour steps from a decomposable code
            let start = args[2].as_str();
            let count: usize = args[3].parse().unwrap();
            let seed: u64 = args[4].parse().unwrap();
            let steps: usize = args[5].parse().unwrap();
            let g = golay();
            let t = tetracode();
            let base = match start {
                "golay5" => repeat_sum(&g, 5),
                "golay4" => repeat_sum(&g, 4),
                "golay3" => repeat_sum(&g, 3),
                "golay2" => repeat_sum(&g, 2),
                "p11golay3" => pless(11).direct_sum(&repeat_sum(&g, 3)),
                "p17p11" => pless(17).direct_sum(&pless(11)),
                "p23golay" => pless(23).direct_sum(&g),
                "x47golay" => xqr(47).direct_sum(&g),
                "golay4tetra3" => repeat_sum(&g, 4).direct_sum(&repeat_sum(&t, 3)),
                other => panic!("unknown start {other}"),
            };
            let n = base.n;
            let mut bad = 0;
            let mut residues: HashMap<i128, usize> = HashMap::new();
            for i in 0..count {
                let mut rng = Rng(seed.wrapping_mul(7_000_001).wrapping_add(i as u64));
                let mut c = base.clone();
                for _ in 0..steps {
                    c = neighbor_step(&c, &mut rng);
                }
                let r = index_of(&c, th);
                if r.index % tmf_modulus(n) != 0 {
                    bad += 1;
                    fs::write(format!("violation_walk_{start}_{seed}_{i}.txt"), c.to_text()).unwrap();
                }
                *residues.entry(r.index.rem_euclid(24)).or_default() += 1;
                println!("{}", report(&format!("walk({start},seed={seed},i={i},steps={steps})"), &r));
            }
            let mut rs: Vec<_> = residues.into_iter().collect();
            rs.sort();
            println!("SUMMARY walk start={start} n={n} steps={steps} count={count} violations={bad} residues_mod24={:?}", rs);
        }
        "batch" => {
            // batch <n> <per_thread> <seed> <thin> [subcode]
            let n: usize = args[2].parse().unwrap();
            let per: usize = args[3].parse().unwrap();
            let seed: u64 = args[4].parse().unwrap();
            let thin: usize = args[5].parse().unwrap();
            let kind = args.get(6).map(|s| s.as_str()).unwrap_or("none");
            batch(n, per, seed, thin, kind);
        }
        "nbr" => {
            // nbr <n> <pairs> <seed>: check I(C) + I(C') = 4 F(D) along a neighbour walk
            let n: usize = args[2].parse().unwrap();
            let pairs: usize = args[3].parse().unwrap();
            let seed: u64 = args[4].parse().unwrap();
            neighbor_identity(n, pairs, seed);
        }
        "export-random" => {
            // export-random <n> <seed> <i> <steps> <out>: regenerate code i of `random n _ seed steps`
            let n: usize = args[2].parse().unwrap();
            let seed: u64 = args[3].parse().unwrap();
            let i: u64 = args[4].parse().unwrap();
            let steps: usize = args[5].parse().unwrap();
            let mut rng = Rng(seed.wrapping_mul(1_000_003).wrapping_add(i));
            let mut c = repeat_sum(&tetracode(), n / 4);
            for _ in 0..steps {
                c = neighbor_step(&c, &mut rng);
            }
            let r = index_of(&c, th);
            println!("{}", report(&format!("export(seed={seed},i={i},steps={steps})"), &r));
            fs::write(&args[6], c.to_text()).unwrap();
        }
        "design" => {
            // design <n> <count> <seed>: signed 2-design identity on random codes (+ P(q), XQR(p) of that length)
            let n: usize = args[2].parse().unwrap();
            let count: usize = args[3].parse().unwrap();
            let seed: u64 = args[4].parse().unwrap();
            let mut all = true;
            let q = (n / 2 - 1) as i64;
            if q % 3 == 2 {
                all &= design_check(&format!("P({q})"), &pless(q));
            }
            let p = (n - 1) as i64;
            if (2..p).all(|d| p % d != 0) && p % 12 == 11 {
                all &= design_check(&format!("XQR({p})"), &xqr(p));
            }
            for i in 0..count {
                let mut rng = Rng(seed.wrapping_mul(1_000_003).wrapping_add(i as u64));
                let mut c = repeat_sum(&tetracode(), n / 4);
                for _ in 0..(3 * n / 2) {
                    c = neighbor_step(&c, &mut rng);
                }
                all &= design_check(&format!("random(seed={seed},i={i})"), &c);
            }
            println!("SUMMARY design n={n}: all hold = {all}");
            if !all {
                std::process::exit(1);
            }
        }
        "allnbrs" => {
            // allnbrs: every neighbour of Golay, of GJF's second length-12 code, and of one random length-24 code
            let mut ok = all_neighbors("Golay", &golay(), 1);
            let mut rng = Rng(77);
            let mut c = repeat_sum(&tetracode(), 6);
            for _ in 0..40 {
                c = neighbor_step(&c, &mut rng);
            }
            ok &= all_neighbors("random24", &c, 2);
            if !ok {
                std::process::exit(1);
            }
        }
        "dc" => {
            // dc <m> <count> <seed>: pure double circulant codes of length 2m
            let m: usize = args[2].parse().unwrap();
            let count: usize = args[3].parse().unwrap();
            let seed: u64 = args[4].parse().unwrap();
            let mut rng = Rng(seed);
            let mut bad = 0;
            let mut residues: HashMap<i128, usize> = HashMap::new();
            for i in 0..count {
                let c = random_double_circulant(m, &mut rng);
                let r = index_of(&c, th);
                if r.index % 24 != 0 {
                    bad += 1;
                    fs::write(format!("violation_dc_{m}_{seed}_{i}.txt"), c.to_text()).unwrap();
                }
                *residues.entry(r.index.rem_euclid(48)).or_default() += 1;
                println!("{}", report(&format!("dc(m={m},seed={seed},i={i})"), &r));
            }
            let mut rs: Vec<_> = residues.into_iter().collect();
            rs.sort();
            println!("SUMMARY dc n={} count={count} violations(24∤I)={bad} residues_mod48={:?}", 2 * m, rs);
        }
        _ => {
            eprintln!("usage: ternary60 selftest | index <file> | pless <q> [out] | xqr <p> [out] | random <n> <count> <seed> [steps] | walk <start> <count> <seed> <steps>");
        }
    }
}
