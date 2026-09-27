//! rsigma_is: R_σ(E) by information-set enumeration, written from the definition and sharing no code with
//! src/main.rs (in particular not with `sl2words`, whose Morita/SL₂-word method it is meant to check).
//!
//! Definition ([I] Lemma 5.8; notes/ternary-code-index.md §5.1): for a linear code E ⊂ F₃ⁿ and a set σ of
//! disjoint 4-blocks,
//!     R_σ(E) = Σ_{x ∈ E} Π_{i ∉ ∪σ} φ(x_i) · Π_{β ∈ σ} λ(#{i ∈ β : x_i ≠ 0}),
//! with φ = (0, −1, +1) on (0, 1, 2) and λ = (0, −2, 0, 0, 1) on block weights 0..4. With σ = ∅ this is the
//! index Σ_x f(x) (GJF's #even − #odd), sign-exact.
//!
//! Method. φ(0) = 0, so only words that are nonzero on every coordinate outside the blocks contribute.
//! Gaussian elimination picks an information set I, preferring coordinates outside the blocks. A word is
//! determined by its values on I; on I ∩ outside only the values 1, 2 can contribute (2^a patterns), on
//! I ∩ blocks all of 0, 1, 2 (3^b patterns). The 2^a patterns are walked in Gray-code order, so each step
//! adds ± one systematic row to the dependent coordinates (bit-sliced F₃ arithmetic on two u64 planes).
//! The elimination is verified: every input row must equal Σ_{i∈I} row[i]·S_i.
//!
//! Usage:  rsigma_is <code-file> <blocks> [threads]
//!         blocks = "-" (none) or "i,j,k,l;i,j,k,l;..." (0-based coordinates)
//!         rsigma_is selftest
//! Output: lines "file", "fnv1a64" (hash of the code file), "blocks", "n", "k", "info_outside",
//! "info_in_blocks", "patterns", "seconds", then "R <value>".
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Clone, Copy)]
struct P {
    one: u64, // coordinates with value 1
    two: u64, // coordinates with value 2
}

#[inline(always)]
fn add(a: P, b: P) -> P {
    let za = !(a.one | a.two);
    let zb = !(b.one | b.two);
    P {
        one: (a.one & zb) | (za & b.one) | (a.two & b.two),
        two: (a.two & zb) | (za & b.two) | (a.one & b.one),
    }
}

#[inline(always)]
fn neg(a: P) -> P {
    P { one: a.two, two: a.one }
}

const LAMBDA: [i64; 5] = [0, -2, 0, 0, 1];

fn read_code(path: &str) -> Vec<Vec<u8>> {
    let s = std::fs::read_to_string(path).expect("cannot read code file");
    let mut rows = Vec::new();
    for line in s.lines() {
        assert!(
            line.chars().all(|c| c == '0' || c == '1' || c == '2' || c.is_whitespace()),
            "code file: only the digits 0, 1, 2 and whitespace are allowed"
        );
        let r: Vec<u8> = line.chars().filter(|c| !c.is_whitespace()).map(|c| c as u8 - b'0').collect();
        if r.is_empty() {
            continue;
        }
        rows.push(r);
    }
    let n = rows[0].len();
    assert!(rows.iter().all(|r| r.len() == n), "rows of different length");
    rows
}

fn parse_blocks(s: &str, n: usize) -> Vec<Vec<usize>> {
    if s == "-" {
        return Vec::new();
    }
    let blocks: Vec<Vec<usize>> = s
        .split(';')
        .map(|b| b.split(',').map(|x| x.trim().parse::<usize>().expect("bad coordinate")).collect())
        .collect();
    let mut seen = vec![false; n];
    for b in &blocks {
        assert_eq!(b.len(), 4, "blocks must have 4 coordinates");
        for &i in b {
            assert!(i < n && !seen[i], "blocks must be disjoint and inside 0..n");
            seen[i] = true;
        }
    }
    blocks
}

fn inv3(a: u8) -> u8 {
    // 1⁻¹ = 1, 2⁻¹ = 2 in F₃
    assert!(a != 0);
    a
}

/// Row-reduce over F₃, pivoting on columns in the given order. Returns (pivot columns, systematic rows).
/// The row operations are applied to [input | identity], and the result is checked in both directions:
/// every systematic row is T·input (so span(sys) ⊆ span(input)), and every input row is
/// Σ_{t} row[piv_t]·sys_t (so span(input) ⊆ span(sys)).
fn eliminate(rows: &[Vec<u8>], order: &[usize]) -> (Vec<usize>, Vec<Vec<u8>>) {
    let n = rows[0].len();
    let m0 = rows.len();
    let mut m: Vec<Vec<u8>> = rows
        .iter()
        .enumerate()
        .map(|(i, r)| {
            let mut v = r.clone();
            v.extend((0..m0).map(|j| (i == j) as u8));
            v
        })
        .collect();
    let width = n + m0;
    let mut piv = Vec::new();
    let mut r = 0;
    for &c in order {
        if r == m.len() {
            break;
        }
        let Some(p) = (r..m.len()).find(|&i| m[i][c] != 0) else { continue };
        m.swap(r, p);
        let s = inv3(m[r][c]);
        for j in 0..width {
            m[r][j] = (m[r][j] * s) % 3;
        }
        for i in 0..m.len() {
            if i != r && m[i][c] != 0 {
                let f = m[i][c];
                for j in 0..width {
                    m[i][j] = (m[i][j] + 3 * 3 - f * m[r][j]) % 3;
                }
            }
        }
        piv.push(c);
        r += 1;
    }
    m.truncate(r);
    // span(sys) ⊆ span(input): sys_t = Σ_i T[t][i]·input_i
    for row in &m {
        for j in 0..n {
            let v: u32 = (0..m0).map(|i| row[n + i] as u32 * rows[i][j] as u32).sum::<u32>() % 3;
            assert_eq!(v as u8, row[j], "elimination check (transform) failed");
        }
    }
    let sys: Vec<Vec<u8>> = m.into_iter().map(|mut v| {
        v.truncate(n);
        v
    }).collect();
    (piv, sys)
}

struct Setup {
    n: usize,
    k: usize,
    info_out: Vec<usize>,   // indices into sys rows (pivots outside the blocks)
    info_blk: Vec<usize>,   // indices into sys rows (pivots inside blocks)
    blk_of_piv: Vec<usize>, // for each info_blk entry: its block index
    rows: Vec<P>,           // dependent part of each systematic row
    omask: u64,             // dependent coordinates outside the blocks
    bmask: Vec<u64>,        // dependent coordinates of each block
}

fn setup(code: &[Vec<u8>], blocks: &[Vec<usize>]) -> Setup {
    let n = code[0].len();
    let mut in_block = vec![usize::MAX; n];
    for (bi, b) in blocks.iter().enumerate() {
        for &i in b {
            in_block[i] = bi;
        }
    }
    let order: Vec<usize> =
        (0..n).filter(|&i| in_block[i] == usize::MAX).chain((0..n).filter(|&i| in_block[i] != usize::MAX)).collect();
    let (piv, sys) = eliminate(code, &order);
    let k = piv.len();
    // span(input) ⊆ span(sys): every input row is Σ_{i ∈ I} row[piv_i]·S_i
    for r in code {
        let mut acc = vec![0u8; n];
        for (t, &c) in piv.iter().enumerate() {
            for j in 0..n {
                acc[j] = (acc[j] + r[c] * sys[t][j]) % 3;
            }
        }
        assert_eq!(&acc, r, "elimination check failed");
    }
    for (t, &c) in piv.iter().enumerate() {
        for (u, &c2) in piv.iter().enumerate() {
            assert_eq!(sys[t][c2], (t == u) as u8, "not systematic");
        }
        let _ = c;
    }
    let is_piv: Vec<bool> = (0..n).map(|i| piv.contains(&i)).collect();
    let dep: Vec<usize> = (0..n).filter(|&i| !is_piv[i]).collect();
    assert!(dep.len() <= 64, "at most 64 dependent coordinates supported");
    let mut omask = 0u64;
    let mut bmask = vec![0u64; blocks.len()];
    for (d, &i) in dep.iter().enumerate() {
        if in_block[i] == usize::MAX {
            omask |= 1 << d;
        } else {
            bmask[in_block[i]] |= 1 << d;
        }
    }
    let rows: Vec<P> = sys
        .iter()
        .map(|s| {
            let mut p = P { one: 0, two: 0 };
            for (d, &i) in dep.iter().enumerate() {
                match s[i] {
                    1 => p.one |= 1 << d,
                    2 => p.two |= 1 << d,
                    _ => {}
                }
            }
            p
        })
        .collect();
    let mut info_out = Vec::new();
    let mut info_blk = Vec::new();
    let mut blk_of_piv = Vec::new();
    for (t, &c) in piv.iter().enumerate() {
        if in_block[c] == usize::MAX {
            info_out.push(t);
        } else {
            info_blk.push(t);
            blk_of_piv.push(in_block[c]);
        }
    }
    Setup { n, k, info_out, info_blk, blk_of_piv, rows, omask, bmask }
}

/// Sum over one work item: fixed values on the block-information coordinates (outer, 3^b) and on the top
/// `q` outside-information coordinates; Gray walk over the remaining outside-information coordinates.
fn work(s: &Setup, blk_vals: &[u8], top_vals: u64, q: usize) -> i64 {
    let a = s.info_out.len();
    let low = a - q;
    // base word: block-info values, top outside-info values, low outside-info all = 1
    let mut x = P { one: 0, two: 0 };
    let mut cw = vec![0usize; s.bmask.len()];
    for (t, &v) in blk_vals.iter().enumerate() {
        let r = s.rows[s.info_blk[t]];
        match v {
            1 => x = add(x, r),
            2 => x = add(x, neg(r)),
            _ => {}
        }
        if v != 0 {
            cw[s.blk_of_piv[t]] += 1;
        }
    }
    let mut ones_info = 0usize; // number of outside-information coordinates equal to 1
    for j in 0..a {
        let r = s.rows[s.info_out[j]];
        let two = j >= low && (top_vals >> (j - low)) & 1 == 1;
        if two {
            x = add(x, neg(r));
        } else {
            x = add(x, r);
            ones_info += 1;
        }
    }
    let plus: Vec<P> = (0..low).map(|j| s.rows[s.info_out[j]]).collect();
    let minus: Vec<P> = plus.iter().map(|&r| neg(r)).collect();
    let omask = s.omask;
    let eval = |x: P, ones_info: usize| -> i64 {
        if (x.one | x.two) & omask != omask {
            return 0;
        }
        let mut w: i64 = if ((ones_info + (x.one & omask).count_ones() as usize) & 1) == 1 { -1 } else { 1 };
        let nz = x.one | x.two;
        for (b, &m) in s.bmask.iter().enumerate() {
            let wt = (nz & m).count_ones() as usize + cw[b];
            w *= LAMBDA[wt];
            if w == 0 {
                return 0;
            }
        }
        w
    };
    let mut acc: i64 = eval(x, ones_info);
    let mut state: u64 = 0; // bit j set ⇔ low coordinate j currently has value 2
    assert!(low < 64, "Gray walk too long");
    let total: u64 = 1u64 << low;
    for t in 1..total {
        let j = t.trailing_zeros() as usize;
        if (state >> j) & 1 == 0 {
            x = add(x, plus[j]); // 1 → 2: add S_j
            ones_info -= 1;
        } else {
            x = add(x, minus[j]); // 2 → 1: subtract S_j
            ones_info += 1;
        }
        state ^= 1 << j;
        acc += eval(x, ones_info);
    }
    acc
}

fn rsigma(code: &[Vec<u8>], blocks: &[Vec<usize>], threads: usize, qmax: usize) -> (Setup, i64) {
    let s = setup(code, blocks);
    let a = s.info_out.len();
    let b = s.info_blk.len();
    let q = a.min(qmax);
    assert!(threads >= 1, "threads must be at least 1");
    let nblk = 3usize.checked_pow(b as u32).expect("too many information coordinates in blocks");
    let items = nblk.checked_mul(1usize << q).expect("too many work items");
    let next = AtomicUsize::new(0);
    let total: i64 = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads)
            .map(|_| {
                let s = &s;
                let next = &next;
                sc.spawn(move || {
                    let mut acc: i64 = 0;
                    loop {
                        let it = next.fetch_add(1, Ordering::Relaxed);
                        if it >= items {
                            break;
                        }
                        let mut bi = it / (1usize << q);
                        let top = (it % (1usize << q)) as u64;
                        let mut vals = vec![0u8; b];
                        for v in vals.iter_mut() {
                            *v = (bi % 3) as u8;
                            bi /= 3;
                        }
                        acc += work(s, &vals, top, q);
                    }
                    acc
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).sum()
    });
    (s, total)
}

/// R_σ by brute force over all combinations of the input rows (repeated words counted once).
fn brute(rows: &[Vec<u8>], blocks: &[Vec<usize>]) -> i64 {
    let n = rows[0].len();
    let mut in_block = vec![usize::MAX; n];
    for (bi, b) in blocks.iter().enumerate() {
        for &i in b {
            in_block[i] = bi;
        }
    }
    let mut words = std::collections::HashSet::new();
    let tot = 3usize.pow(rows.len() as u32);
    let mut acc: i64 = 0;
    for c in 0..tot {
        let mut x = vec![0u8; n];
        let mut cc = c;
        for r in rows {
            let f = (cc % 3) as u8;
            cc /= 3;
            for j in 0..n {
                x[j] = (x[j] + f * r[j]) % 3;
            }
        }
        if !words.insert(x.clone()) {
            continue;
        }
        let mut w: i64 = 1;
        let mut bw = vec![0usize; blocks.len()];
        for j in 0..n {
            if in_block[j] == usize::MAX {
                w *= [0, -1, 1][x[j] as usize];
            } else if x[j] != 0 {
                bw[in_block[j]] += 1;
            }
        }
        for &c2 in &bw {
            w *= LAMBDA[c2];
        }
        acc += w;
    }
    acc
}

struct Rng(u64);
impl Rng {
    fn next(&mut self, m: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % m
    }
    fn perm(&mut self, n: usize) -> Vec<usize> {
        let mut p: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            let j = self.next((i + 1) as u64) as usize;
            p.swap(i, j);
        }
        p
    }
}

/// A random self-dual code of length n (n ≡ 0 mod 4): extend an isotropic subspace greedily by random
/// self-orthogonal vectors of its orthogonal complement.
fn random_selfdual(n: usize, rng: &mut Rng) -> Vec<Vec<u8>> {
    let dot = |a: &[u8], b: &[u8]| a.iter().zip(b).map(|(x, y)| (x * y) as u32).sum::<u32>() % 3;
    let mut s: Vec<Vec<u8>> = Vec::new();
    while s.len() < n / 2 {
        // basis of S^⊥ from the reduced form of S
        let (piv, red) = if s.is_empty() { (Vec::new(), Vec::new()) } else { eliminate(&s, &(0..n).collect::<Vec<_>>()) };
        let free: Vec<usize> = (0..n).filter(|c| !piv.contains(c)).collect();
        let perp: Vec<Vec<u8>> = free
            .iter()
            .map(|&f| {
                let mut v = vec![0u8; n];
                v[f] = 1;
                for (t, &c) in piv.iter().enumerate() {
                    v[c] = (3 - red[t][f]) % 3;
                }
                v
            })
            .collect();
        loop {
            let mut v = vec![0u8; n];
            for b in &perp {
                let f = rng.next(3) as u8;
                for j in 0..n {
                    v[j] = (v[j] + f * b[j]) % 3;
                }
            }
            if v.iter().all(|&x| x == 0) || dot(&v, &v) != 0 {
                continue;
            }
            let mut t = s.clone();
            t.push(v.clone());
            if eliminate(&t, &(0..n).collect::<Vec<_>>()).0.len() == s.len() + 1 {
                s.push(v);
                break;
            }
        }
    }
    for a in &s {
        for b in &s {
            assert_eq!(dot(a, b), 0);
        }
    }
    s
}

fn selftest() {
    // bit-sliced F₃ addition and negation, all 9 value pairs in every bit position
    for pos in 0..64 {
        for a in 0..3u8 {
            for b in 0..3u8 {
                let enc = |v: u8| P { one: ((v == 1) as u64) << pos, two: ((v == 2) as u64) << pos };
                let r = add(enc(a), enc(b));
                let want = enc((a + b) % 3);
                assert!(r.one == want.one && r.two == want.two, "add {} {}", a, b);
                let m = neg(enc(a));
                let wm = enc((3 - a) % 3);
                assert!(m.one == wm.one && m.two == wm.two, "neg {}", a);
            }
        }
    }
    let mut rng = Rng(0x9E3779B97F4A7C15);
    let (mut cases, mut nonzero, mut with_blk_info, mut deficient, mut walk_default) = (0, 0, 0, 0, 0);
    let mut check = |rows: &Vec<Vec<u8>>, blocks: &Vec<Vec<usize>>, tag: &str| {
        let want = brute(rows, blocks);
        let st = setup(rows, blocks);
        cases += 1;
        nonzero += (want != 0) as usize;
        with_blk_info += (!st.info_blk.is_empty()) as usize;
        deficient += (st.k < rows.len()) as usize;
        walk_default += (st.info_out.len() > 10) as usize;
        // outer split depth qmax: 0 = one long Gray walk, 10 = the production setting
        for qmax in [0usize, 1, 3, 10] {
            for threads in [1usize, 3] {
                let (_, got) = rsigma(rows, blocks, threads, qmax);
                assert_eq!(want, got, "{} rows {:?} blocks {:?} q {} threads {}", tag, rows, blocks, qmax, threads);
            }
        }
    };
    // (a) random linear codes, n = 8..17, often with an even number of outside coordinates (for odd counts
    //     x ↦ −x forces R = 0), a third of them rank-deficient (zero, repeated and dependent rows)
    for _ in 0..200 {
        let mut n = 8 + rng.next(10) as usize;
        if rng.next(3) != 0 && n % 2 == 1 {
            n += 1;
        }
        let k = (2 + rng.next((n - 2) as u64) as usize).min(9);
        let mut rows: Vec<Vec<u8>> = (0..k).map(|_| (0..n).map(|_| rng.next(3) as u8).collect()).collect();
        if rng.next(3) == 0 {
            rows.push(vec![0u8; n]);
            rows.push(rows[0].clone());
            let d: Vec<u8> = (0..n).map(|j| (rows[0][j] + 2 * rows[1][j]) % 3).collect();
            rows.push(d);
        }
        let nb = rng.next((n / 4 + 1) as u64) as usize;
        let p = rng.perm(n);
        let blocks: Vec<Vec<usize>> = (0..nb).map(|t| p[4 * t..4 * t + 4].to_vec()).collect();
        check(&rows, &blocks, "random");
    }
    // (b) random self-dual codes of length 12 and 24 (length 24 without blocks runs the production split
    //     with a Gray walk below it)
    for (n, count) in [(12usize, 40usize), (24, 12)] {
        for _ in 0..count {
            let rows = random_selfdual(n, &mut rng);
            let nb = rng.next(4) as usize;
            let p = rng.perm(n);
            let blocks: Vec<Vec<usize>> = (0..nb).map(|t| p[4 * t..4 * t + 4].to_vec()).collect();
            check(&rows, &blocks, "self-dual");
        }
    }
    println!(
        "selftest ok: F3 arithmetic; {} codes against brute force (200 random, 52 random self-dual of length 12 \
         and 24), each at outer split depth 0, 1, 3, 10 and with 1 and 3 threads: {} with R != 0, {} with \
         information coordinates in blocks, {} rank-deficient, {} with a Gray walk under the production split",
        cases, nonzero, with_blk_info, deficient, walk_default
    );
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() >= 2 && args[1] == "selftest" {
        selftest();
        return;
    }
    assert!(args.len() >= 3, "usage: rsigma_is <code-file> <blocks> [threads] | rsigma_is selftest");
    let code = read_code(&args[1]);
    let bytes = std::fs::read(&args[1]).unwrap();
    let mut h: u64 = 0xcbf29ce484222325; // FNV-1a of the code file
    for &c in &bytes {
        h ^= c as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    let blocks = parse_blocks(&args[2], code[0].len());
    let threads: usize = args.get(3).map(|t| t.parse().unwrap()).unwrap_or(4);
    let t0 = std::time::Instant::now();
    let (s, r) = rsigma(&code, &blocks, threads, 10);
    println!("file {}", args[1]);
    println!("fnv1a64 {:016x}", h);
    println!("blocks {}", args[2]);
    println!("n {}", s.n);
    println!("k {}", s.k);
    println!("info_outside {}", s.info_out.len());
    println!("info_in_blocks {}", s.info_blk.len());
    println!("patterns 2^{}*3^{}", s.info_out.len(), s.info_blk.len());
    println!("seconds {:.1}", t0.elapsed().as_secs_f64());
    println!("R {}", r);
}
