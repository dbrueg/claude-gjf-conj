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
//! Output: lines "n", "k", "info_outside", "info_in_blocks", "patterns", then "R <value>".
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
        let r: Vec<u8> = line.chars().filter(|c| c.is_ascii_digit()).map(|c| c as u8 - b'0').collect();
        if r.is_empty() {
            continue;
        }
        assert!(r.iter().all(|&v| v < 3), "entries must be 0, 1, 2");
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
fn eliminate(rows: &[Vec<u8>], order: &[usize]) -> (Vec<usize>, Vec<Vec<u8>>) {
    let mut m: Vec<Vec<u8>> = rows.to_vec();
    let n = m[0].len();
    let mut piv = Vec::new();
    let mut r = 0;
    for &c in order {
        if r == m.len() {
            break;
        }
        let Some(p) = (r..m.len()).find(|&i| m[i][c] != 0) else { continue };
        m.swap(r, p);
        let s = inv3(m[r][c]);
        for j in 0..n {
            m[r][j] = (m[r][j] * s) % 3;
        }
        for i in 0..m.len() {
            if i != r && m[i][c] != 0 {
                let f = m[i][c];
                for j in 0..n {
                    m[i][j] = (m[i][j] + 3 * 3 - f * m[r][j]) % 3;
                }
            }
        }
        piv.push(c);
        r += 1;
    }
    m.truncate(r);
    (piv, m)
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
    // verification: every input row is Σ_{i ∈ I} row[piv_i]·S_i
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
    let nblk = 3usize.pow(b as u32);
    let items = nblk * (1usize << q);
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
    // brute force against the enumeration on small pseudo-random codes
    let mut seed: u64 = 0x9E3779B97F4A7C15;
    let mut rnd = |m: u64| -> u64 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed % m
    };
    let mut nonzero = 0;
    let mut with_blk_info = 0;
    for trial in 0..200 {
        let n = 8 + rnd(9) as usize; // 8..16
        let k = 2 + rnd((n - 2) as u64) as usize;
        let k = k.min(9);
        let rows: Vec<Vec<u8>> = (0..k).map(|_| (0..n).map(|_| rnd(3) as u8).collect()).collect();
        let nb = rnd((n / 4 + 1) as u64) as usize;
        let mut perm: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            let j = rnd((i + 1) as u64) as usize;
            perm.swap(i, j);
        }
        let blocks: Vec<Vec<usize>> = (0..nb).map(|t| perm[4 * t..4 * t + 4].to_vec()).collect();
        // brute force over all 3^k combinations of the input rows (duplicates if rank < k are divided out)
        let mut in_block = vec![usize::MAX; n];
        for (bi, b) in blocks.iter().enumerate() {
            for &i in b {
                in_block[i] = bi;
            }
        }
        let mut words = std::collections::HashSet::new();
        let tot = 3usize.pow(k as u32);
        let mut brute: i64 = 0;
        for c in 0..tot {
            let mut x = vec![0u8; n];
            let mut cc = c;
            for r in &rows {
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
            let mut bw = vec![0usize; nb];
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
            brute += w;
        }
        if brute != 0 {
            nonzero += 1;
        }
        if !setup(&rows, &blocks).info_blk.is_empty() {
            with_blk_info += 1;
        }
        for qmax in [0usize, 1, 3, 10] {
            let (_, fast) = rsigma(&rows, &blocks, 2, qmax);
            assert_eq!(brute, fast, "trial {} n {} k {} q {} blocks {:?}", trial, n, k, qmax, blocks);
        }
    }
    println!(
        "selftest ok: F3 arithmetic; 200 random codes against brute force ({} with R != 0, {} with information \
         coordinates in blocks), Gray-walk depth 0, 1, 3, 10",
        nonzero, with_blk_info
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
    let blocks = parse_blocks(&args[2], code[0].len());
    let threads: usize = args.get(3).map(|t| t.parse().unwrap()).unwrap_or(4);
    let t0 = std::time::Instant::now();
    let (s, r) = rsigma(&code, &blocks, threads, 10);
    println!("n {}", s.n);
    println!("k {}", s.k);
    println!("info_outside {}", s.info_out.len());
    println!("info_in_blocks {}", s.info_blk.len());
    println!("patterns 2^{}*3^{}", s.info_out.len(), s.info_blk.len());
    println!("seconds {:.1}", t0.elapsed().as_secs_f64());
    println!("R {}", r);
}
