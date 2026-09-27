//! rsigma_mitm: a third evaluator of R_σ(E), written by an independent reviewer (a separate agent that had
//! read rsigma_is.rs but shares no code with it or with src/main.rs), 2026-09-27. Same definition as
//! rsigma_is (φ = (0, −1, +1) outside the blocks, λ = (0, −2, 0, 0, 1) on block weights), different choices:
//! - information coordinates chosen in reverse order (outside the blocks first);
//! - Gaussian elimination with a tracked transform, checked in both directions;
//! - full-length words as u128 bit planes (n ≤ 128), a different bit-sliced F₃ addition;
//! - a table of all 2^l words on the last l ≤ 20 outside information coordinates, combined with an outer loop
//!   over the remaining ones (radix 2) and the block information coordinates (radix 3); no Gray code.
//! Usage: rsigma_mitm <code-file> <blocks> [threads]   (blocks as for rsigma_is). Output: "n k a b", "R <value>".
use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Clone, Copy, Default)]
struct W { a: u128, b: u128 } // a: value 1, b: value 2

#[inline(always)]
fn addw(x: W, y: W) -> W {
    let t = (x.a | y.b) ^ (x.b | y.a);
    W { a: (x.b | y.b) ^ t, b: (x.a | y.a) ^ t }
}
fn scal(x: W, c: u8) -> W { match c { 0 => W::default(), 1 => x, _ => W { a: x.b, b: x.a } } }

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let txt = std::fs::read_to_string(&args[1]).unwrap();
    let rows: Vec<Vec<u8>> = txt.lines().filter(|l| !l.trim().is_empty())
        .map(|l| l.trim().bytes().map(|c| { assert!(c >= b'0' && c <= b'2'); c - b'0' }).collect()).collect();
    let n = rows[0].len();
    assert!(n <= 128 && rows.iter().all(|r| r.len() == n));
    let mut blk: Vec<Vec<usize>> = Vec::new();
    if args[2] != "-" {
        for b in args[2].split(';') { blk.push(b.split(',').map(|x| x.parse().unwrap()).collect()); }
    }
    let threads: usize = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(4);
    let mut inb = vec![false; n];
    for b in &blk { assert_eq!(b.len(), 4); for &i in b { assert!(!inb[i]); inb[i] = true; } }
    // column order: outside coordinates in REVERSE order, then block coordinates in reverse
    let order: Vec<usize> = (0..n).rev().filter(|&i| !inb[i]).chain((0..n).rev().filter(|&i| inb[i])).collect();
    // Gaussian elimination with a tracked transform to verify both inclusions
    let m0 = rows.len();
    let mut m: Vec<Vec<i32>> = rows.iter().map(|r| r.iter().map(|&v| v as i32).collect()).collect();
    let mut tr: Vec<Vec<i32>> = (0..m0).map(|i| (0..m0).map(|j| (i == j) as i32).collect()).collect();
    let mut piv = vec![];
    let mut r = 0;
    for &c in &order {
        if r == m0 { break; }
        let Some(p) = (r..m0).find(|&i| m[i][c] != 0) else { continue };
        m.swap(r, p); tr.swap(r, p);
        let s = m[r][c]; // s^{-1} = s in F3
        for j in 0..n { m[r][j] = m[r][j] * s % 3; }
        for j in 0..m0 { tr[r][j] = tr[r][j] * s % 3; }
        for i in 0..m0 {
            if i != r && m[i][c] != 0 {
                let f = m[i][c];
                for j in 0..n { m[i][j] = (m[i][j] - f * m[r][j]).rem_euclid(3); }
                for j in 0..m0 { tr[i][j] = (tr[i][j] - f * tr[r][j]).rem_euclid(3); }
            }
        }
        piv.push(c); r += 1;
    }
    let k = r;
    // verify: sys rows = T * input; input rows in span(sys)
    for t in 0..k {
        for j in 0..n {
            let v: i32 = (0..m0).map(|i| tr[t][i] * rows[i][j] as i32).sum::<i32>().rem_euclid(3);
            assert_eq!(v, m[t][j]);
        }
    }
    for row in &rows {
        for j in 0..n {
            let v: i32 = (0..k).map(|t| row[piv[t]] as i32 * m[t][j]).sum::<i32>().rem_euclid(3);
            assert_eq!(v, row[j] as i32);
        }
    }
    let tow = |v: &Vec<i32>| { let mut w = W::default(); for j in 0..n { if v[j] == 1 { w.a |= 1u128 << j } else if v[j] == 2 { w.b |= 1u128 << j } } w };
    let sysw: Vec<W> = (0..k).map(|t| tow(&m[t])).collect();
    let out_idx: Vec<usize> = (0..k).filter(|&t| !inb[piv[t]]).collect();
    let blk_idx: Vec<usize> = (0..k).filter(|&t| inb[piv[t]]).collect();
    let mut outmask = 0u128; for i in 0..n { if !inb[i] { outmask |= 1u128 << i } }
    let bmasks: Vec<u128> = blk.iter().map(|b| b.iter().fold(0u128, |acc, &i| acc | (1u128 << i))).collect();
    let lam = [0i64, -2, 0, 0, 1];
    // L = last `l` outside rows (table), H = the rest (outside, radix 2) + block rows (radix 3)
    let a = out_idx.len();
    let l = a.min(20);
    let lrows: Vec<W> = out_idx[a - l..].iter().map(|&t| sysw[t]).collect();
    let hrows: Vec<W> = out_idx[..a - l].iter().map(|&t| sysw[t]).collect();
    let brows: Vec<W> = blk_idx.iter().map(|&t| sysw[t]).collect();
    let mut table = vec![W::default(); 1 << l];
    for mask in 0..(1usize << l) {
        let mut w = W::default();
        for j in 0..l { w = addw(w, scal(lrows[j], if (mask >> j) & 1 == 1 { 2 } else { 1 })); }
        table[mask] = w;
    }
    let nh: u64 = (1u64 << hrows.len()) * 3u64.pow(brows.len() as u32);
    let next = AtomicU64::new(0);
    let total: i64 = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads).map(|_| sc.spawn(|| {
            let mut acc = 0i64;
            loop {
                let h = next.fetch_add(1, Ordering::Relaxed);
                if h >= nh { break; }
                let mut base = W::default();
                let hb = h & ((1u64 << hrows.len()) - 1);
                let mut hc = h >> hrows.len();
                for j in 0..hrows.len() { base = addw(base, scal(hrows[j], if (hb >> j) & 1 == 1 { 2 } else { 1 })); }
                for j in 0..brows.len() { base = addw(base, scal(brows[j], (hc % 3) as u8)); hc /= 3; }
                for w0 in table.iter() {
                    let w = addw(base, *w0);
                    let nz = w.a | w.b;
                    if nz & outmask != outmask { continue; }
                    let mut v: i64 = if (w.a & outmask).count_ones() & 1 == 1 { -1 } else { 1 };
                    for &bm in &bmasks { v *= lam[(nz & bm).count_ones() as usize]; if v == 0 { break; } }
                    acc += v;
                }
            }
            acc
        })).collect();
        hs.into_iter().map(|h| h.join().unwrap()).sum()
    });
    println!("n {} k {} a {} b {}", n, k, a, blk_idx.len());
    println!("R {}", total);
}
