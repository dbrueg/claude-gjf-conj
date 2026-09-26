# GJF Conjecture 1.4: indices of self-dual ternary codes

This repo holds research notes and code on Gaiotto–Johnson-Freyd, *Holomorphic SCFTs with small index*, Canad. J. Math. 74(2) (2022) 573–601, arXiv:1811.00589, **Conjecture 1.4**:

> The index of any self-dual ternary code is divisible by 24, even if the length is merely divisible by 12. For all lengths c = 12k there exists a self-dual ternary code of index 24.

Index(C) = #even − #odd maximal (full-weight) codewords, where parity is the number of 1s.

## Status (2026-09-26)

| part | status | where |
|---|---|---|
| 24 \| Index for all codes (divisibility half) | **proved**, two proofs. Proof I uses Kneser neighbours and Fourier analysis on F₃ⁿ. Proof II uses a signed 2-design and M₂(SL₂ℤ) = 0; its lattice form covers odd unimodular lattices of rank 12k with shadow minimum ≥ k. | notes §1, §2 |
| index-24 code at every length 12k (existence half) | **proved for k = 2^j** by explicit Hadamard doubling from the Golay code (Thm 5.7). Known for k ≤ 5 (GJF Ex 5.7). **Open** otherwise; the first open case is k = 6. | notes §5.1(f″) |
| by-products | Lemma 5.2 (neighbours of direct sums have 72 \| Index). Lemma 5.3 (gluing divisibility). Thm 5.4 (Hadamard doubling preserves Index mod 48). Prop 5.5 (#even ≡ #odd ≡ 0 mod 8 maximal codewords). Lemma 5.6 (refinement invariance). | notes §5.1 |

**Reduction of the open cases.** For each odd k₀ ≥ 3 two things are needed:
1. An index-24 code at length 12k₀ (known for k₀ = 3, 5).
2. A *seed*: a length-12k₀ code E and a 4-block partition σ with S_σ(E) = Index(H(E ⊕ σT)) = ±24. A seed gives every length 12k₀·2^j with j ≥ 1.

## Layout

```
notes/ternary-code-index.md   the notes (read §0, then §5.1)
notes/tmf-context.md          TMF background
CLAUDE.md                     working instructions and handoff for Claude Code sessions
ternary60/                    Rust crate (std only): index computation, neighbour walks, design checks
  src/main.rs                 `ternary60 selftest | index <file> | pless <q> | xqr <p> | random | walk | batch | nbr | design | allnbrs | dc`
  codes/                      generator matrices (rows of digits 0/1/2): P17, P23, P29, XQR47, XQR59, index24_len60
  runs/                       logs of the Rust runs cited in notes §4; seeds.txt is written by the seed search
  theory/                     stdlib Python: invariant theory, q-series checks, and the existence_*.py experiments (each with .log)
scratch/                      exploratory scripts (not canonical; cited in notes §5.1(e))
scripts/fetch_gjf_source.sh   downloads GJF's arXiv TeX source into literature/ (gitignored)
```

## Quickstart

```bash
cd ternary60 && cargo build --release && ./target/release/ternary60 selftest
./target/release/ternary60 index codes/index24_len60.txt        # n=60, I=24
cd theory
python3 existence_refinement.py      # Lemma 5.6 + Theorem 5.7 checks (~minutes)
python3 existence_mod48.py           # Thm 5.4 + Prop 5.5 checks (~15 min)
python3 existence_seed_search.py --code ../codes/P17.txt --tries 300 --seed 1   # next open step
```

Python scripts are stdlib only; numpy was not available on the original machine. Check scripts write `<script>.log` beside themselves.

## Cost of computing Index(C)

`ternary60 index` enumerates 2^{n/2−1} words on 8 cores:

| n | time per code |
|---|---|
| 60 | ≈ 0.15 s |
| 72 | ≈ 10 s |
| 84 | ≈ 10 min (extrapolated: 64× the n = 72 time) |
| ≥ 96 | infeasible |

Python brute force (`brute_index`) is practical up to n = 24, since that is 3¹² words.
