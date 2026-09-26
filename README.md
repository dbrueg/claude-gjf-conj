# GJF Conjecture 1.4: indices of self-dual ternary codes

This repo holds research notes and code on Gaiotto–Johnson-Freyd, *Holomorphic SCFTs with small index*, Canad. J. Math. 74(2) (2022) 573–601, arXiv:1811.00589, **Conjecture 1.4**:

> The index of any self-dual ternary code is divisible by 24, even if the length is merely divisible by 12. For all lengths c = 12k there exists a self-dual ternary code of index 24.

Index(C) = #even − #odd maximal (full-weight) codewords, where parity is the number of 1s.

## Status (2026-09-26)

| part | status | where |
|---|---|---|
| 24 \| Index for all codes (divisibility half) | **proved** and **formally verified in Lean 4** (`lean/GJF/Divisibility.lean`; positive length). Several proofs; the shortest is one Poisson summation (notes §2 Step 1′). Proof I uses Kneser neighbours and Fourier analysis on F₃ⁿ. Proof II uses a signed 2-design and M₂(SL₂ℤ) = 0; its lattice form covers odd unimodular lattices of rank 12k with shadow minimum ≥ k. | notes §1, §2 |
| index-24 code at every length 12k (existence half) | **proved for all k** and **formally verified in Lean 4** (`lean/GJF/Existence.lean`), by an explicit construction: partial Hadamard quadrupling from the Golay code adds 24 to the length and keeps a block-weighted index R_σ = ±24 (Lemma 5.8, Thm 5.9). Verified on explicit codes at n = 24–84. Web literature check found no prior solution; awaiting a full citation search and an independent reading. | notes §5.1(f‴) |
| by-products | Lemma 5.2 (neighbours of direct sums have 72 \| Index). Lemma 5.3 (gluing divisibility). Thm 5.4 (Hadamard doubling preserves Index mod 48). Prop 5.5 (#even ≡ #odd ≡ 0 mod 8 maximal codewords). Lemma 5.6 (refinement invariance). Thm 5.7 (lengths 12·2^j by doubling). | notes §5.1 |

**How the existence proof works.** For a code E and a set σ of b disjoint 4-blocks, R_σ(E) weights each codeword by φ on the coordinates outside the blocks and by λ = (0, −2, 0, 0, 1)(|c ∩ β|) on each block. Hadamard-doubling the blocks twice against tetracodes gives a self-dual code of length m + 12b and index R_σ(E), and it carries a new 2-block system with the same R. Starting from Golay with b = 1 or b = 2 gives every length 12k.

## Layout

```
notes/ternary-code-index.md   the notes (read §0, then §5.1)
paper/index24.tex (+ .pdf)    short paper draft: index-24 codes in every length 12k (pdflatex, 2 passes)
paper/divisibility.tex (+ .pdf) the divisibility proofs: GJF, Kneser neighbours, modular 2-design, finite Poisson 2-design
notes/tmf-context.md          TMF background
lean/                         Lean 4 + Mathlib: both halves formally verified (GJF.conjecture_1_4). Divisibility.lean (24 | Index), Existence.lean (index 24 at every 12k), Orthogonal.lean (link to Mathlib's C^⊥); setup in CLAUDE.md
CLAUDE.md                     working instructions and handoff for Claude Code sessions
ternary60/                    Rust crate (std only): index computation, neighbour walks, design checks
  src/main.rs                 `ternary60 selftest | index <file> | pless <q> | xqr <p> | random | walk | batch | nbr | design | allnbrs | dc`
  codes/                      generator matrices (rows of digits 0/1/2): P17, P23, P29, XQR47, XQR59, index24_len60,
                              quad_index24_len{24,…,84} (Thm 5.9 chain, written by theory/existence_quadruple.py)
  runs/                       logs of the Rust runs cited in notes §4; seeds.txt is written by the seed search
  theory/                     stdlib Python: invariant theory, q-series checks, and the existence_*.py experiments (each with .log)
                              divisibility_check.py: critical check of the finite proof (log beside it)
                              design_poisson.py: checks for the finite proof of (◆), notes §2 Step 1′ (log beside it)
                              paper_check.py: independent re-implementation of every computable claim in paper/index24.tex (log beside it)
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
python3 existence_quadruple.py       # Lemma 5.8 + Theorem 5.9: index 24 at every length (≈ 30 min; --no84 skips n = 84)
python3 divisibility_check.py        # critical check of the finite proof, incl. four-point identity (≈ 5 min)
python3 design_poisson.py            # finite Poisson proof of the signed 2-design (notes §2 Step 1′) (≈ 5 min)
python3 paper_check.py               # every computable claim of paper/index24.tex, incl. a sign-exact Index at n = 36 (≈ 15 min)
```

Lean (formal proof of 24 | Index; toolchain and Mathlib-cache setup in CLAUDE.md):

```bash
cd lean && lake build                # builds GJF.conjecture_1_4 (both halves); ≈ 2 min for Existence.lean
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
