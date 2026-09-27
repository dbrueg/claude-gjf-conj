# GJF Conjecture 1.4: indices of self-dual ternary codes

This repo holds research notes and code on Gaiotto–Johnson-Freyd, *Holomorphic SCFTs with small index*, Canad. J. Math. 74(2) (2022) 573–601, arXiv:1811.00589, **Conjecture 1.4**:

> The index of any self-dual ternary code is divisible by 24, even if the length is merely divisible by 12. For all lengths c = 12k there exists a self-dual ternary code of index 24.

Index(C) = #even − #odd maximal (full-weight) codewords, where parity is the number of 1s.

## Status (2026-09-26)

| part | status | where |
|---|---|---|
| 24 \| Index for all codes (divisibility half) | **proved** and **formally verified in Lean 4** (`lean/GJF/Divisibility.lean`; positive length). Several proofs; the shortest is one Poisson summation (notes §2 Step 1′). Proof I uses Kneser neighbours and Fourier analysis on F₃ⁿ. Proof II uses a signed 2-design and M₂(SL₂ℤ) = 0; its lattice form covers odd unimodular lattices of rank 12k with shadow minimum ≥ k. | notes §1, §2 |
| index-24 code at every length 12k (existence half) | **proved for all k** and **formally verified in Lean 4** (`lean/GJF/Existence.lean`), by an explicit construction: partial Hadamard quadrupling from the Golay code adds 24 to the length and keeps a block-weighted index R_σ = ±24 (Lemma 5.8, Thm 5.9). Verified on explicit codes at n = 24–84. Web literature check found no prior solution; awaiting a full citation search and an independent reading. | notes §5.1(f‴) |
| GJF **Main Question** (a holomorphic N=1 VOA with c = 12k and index 24/gcd(k,24)) | **answered for every k**, given GJF's orbifold theorem (its fermionic part is only sketched in GJF: Hypothesis ORB) and the cited VOA inputs. For 8 ∤ k via GJF Thm 5.6, by building the needed code automorphism into the construction (J-chain from Golay; ℤ/12-chains from a searched length-36 seed). For 8 \| k the cyclic route is impossible (g⁴ = −1 forces 48 \| Index), but a quaternion group Q₈ works: its anomaly is 3k times a class of order 8, so it vanishes for 8 \| k (index 3). For k ≡ 0 mod 24, Q₈ × ℤ/3 on a chain from a length-72 seed (index 1). The orbifold index for these non-cyclic groups is proved in `notes/orbifold-index.md`; a Lean blueprint with a size estimate is in `notes/blueprint/`. | `notes/main-question.md` |
| by-products | Lemma 5.2 (neighbours of direct sums have 72 \| Index). Lemma 5.3 (gluing divisibility). Thm 5.4 (Hadamard doubling preserves Index mod 48). Prop 5.5 (#even ≡ #odd ≡ 0 mod 8 maximal codewords). Lemma 5.6 (refinement invariance). Thm 5.7 (lengths 12·2^j by doubling). | notes §5.1 |

**How the existence proof works.** For a code E and a set σ of b disjoint 4-blocks, R_σ(E) weights each codeword by φ on the coordinates outside the blocks and by λ = (0, −2, 0, 0, 1)(|c ∩ β|) on each block. Hadamard-doubling the blocks twice against tetracodes gives a self-dual code of length m + 12b and index R_σ(E), and it carries a new 2-block system with the same R. Starting from Golay with b = 1 or b = 2 gives every length 12k.

## Layout

```
notes/ternary-code-index.md   the notes (read §0, then §5.1)
notes/main-question.md        GJF's Main Question: code automorphisms, equivariant chains, the g⁴ = −1 obstruction
notes/orbifold-index.md       Theorem O: Index(V//G) = ±Index(C)/|G| for all groups used (cyclic, Q₈, Q₈ × ℤ/3)
notes/blueprint/              Lean blueprint for the Main Question (README.md: dependency list, trusted base, size estimate)
paper/index24.tex (+ .pdf)    short paper draft: index-24 codes in every length 12k (pdflatex, 2 passes)
paper/main-question.tex (+ .pdf)  second draft: the Main Question for all k (Theorems A–D), and the obstruction
paper/divisibility.tex (+ .pdf) the divisibility proofs: GJF, Kneser neighbours, modular 2-design, finite Poisson 2-design
notes/tmf-context.md          TMF background
lean/                         Lean 4 + Mathlib (see lean/README.md): both halves formally verified (GJF.conjecture_1_4). Divisibility.lean (24 | Index), Existence.lean (index 24 at every 12k), Orthogonal.lean (link to Mathlib's C^⊥); setup in CLAUDE.md
CLAUDE.md                     working instructions and handoff for Claude Code sessions
ternary60/                    Rust crate (std only): index computation, neighbour walks, design checks
  src/main.rs                 `ternary60 selftest | index <file> | pless <q> | xqr <p> | random | walk | batch | nbr | design | allnbrs | dc`
                              `| words <file> <w>` (all codewords of weight ≤ w) `| rsigma <file> <blocks>` (R_σ, sign-exact, any linear code)
                              `| sl2words <U-file> <b0> [systems]` (Q₈-invariant codes F₃²⊗U: good planes, index and orbit-block R_σ, sign-exact; notes main-question §9)
  src/bin/rsigma_is.rs        `rsigma_is <file> <blocks> [threads] | selftest`: R_σ by information-set enumeration from the definition (no code shared with main.rs; the independent check of R_σ(E₇₂) = 24)
  src/bin/rsigma_mitm.rs      `rsigma_mitm <file> <blocks> [threads]`: a third evaluator of the same sum (a reviewer's; table instead of Gray walk)
  codes/                      generator matrices (rows of digits 0/1/2): P17, P23, P29, XQR47, XQR59, index24_len60,
                              quad_index24_len{24,…,84} (Thm 5.9 chain, written by theory/existence_quadruple.py)
                              gjf_ex57_len{12,…,60}: GJF's Example 5.7 codes (from their TeX); z12seed_len36_*: seeds (mainq_seed_search.py)
                              jchain_len<n> (+ .gens.txt), z12chain_len<n> (+ .gens.txt), q8chain_len<n>: the equivariant chains (generators space-separated;
                              the older .J.txt/.g.txt files, row 1 permutation without separators, row 2 signs 1/2, are ambiguous and kept for old logs)
                              q8z3_len72_T0 (+ .U.txt): Q₈ × ℤ/3-invariant code with T_h = 0 and Index −3840 ≢ 0 mod 72 (refutes the 72-rule)
                              q8z3_seed72 (+ .U.txt), q8z3_chain_len{144,288} (+ .gens.txt): the Q₈ × ℤ/3 chain for k ≡ 0 mod 24 (index 24, T_h = 0)
  runs/                       logs of the Rust runs cited in notes §4; seeds.txt is written by the seed search
  theory/                     stdlib Python: invariant theory, q-series checks, and the existence_*.py experiments (each with .log)
                              divisibility_check.py: critical check of the finite proof (log beside it)
                              design_poisson.py: checks for the finite proof of (◆), notes §2 Step 1′ (log beside it)
                              paper_check.py: independent re-implementation of every computable claim in paper/index24.tex (log beside it)
                              mainq_common.py, mainq_equivariant.py: monomial maps, fixed codes, twined counts; equivariant Q_σ
                              mainq_jchain.py, mainq_z12chain.py, mainq_seed_search.py, mainq_obstruction.py: Main Question checks (logs beside them)
                              mainq_automorphisms.py: automorphism groups via nauty (needs $DREADNAUT; scripts/build_nauty.sh)
                              mainq_q8chain.py, mainq_q8_anomaly.py: Q₈-equivariant chain; the Q₈ anomaly (reduction checks, eta invariants)
                              mainq_q8_gauging.py: the coprime-gauging step of Thm 8.1 (multi-neighbour data; GJF's cyclic anomalies vs 3k·a; log beside it)
                              mainq_orbifold_index.py: the orbifold index for cyclic, Q₈ and Q₈ × ℤ/3 groups (notes/orbifold-index.md; log beside it)
                              mainq_q8_orbifold_character.py: the facts behind μ (exact eta identities; S-invariance of the would-be Q₈-orbifold character; log beside it)
                              mainq_e72_infoset.py: R_σ(E₇₂) = +24 and Index(E₇₂) = −1608 by information-set enumeration (src/bin/rsigma_is.rs, rsigma_mitm.rs), independent of sl2words (log beside it)
                              mainq_gens_files.py: unambiguous .gens.txt generator files for the J- and ℤ/12-chains (log beside it)
                              blueprint_equivariant.py: checks for notes/blueprint/equivariant-quadrupling.md (placements, local identities, equivariance, collapse; log beside it)
                              blueprint_chains.py: checks for notes/blueprint/chains-and-seeds.md (seed values sign-exact, splits, coverage, data files; log beside it)
                              blueprint_anomaly.py: checks for notes/blueprint/anomalies.md (Majorana layer, Frame shapes, Sylow detection, cyclic kernel, Clifford traces, Prop 4.7; log beside it)
                              blueprint_foundations.py: checks for notes/blueprint/orbifold-foundations.md (Ramond ground states, twisted modules of odd lattices, vacuum energy; log beside it)
                              mainq_q8_nonanomaly.py: non-anomaly for 8 | k directly (rSH³(Q₈) via free fermions; μ on codes and direct sums; log beside it)
                              mainq_q8_twisted.py: the Q₈-action on the (−1)-twisted sector (frame Clifford module, modular normalisation, μ = S³/Q₈ value; log beside it)
                              mainq_q8z3.py: Q₈ × ℤ/3 codes at n = 36 (the 72 | Index rule seen there)
                              mainq_morita.py: Q₈-invariant codes as F₃² ⊗ U (Morita form), h-invariant Lagrangians, free lifts over F₃[u]/u³
                              mainq_72rule.py: the 72-rule: exact laws at n = 12, 24, 36 and counterexamples at n = 72 (log beside it)
                              mainq_q8z3_seed72.py: search for length-72 seeds of a Q₈ × ℤ/3 chain to k ≡ 0 mod 24 (log beside it)
                              mainq_q8z3_chain24.py: the seed and its chain to n = 144, 288 (Main Question for k ≡ 0 mod 24; log beside it)
                              lean_seed_data.py: Lean literals of the Tier A seeds (bitmask rows, block orderings with local maps in LM, evaluation trees), each seed value recomputed (log per seed)
scratch/                      exploratory scripts (not canonical; cited in notes §5.1(e))
scripts/fetch_gjf_source.sh   downloads GJF's arXiv TeX source into literature/ (gitignored)
scripts/build_nauty.sh        builds nauty's dreadnaut into tools/ (gitignored), for mainq_automorphisms.py
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
python3 mainq_jchain.py              # J-chain: m = 4 (≈ 2 min)
python3 mainq_z12chain.py            # ℤ/12 chains: m = 3, 6, 12 (≈ 30 min; the n = 144 twined count dominates)
python3 mainq_obstruction.py         # g⁴ = −1 ⇒ 48 | Index, and the four-code identity (≈ 20 min)
python3 mainq_72rule.py              # the 72-rule: laws at n ≤ 36, counterexamples at n = 72 (≈ 10 min)
python3 mainq_q8z3_chain24.py        # k ≡ 0 mod 24: the length-72 seed and its chain to n = 288 (≈ 15 min)
```

Lean (formal proof of 24 | Index; toolchain and Mathlib-cache setup in CLAUDE.md):

```bash
cd lean && lake build                # builds GJF.conjecture_1_4 (both halves); ≈ 2 min for Existence.lean
```

Python scripts are stdlib only (numpy was not available on the original machine); `mainq_automorphisms.py` additionally calls nauty's `dreadnaut`. Check scripts write `<script>.log` beside themselves.

## Cost of computing Index(C)

`ternary60 index` enumerates 2^{n/2−1} words on 8 cores:

| n | time per code |
|---|---|
| 60 | ≈ 0.15 s |
| 72 | ≈ 10 s |
| 84 | ≈ 10 min (extrapolated: 64× the n = 72 time) |
| ≥ 96 | infeasible |

Python brute force (`brute_index`) is practical up to n = 24, since that is 3¹² words.
