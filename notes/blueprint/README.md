# Lean blueprint for the answer to GJF's Main Question

Written 2026-09-27. This directory prepares a Lean formalization of the answer to the Main Question ([MQ] = `notes/main-question.md`, Cor 10.2): for every k ≥ 1 there is a holomorphic N=1 SVOA of central charge 12k with index 24/gcd(k, 24).

Each file states definitions and lemmas in a Lean-ready form and proves them in full. It separates what is proved ([P]), checked by computation ([V], with a script), cited ([T]), or cited with only a sketched super-VOA proof ([T*]). Each file ends with a list of issues found in the older notes. Status labels are as in the notes.

Nothing here is formalized yet. The existing Lean development (`lean/`, 1,639 lines) proves Conj 1.4 (`GJF.conjecture_1_4`). It covers [I] Lemma 5.8 only in the special case used by Thm 5.9.

## 1. Files

| file | tag | content | script (log beside it) |
|---|---|---|---|
| `equivariant-quadrupling.md` | [EQ] | partial quadrupling in general (all 8 tetracode placements, all splits, any set of refined blocks, any linear E); equivariance ([MQ] Lemma 4.1 expanded: extension, transport, inherited data, placement existence at both steps, local types); collapsed fixed codes ([MQ] Lemma 4.3: T_h = R_σ̄(D)); the equivariant chain engine | `ternary60/theory/blueprint_equivariant.py` (≈ 35 s) |
| `chains-and-seeds.md` | [CS] | each chain (J, ℤ/12 A and B, Q₈, Q₈ × ℤ/3) as an exact inductive statement; every seed certificate with its size and a Lean route; coverage of all k; the data files | `ternary60/theory/blueprint_chains.py` (≈ 3 min) |
| `anomalies.md` | [AN] | the anomaly side: interface (A1)–(A11); cyclic anomalies from Frame shapes (GJF Ex 4.4, including the odd-lattice m = 3 step); Sylow detection for Q₈ × ℤ/3; the Q₈ theorem (non-anomalous iff 8 \| k) with a counting proof of the cyclic kernel | `ternary60/theory/blueprint_anomaly.py` (53 checks) |
| `orbifold-foundations.md` | [OF] | the VOA inputs with exact sources: the Ramond sector and GJF Prop 2.4 sign-exact; twisted modules of odd lattice SVOAs (BK04); vacuum energy; modular covariance (DZ05); regularity of V^G (CM16 on V₀̄); the G̃-crossed structure (McR21); Hypothesis ORB | `ternary60/theory/blueprint_foundations.py` (≈ 3 s) |
| `../orbifold-index.md` | [OI] | Theorem O: Index(V//G) = ±Index(C)/\|G\| for all groups used, including Q₈ and Q₈ × ℤ/3 | `ternary60/theory/mainq_orbifold_index.py` |

## 2. The proof of the answer, as a dependency list

The Main Question is answered per residue class of k mod 24 ([MQ] §6, [CS] §0):
- m = gcd(k,24) ∈ {1, 2}: G = 1 or ⟨−1⟩;
- m = 4: ⟨J⟩ with J² = −1;
- m ∈ {3, 6, 12}: ℤ/m inside a ℤ/12 with g⁶ = −1 and T_{g⁴} = 0;
- m = 8: Q₈;
- m = 24: Q₈ × ℤ/3.

In each case the orbifold V_{Λ(C)}//G has index 24/|G|.

| # | node | content | status | where | Lean today |
|---|---|---|---|---|---|
| D1 | codes | F₃-codes, self-duality, f, Index | definitions | [I] | done (`IsSelfDual`, `gjfIndex`) |
| D2 | placements, local identities | 8 placements = the [4,2,3] codes; Lemmas A, B for every placement and split | [P; V] | [EQ] §1–2 | `localA`, `localB` for one placement |
| D3 | partial quadrupling | Q_σ(E) self-dual; F(Q_σE) = R_σ(E); R_σ″(Q_σE) = R_σ(E), for any linear E | [P; V] | [EQ] Thm 3.3 | special case (`engine`) |
| D4 | equivariance | G ⊂ Aut(Q_σE); inherited relations, orders, cycle and sign data; invariant placements exist at every stage | [P; V] | [EQ] §4 (Lemma 4.11) | — |
| D5 | twined counts | T_h(Q_σE) = R_σ̄(D) (collapse) or R^h_σ(E) (orbit weights); constant along chains | [P; V] | [EQ] §5, [CS] Lemma 2.3 | — |
| D6 | seeds | Golay, J; ℤ/12 seed 6 (R = +24, twined 0); Q₈ seed (R = 24); Q₈ × ℤ/3 seed E₇₂ (R_σ = 24, twined 0) | [V] | [CS] §3–4 | Golay only |
| D7 | chains, coverage | every k reached, with the group data H(k) that D9–D12 need | [P; V] | [CS] §3 | m ∈ {1, 2} only |
| D8 | Ramond ground states | V_R = V_{Λ+χ/2}; ground states ↔ maximal codewords; Z_RR = Index(C) exactly | [P, given T] | [OF] §3 | — |
| D9 | Theorem O | Index(V//G) = ±Index(C)/\|G\| | [P, given ORB, T] | [OI] | — |
| D10 | cyclic anomalies | α(ℤ/m) = 2k·ν_m, zero iff m \| k (GJF Thm 5.6's anomaly clause) | [P, given (A7), (A8)] | [AN] §2 | — |
| D11 | Q₈ × ℤ/3 | anomaly vanishes iff both Sylow restrictions do | [P, given (A2), (A5), transfer] | [AN] §3 | — |
| D12 | Q₈ | non-anomalous iff 8 \| k: Clifford traces t_x = 2^{3k}, eta identities, S-invariance of the would-be orbifold character, tetracode sum D₄₈ and additivity | [P, given (A1)–(A11)] | [AN] §4; [MQ] §8.4–8.5 | — |
| D13 | ORB | the orbifold exists and W_R = ⊕ V_{R,g}^{C(g)} | [T*] | [OF] Thm 5.4, Hyp 5.5 | hypothesis |
| D14 | assembly | [MQ] Cor 2.1, Thm 4.2, Thm 4.4, Cor 8.2, Thm 10.1 ⇒ Cor 10.2 | [P] | [MQ] §6, [CS] §3.6 | — |

Not on the path: [MQ] Thm 5.1 (the obstruction 48 | Index when g⁴ = −1) only explains why Q₈ is used; the 72-rule (§8.1, §9) only explains why the Q₈ × ℤ/3 seed is at k = 6.

## 3. The trusted base (what a Lean proof would assume)

- **[T*] ORB** ([OF] Hyp 5.5; [OI] §1). The fermionic part of GJF Thm 4.2: the anomaly lives in S̃H³(G), and a trivialisation gives a holomorphic SVOA W with W_R = ⊕ V_{R,g}^{C(g)}. It is only sketched in GJF ("replace category with supercategory"). The bosonic analogue is a theorem (DNR25, Kirillov, Müger, McR21). Regularity of V^G is a theorem (CM16 on V₀̄, [OF] Thm 5.2).
- **[T] The anomaly interface (A1)–(A11)** ([AN] §1.2). The only item with no written proof even in the bosonic setting is **(A7), the multiplier principle for cyclic groups**, which GJF state without proof. It is used for every cyclic anomaly.
- **[T] VOA theorems with super versions in print:**
  - GJF Thm 3.1 (the lift);
  - Li96 Prop 5.4 (Ramond sector);
  - BK04 Thm 4.2 (twisted modules of odd lattice SVOAs);
  - DZ05 Thms 4.12, 7.7 (uniqueness, modular covariance), with DRY22 Prop 3.4 (g-rationality);
  - McR21 Thms 4.15, 4.17 (G̃-crossed supercategory);
  - CM16 Cor 5.25 (regularity);
  - FLM Thm 1.7.3 (twisted Heisenberg modules).
- **[T] Group cohomology** ([AN] Lemmas 3.1, 4.2): transfer (cor∘res = index), H*(Q₈) via the periodic resolution, and the Bockstein H³(G; U(1)) ≅ H⁴(G; ℤ).
- **[V] only: R_σ(E₇₂) = 24.** It decides k ≡ 0 mod 24 and rests on one program (`ternary60 sl2words`, two code paths). The Morita good-plane formula was cross-checked against direct enumeration only for n ≤ 36. It needs ≈ 5.8·10⁶ good planes, so it is out of kernel reach (§4).

**Observation (not used by the notes; [P, given T]).** Holomorphic N=1 SVOAs are closed under ⊗: c adds, and for c ∈ ℤ the Ramond sectors are of ℂ-type, so the index multiplies up to sign. Hence W₂₄^{⊗q} ⊗ W_r answers k = 24q + r, since gcd(k, 24) = gcd(r, 24). This reduces the Main Question to k ≤ 24. For Lean it saves only ≈ 100–300 lines: the chains are still needed up to n = 288. It does not remove the E₇₂ certificate.

## 4. How many lines would a Lean formalization take? [H]

Calibration. Existence.lean is 805 lines for [I] Lemma 5.8 (special case) plus Thm 5.9, and Divisibility.lean is 662 lines for a proof of a few pages: roughly 200–350 lines per page of elementary proof on Mathlib's finite sums. The earlier estimates for these two files overshot (1,000–2,500 against 805; 600–1,200 against 662). But those files are sum- and `decide`-heavy; group-action bookkeeping, complex analysis and homological algebra tend to overrun instead.

Two independent estimates were made (by component in the four blueprint files, and top-down by tier) and are merged below. All figures are new Lean lines, including blank lines and comments, in this repository's style.

| tier | what is proved | new lines | most likely |
|---|---|---|---|
| **A: code level** | For every k ≥ 1: a self-dual C of length 12k with Index 24 and G ⊂ Aut(C) satisfying the exact hypotheses H(k) of GJF Thm 5.6 / Theorem O (relations, cycle and sign data, T_h = 0, ε = 1, E_g > n/24). R_σ(E₇₂) = 24 is a named hypothesis. | 2,500–5,000 | ≈ 3,500 |
| A + certificate | also machine-check R_σ(E₇₂) = 24 (Morita form, good-plane formula, verified enumerator) | + 800–1,500 | needs `native_decide` |
| **B: conditional answer** | Tier A, plus the VOA side with every [T]/[T*] input of §3 as fields of one hypothesis structure, and everything elementary proved: Theorem O, cyclic anomalies, Sylow detection, the Q₈ theorem (Clifford traces, eta identities, the character argument) and the assembly | + 4,000–9,000 | ≈ + 6,000 (total ≈ 9,500) |
| B-coarse | Tier A, plus GJF Thm 5.6, [MQ] Thm 8.1 and Theorem O themselves as hypotheses (trust-heavy: it assumes the results proved here) | + 300–1,200 | total ≈ 4,500 |
| B + cohomology | also prove transfer, H*(Q₈) and the Bockstein instead of citing them | + 1,500–4,400 | |
| **C: unconditional** | also the VOA foundations: lattice SVOAs, twisted modules, Zhu/DZ05 modular invariance, C₂-cofiniteness of V^G, Huang–Lepowsky–Zhang tensor categories, G-crossed and super fusion categories, GJF Thm 4.2 | + 10⁵–5·10⁵ | multi-year, many people |

Breakdown of Tier A (≈ 2,500–5,000):
- signed-permutation API (Mathlib has `Equiv.Perm`, no signed permutations): 250–400;
- placements and local identities for all placements and splits: 80–180;
- general partial quadrupling with transposed splits and per-orbit refinement: 150–330;
- equivariance: extension, transport through the Hadamard layers and regroupings, inherited data, invariant placements: 350–700;
- twined counts (collapse or orbit weights), sign normalisation: 200–500;
- the equivariant engine and induction: 150–400;
- seed data and small certificates (Golay + J, ℤ/12 seed 6, Q₈ seed, Q₈ × ℤ/3 seed with 729/4,096-word twined sums): 420–900;
- a verified bit-sliced F₃ evaluator for the ℤ/12 seed sums (2.6·10⁵ and 5.9·10⁵ candidates): 300–600;
- code-level group facts behind Theorem O (Lemmas 2.1, 3.2, 3.3 of [OI], ε = 1): 200–450;
- five chain instantiations and the residue-class assembly: 250–500.

Breakdown of Tier B (≈ 4,000–9,000):
- the interface structure (≈ 30–45 fields: SVOA with c and RR index, V_{Λ(C)} and index = gjfIndex, lift, twisted sectors and their characters as functions on Mathlib's ℍ, anomaly groups with layers, restriction and additivity, (A6)–(A11), ORB, modular covariance): 600–1,200;
- Theorem O (supertrace cancellation, reduction to ground states, the evenness lemma, the untwisted and order-3 terms, SL₂(ℤ/3)-orbits): 500–1,000;
- cyclic anomalies (Frame-shape formula from (A7), q² rule, odd-lattice m = 3 step): 800–1,600;
- missing modular-forms infrastructure: 500–1,200. Mathlib master (2026-09-27) has η and its S-law, `eta_comp_eq_csqrt_I_inv` in `NumberTheory/ModularForms/Discriminant.lean`, and the Jacobi θ functional equation. Still needed are the scaled/translated branches (2τ, τ/4, τ − ½), the Euler identity for η(τ − ½), and θ with characteristics;
- supercohomology diagram chases (Sylow detection, the cyclic kernel {0, κ} by counting): 350–750;
- the Q₈ theorem ((−1)-twisted Clifford traces, the eta identities, the S-invariance argument with the leading-exponent separation, the tetracode sum and additivity): 1,200–2,200;
- final assembly: 100–250.

Main risks:
- **The E₇₂ certificate.** A kernel-only Tier A needs a new seed with a cheap certificate, or a new reduction; neither exists yet.
- **Kernel time** for the ℤ/12 seed sums is unmeasured (no Lean toolchain in this container).
- **Interface faithfulness.** A mis-stated field makes the theorem vacuous or wrong, and no model can be built without Tier C. Examples: the index sign, the trivialisation torsor, the ν_m normalisation, a missing KJ = −JK hypothesis. Use `structure` hypotheses, never global `axiom`s, and review each field against its source.
- **Dependent-type bookkeeping** for nested Sum/product coordinate types (the CLAUDE.md pitfalls).
- **Branch tracking** in the complex analysis.

For scale (`.lean` lines in clones of 2026-09-27, except the LTE):
- this repository: 1,639 lines;
- Mathlib `NumberTheory/ModularForms/`: 8,957;
- Mathlib `Algebra/Vertex`: 261;
- sphere eversion: 14,936;
- PFR: 21,975;
- Carleson: 49,947;
- the Imperial FLT project: 58,786 (ongoing);
- the Liquid Tensor Experiment: reported > 70,000.

So Tier A is about 4–5 times Existence.lean, and Tier B is the size of a mid-sized formalization project (sphere eversion, half of PFR). Tier C is several times the LTE, and most of it is general VOA theory rather than anything specific to this problem.

**Recommended order.**
1. The signed-permutation API and the general quadrupling (D2–D3). This also lets the Lean Thm 5.9 codes coincide with the chain codes; today `Tfin` is not J-invariant.
2. Equivariance and twined counts (D4–D5).
3. The J-chain and the Q₈-chain (cheap seeds).
4. The ℤ/12 chains with the verified evaluator.
5. The Q₈ × ℤ/3 chain with E₇₂ as a hypothesis.
6. Tier A assembly.
7. Then Tier B, starting with Theorem O and the Ramond ground states (D8–D9), which reuse `gjfIndex`.

## 5. Issues found by the blueprint pass, and their status

| issue | where | status |
|---|---|---|
| "the order-3 lift is unique"; "acts on fixed ground states by 1" | [OI] §3.2 | fixed 2026-09-27 ([OI] §5): Z_RR(1,h) = ±ζT_h |
| Ramond decomposition attributed to GJF Thm 4.2; fermionic Thm 4.2 labelled [T] | [OI], [MQ] | fixed in [OI]; [MQ] now says [T*] |
| wrong or even-lattice-only citations (DLM, van Ekeren, Lepowsky, Dong–Lepowsky) for super statements | [OI] Lemma 3.1, [MQ] §8.3 | fixed in [OI] (DZ05, BK04, Li96, M(1) argument) |
| dangling reference `notes/lean-blueprint.md` | [OI] §4 | fixed (points to [OF]) |
| refinement split: [MQ] §4 "Conventions" describes the canonical split; the scripts use the pair-preserving (transposed) split, without which the ℤ/12 chains miss k ≡ 6, 9 mod 12 for k ≥ 18 | [MQ] §4 | fixed in [MQ] §4 |
| Lemma 4.1(3) "the construction iterates" needs invariant placements at both steps of each stage ([EQ] Lemma 4.11) | [MQ] §4 | noted in [MQ] §4 |
| Thm 4.4: chains from seed 3 have Index −24; one coordinate must be re-signed | [MQ] §4 | noted in [MQ] §4 |
| κ names two classes in §8 | [MQ] §8.4 | noted in [MQ] §8.4 |
| Prop 8.5.2: ε⁴ = 1 uses 4h_x ∈ ℤ; ε = ±1 needs W_x ≠ 0 | [MQ] §8.5 | noted; full proof in [AN] Prop 4.7 |
| [I] Lemma 5.8 is stated for self-dual E but applied to the non-self-dual D | [MQ] Lemma 4.3 | wording; [EQ] Thm 3.3 proves it for any linear E |
| Existence.lean's `Tfin` is not J-invariant, so the Lean Thm 5.9 codes are not the chain codes | `lean/` | open (Tier A step 1) |
| ambiguous generator files `jchain_len*.J.txt`, `z12chain_len*.g.txt` (up to 888 parses) | `ternary60/codes/` | fixed: separated `.gens.txt` copies written; old files kept for the logs that cite them |
| R_σ(E₇₂) = 24 rests on one program | [MQ] §10 | open: an independent second implementation is wanted |
| GJF typos: Ex 4.4 exponent for m odd (2m/k); Thm 5.6 proof "3(m/2) − 2×odd" should be 6×odd; the m = 3 step cites even-lattice results | GJF | recorded ([AN] §6, [OF] §9) |
