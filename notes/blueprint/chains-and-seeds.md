# Blueprint: the chains and seeds behind the Main Question

Proof file, 2026-09-27. Purpose: for every residue class of k mod 24, record the chain of codes that answers GJF's Main Question at the code level. For each chain this file gives:
- the seed code and group, the data files and the scripts that build and check them;
- the block system and the exact inductive statement (length, index, group, twined count, next block system);
- the finite facts about the seed that must be certified, the size of each computation, how each could be checked in Lean, and whether the kernel can do it.

The general machinery (partial quadrupling, equivariance, collapse of fixed codes) is proved in the companion blueprint [EQ] = `notes/blueprint/equivariant-quadrupling.md`. This file cites it and proves the chain-specific steps in full. It adds three things:
- an orbit-weighted form of the twined count that needs no collapse (Lemma 2.3);
- an information-set bound for every seed sum, with the sums recomputed independently of the Rust code (Lemma 2.5);
- a way to keep the single placement hard-wired in `lean/GJF/Existence.lean` (Lemma 2.7, and seed 6 in §3.3).

Sources:
- [MQ] `notes/main-question.md`; [I] `notes/ternary-code-index.md`; [OI] `notes/orbifold-index.md`;
- [GJF] `literature/gjf-1811.00589.tex` (Thm 5.6 = `thm.answers`, Thm 3.1 = `thm.symmetries lift`);
- [Lean] `lean/GJF/Existence.lean`.

Status labels: [P] proved in this file (or in [EQ] where cited), [T] cited theorem, [V] exact computation, [H] heuristic estimate.

Script: `ternary60/theory/blueprint_chains.py` (stdlib Python; only Part 6 calls the Rust binary), log `blueprint_chains.log` beside it, ≈ 3 min, cited as [V: Part n].
- It uses its own bit-sliced F₃ arithmetic, and checks every seed number with information-set enumeration, independently of `rsigma` and `sl2words`. The one exception is R_σ of the length-72 seed.
- Part 4 builds its codes with `mainq_equivariant.quad_eq`, the construction under test. Part 7 is the seed-6 search.

--------------------------------------------------------------------------------------------

## 0. Summary

| k mod 24 | m = gcd(k,24) | index | chain | G | seed (file) | σ₀ | codes at k = | largest seed computation |
|---|---|---|---|---|---|---|---|---|
| 1, 5, 7, 11, 13, 17, 19, 23 | 1 | 24 | [I Thm 5.9] | 1 | Golay | – | all k | done in [Lean] |
| 2, 10, 14, 22 | 2 | 12 | [I Thm 5.9] | ⟨−1⟩ | Golay | – | all k | done in [Lean] |
| 4, 20 | 4 | 6 | J-chain (§3.2) | ℤ/4 | Golay, J | (0,1\|2,3) | 2, 4, 6, … | 729 words (`R_golay₁` exists) |
| 3, 9, 15, 21 | 3 | 8 | ℤ/12 seed (k = 3) and chain B (§3.3) | ℤ/12 | `z12seed_len36_{3,6}` | σ_B / σ_B6, b = 6 | 3; 9, 15, 21, … | 589,824 candidates |
| 6, 18 | 6 | 4 | ℤ/12 chain A (§3.3) | ℤ/12 | same | σ_A / σ_A6, b = 3 | 6, 12, 18, … | 262,144 candidates |
| 12 | 12 | 2 | ℤ/12 chain A | ℤ/12 | same | same | same | same |
| 8, 16 | 8 | 3 | Q₈-chain (§3.4) | Q₈ | `q8chain_len24` | 2 orbit blocks | 4, 8, 12, … | 4,096 candidates |
| 0 | 24 | 1 | Q₈×ℤ/3-chain (§3.5) | Q₈×ℤ/3 | `q8z3_seed72(.U)` | 6 orbit blocks | 12, 24, 36, … | **5,812,449 good planes** |

Main points:
- **Seed values, re-verified sign-exactly with independent code** [V: Part 2]:
  - Golay: R_(0,1\|2,3) = 24.
  - `z12seed_len36_3`: Index = +24, R_σA = R_σB = −24.
  - `z12seed_len36_6`: Index = −24, R_σA6 = R_σB6 = +24.
  - `q8chain_len24`: R_σ = +24.
  - The twisted seeds: R^h_σ = T_h = 0 for all four ℤ/12 systems and for the Q₈×ℤ/3 seed.
- **Only one seed fact is out of reach of the Lean kernel:** R_σ(E₇₂) = 24 for the Q₈×ℤ/3 seed (5.8·10⁶ normalised SL₂-words, [MQ] Cor 9.2). Its value was first computed by a single program (`ternary60 sl2words`, two code paths; §7 issue 4); since 2026-09-27 an independent information-set enumeration (`rsigma_is`, `mainq_e72_infoset.py`) confirms +24. Every other seed fact needs at most 589,824 candidate evaluations. Those are within reach of a verified bit-sliced checker, though not of `decide` in the style of [Lean].
- **Twined counts without collapsing** (Lemma 2.3): T_h(Q_σ E) = R^h_σ(E), with one weight per ⟨h⟩-orbit [P; V: Part 4, 24/24 with 12 nonzero values].
- **The refinement split and the placement matter for Lean** (Lemma 2.2, 2.7, §7 issues 1–2).
  - With the split hard-wired in [Lean] (`refd`, `r₂`), the ℤ/12 chains miss k ≡ 6, 9 mod 12 for k ≥ 18 [V: Part 3].
  - With the transposed split, and σ″-blocks ordered (x, y, y**, x**), the fixed placement `Tfin` works for the J-, Q₈- and Q₈×ℤ/3-chains and for ℤ/12-chain A.
  - It fails for the committed chain-B system σ_B. Seed 6 has offset-matched systems σ_A6, σ_B6 for which it works.
- **Data files.** The generator files `jchain_len<n>.J.txt` and `z12chain_len<n>.g.txt` are ambiguous: 3 to 888 parses into a permutation. Exactly one parse satisfies the stated relation, and it is an automorphism [V: Part 5].
- **Lean size.** ≈ 1,200–2,000 lines for this component on top of [EQ]'s ≈ 1,200–1,900; plus ≈ 800–1,200 for the length-72 certificate (§5).

--------------------------------------------------------------------------------------------

## 1. Definitions

**1.1 Weights.** F = F₃ = `ZMod 3`. φ(0, 1, 2) = (0, −1, +1); f(x) = ∏_i φ(x_i); Index(C) = Σ_{x∈C} f(x). This is GJF's #even − #odd (`gjfIndex` in [Lean]). λ(w) = 1 if w = 4, −2 if w = 1, 0 otherwise (`lam`).

**1.2 Ordered blocks, systems, R_σ.**
- A *block* on a finite set X is an ordered 4-tuple β = (β₀₀, β₀₁, β₁₀, β₁₁) of distinct elements. The labels are P = Fin 2 × Fin 2 as in [Lean], and the *split pairs* are π_a(β) = (β_{a0}, β_{a1}) for a = 0, 1 ("pairs = first coordinate").
- A *system* σ is a set of disjoint blocks, and S = X ∖ ⋃σ is the set of *singletons*. Then
      R_σ(E) := Σ_{c∈E} ∏_{i∈S} φ(c_i) ∏_{β∈σ} λ(|supp c ∩ β|),
  with Index = R_∅. R_σ does not depend on the orderings; placements and splits do.

**1.3 Placements and local maps.**
- A *placement* on a block is a monomial image of the tetracode, written in the block's labels.
- T_L := ⟨1110, 0121⟩ in the labels (a, b) ↦ 2a + b. This is `Tfin` of [Lean].
- There are 8 placements [V: Part 1], numbered as in the log. Placement 0 = T_L = ⟨1110, 0121⟩; 1 = ⟨1110, 0122⟩; 2 = ⟨1120, 0111⟩; 3 = ⟨1120, 0112⟩; 4 = ⟨1210, 0221⟩; 5 = ⟨1210, 0222⟩; 6 = ⟨1220, 0211⟩; 7 = ⟨1220, 0212⟩.
- Two classes: 𝒜 = {0, 3, 5, 6} ∋ T_L and ℬ = {1, 2, 4, 7}. Transposing the labels, (a, b) ↦ (b, a), exchanges them.
- *Local maps.* For g = (p, s) ∈ Mon(X) (e_i ↦ s_i e_{p(i)}, as in `mono_apply`) and a block β with gβ also a block, μ_{g,β} ∈ Mon(P) is g read in the labels of β and gβ. Named types, with ε, s₀, s₁ ∈ {±1}:
  - x_{s₀,s₁}: within-pair swaps, e_{(a,0)} ↦ s_a e_{(a,1)} and e_{(a,1)} ↦ −s_a e_{(a,0)};
  - y_ε: pair swap, e_{(0,s)} ↦ ε e_{(1,s)} and e_{(1,s)} ↦ −ε e_{(0,s)}.
- *Pair maps.* For a split pair π = (x, y) and g mapping {x, y} onto a split pair π′ = (x′, y′), write μ_{g,π} for the signed 2×2 permutation matrix of g in these orders. It is a *rotation* if det = +1, i.e. ±id or ±J₊ with J₊ = (x ↦ y′, y ↦ −x′), and a *reflection* otherwise.

**1.4 Partial quadrupling and the two refinement conventions.** Let E ⊂ F^X and σ be given, with placements T¹_β and T²_B ([EQ] Def 1.8, Thm 3.3).
- *Step 1.* A new block β* sits beside each β (x ↦ x*), with T¹_β in the labels of β. The pair Hadamard map (u, v) ↦ (u + v, u − v) is applied on (x, x*).
- *Step-one blocks.* B_{β,a} = (x, x*, y, y*) for π_a(β) = (x, y). These are exactly the labels (b, s) ↦ (β, (a, b), s) of [Lean]'s `r₁`.
- *Step 2.* Same, on each step-one block B, with T²_B and z ↦ z**.
- Q_σ(E) has length |X| + 12|σ|.
- *Refinement* of a set 𝓑 of step-one blocks. Let B = (x, x*, y, y*) ∈ 𝓑.
  - **Transposed split** (used by every `mainq_*` script via `choose_splits`; [EQ] Lemma 4.11). The new blocks are
        N_{B,0} = (x, y, y**, x**),   N_{B,1} = (x*, y*, (y*)**, (x*)**),
    with split pairs (x, y), (y**, x**) and (x*, y*), ((y*)**, (x*)**). The second pair is written reversed; this only matters for Lemma 2.7.
  - **Canonical split** ([Lean] `refd`/`r₂`; the reading in [MQ] §4 "Conventions"). The new blocks are (x, x**, x*, (x*)**) and the same with y.
- σ″ = {N_{B,s} : B ∈ 𝓑, s = 0, 1}. The singletons of Q_σ(E) are S together with all coordinates of the unrefined step-one blocks and their ** partners.

**1.5 Group data.**
- G ⊂ Aut(E) ⊂ Mon(X) is *σ-compatible* if it permutes the blocks of σ as sets and maps split pairs onto split pairs. G_β and G_π denote the setwise stabilisers.
- **Condition (★):** for every split pair π = {x, y}, every g ∈ G_π acts on π as ±id or as a signed swap with square −1 (g e_x = ε e_y, g e_y = −ε e_x).
- ĝ is the extension to the new coordinates: z* follows z with the same sign ([EQ] Def 4.2).

**1.6 Twined counts.** Let h ∈ Mon(X) have order 3 and no fixed coordinate, and first make it a permutation by a diagonal sign change (Lemma 2.6). Let σ be a union of ⟨h⟩-orbits of blocks. Choose a representative r(o) of each singleton orbit o and a representative block β_O of each block orbit O. Then
      T_h(E) := Σ_{c∈E^h} f(c),   R^h_σ(E) := Σ_{c∈E^h} ∏_{o∈S/h} φ(c_{r(o)}) ∏_{O∈σ/h} λ(|supp c ∩ β_O|).
- A fixed c is constant on orbits, so nothing depends on the representatives. T_h = R^h_∅, since φ³ = φ.
- In the collapsed form of [MQ] Lemma 4.3 and [EQ] Cor 5.6, R^h_σ(E) = R_σ̄(D) with D the collapsed fixed code.
- GJF Thm 5.6 condition 2 ("fixes the same number of even and odd maximal codewords") is T_h = 0, computed for the signed h or after normalisation, which differ by a sign.
- **Not** the same thing: Σ_{c∈E^h} (R_σ-weight of c), which counts λ³ per block orbit. [V: Part 4] finds it differs from R^h in 13 of 24 random cases; see also [EQ] Rem 5.8.

**1.7 The code-level target.** MQcode(k): there is a self-dual C of length 12k with Index(C) = 24 and, with m = gcd(k, 24):
- m ∈ {1, 2}: nothing more (g = ±1 always lies in Aut(C));
- m = 4: J ∈ Aut(C) with J² = −1;
- m ∈ {3, 6, 12}: g ∈ Aut(C) with g^m = 1, g^{m/2} = −1 if m is even, and h := g^{m/3} of order 3 with no fixed coordinate (cycle shape 3^{4k}) and T_h(C) = 0;
- m = 8: J, K ∈ Aut(C) with J² = K² = −1 and JK = −KJ;
- m = 24: J, K, h ∈ Aut(C) with these Q₈ relations, h³ = 1, hJ = Jh, hK = Kh, h without fixed coordinate, and T_h(C) = 0.

These are the hypotheses of GJF Thm 5.6 [T] (cyclic cases) and of [OI] Theorem O together with [MQ] Thm 8.1 (Q₈, Q₈×ℤ/3). The step from MQcode(k) to an SVOA of index 24/m is the VOA side, which is not in Mathlib and enters a formalization as a hypothesis (§5).

--------------------------------------------------------------------------------------------

## 2. Lemmas used by all chains

**Lemma 2.1 (placements) [P; V: Part 1; cf. EQ Lemma 1.5, Prop 4.9–4.10].**
- (a) There are 8 placements. Each of the 12 signed double transpositions x with x² = −1 fixes exactly 4. Each of the 8 regular Q₈-actions on a 4-block fixes exactly 4. For [MQ] §9's Morita Q₈ (left multiplication) these are class ℬ.
- (b) T_L is invariant under x_{s,−s} and y_ε (all signs), and not under x_{s,s}. Every class-𝒜 placement behaves like T_L; class ℬ behaves the opposite way on x and y.
- (c) Lemma A (Σ_{t∈T_L} φ⁸(dbl(u,t)) = λ(wt u)) holds for all 81 u. Lemma B, with λλ on the refined halves, holds for all 81 u and for **each** of the 3 pair-splittings.

*Proof of (b) by hand.*
- x_{1,−1} sends 1110 ↦ 2102 = 2·1110 + 2·0121 and 0121 ↦ 2011 = 2·1110 + 0121.
- y₁ sends 1110 ↦ 2011 and 0121 ↦ 1201 = 1110 + 0121.
- x_{1,1} sends 1110 ↦ 2101. This is not in T_L: its words are (a, a+b, a+2b, b), and a = 2, b = 1 gives 2011.
- Negation fixes every placement, so the other signs follow.
- (a) and (c) are finite checks. □

**Lemma 2.2 (one chain step) [P, given EQ Thm 3.3 and Lemmas 4.3–4.8; V: Part 3].** Let E ⊂ F^X be self-dual, and G ⊂ Aut(E) σ-compatible with (★) and with G-equivariant placements. Let 𝓑 be a union of G-orbits of step-one blocks, refined with the transposed split. Then:
- (a) Q := Q_σ(E) is self-dual of length |X| + 12|σ|, with Index(Q) = R_σ(E) and R_{σ″}(Q) = R_σ(E).
- (b) g ↦ ĝ is an injective homomorphism G → Aut(Q). Relations, orders and signed cycle data are inherited: each new coordinate lies in a cycle of the same length and sign product as its partner. No new fixed coordinates appear.
- (c) σ″ is Ĝ-compatible and satisfies (★). G_{N_{B,s}} = G_π with π = B ∩ X the old pair, acting on both pairs of N_{B,s} as on π.
- (d) |σ″| = 2|𝓑|. For 𝓑 a single G-orbit, |𝓑| = [G : G_π].
- (e) An h ∈ G of order 3 without fixed coordinate acts freely on σ″.

*Proof.*
- (a) is [EQ] Thm 3.3, which holds for any placements, any splits and any refined set.
- (b) is [EQ] Lemma 4.3 and Lemma 4.7.
- (c):
  - B ∈ 𝓑 is determined by the old pair π = B ∩ X, and N_{B,s} by (π, s).
  - ĝ maps old coordinates to old ones, *-copies to *-copies and **-copies to **-copies, so ĝN_{B,s} = N_{gB,s}. Hence Ĝ permutes σ″ and G_{N_{B,s}} = G_π.
  - The split pairs of N_{B,s} are π^{(s)} and its **-copy. g ∈ G_π maps each to itself, with the same local action as on π, since new coordinates follow their partners with the same sign.
  - So (★) for π gives (★) for both pairs.
- (d) Orbit–stabiliser, since B ↦ π is injective.
- (e) An h-stable 4-set would carry a permutation of order 3 of 4 points, which has a fixed point. □

Equivariant placements exist at the next step. N_{B,s} and the new step-one blocks have stabiliser G_π, which acts by ±1 or by a swap of square −1. Lemma 2.1(a) then gives invariant placements, and they are transported along orbits ([EQ] Lemma 4.6).

With the canonical split instead, G_{N} = {g : g e_x = ±e_x} = {±1} for the chains here. The next orbit of step-one blocks is then twice as large, and so is the k-increment (§7 issue 2).

**Lemma 2.3 (orbit-weighted twined count) [P; V: Part 4].** Keep the setting of Lemma 2.2, except that E may be any linear code (self-duality is not used). Suppose h ∈ G has order 3 and acts on X as a permutation without fixed coordinates, σ is a union of ⟨h⟩-orbits, and 𝓑 is h-stable. Then
      **T_h(Q_σ(E)) = R^h_σ(E)   and   R^h_{σ″}(Q_σ(E)) = R^h_σ(E).**

*Proof.*
- Φ(e, t¹, t²) := H₂(H₁(e, t¹), t²) is a linear bijection E ⊕ T¹ ⊕ T² → Q, where T¹ = ⊕_β T¹_β and T² = ⊕_B T²_B ([EQ] Thm 3.3).
- It is ĥ-equivariant ([EQ] Lemma 4.4). So Q^ĥ = Φ(E^h ⊕ (T¹)^ĥ ⊕ (T²)^ĥ).
- ĥ permutes the blocks of σ in 3-cycles (Lemma 2.2(e)), and ĥT¹_β = T¹_{hβ}. Hence (T¹)^ĥ = {(t_β) : t_{hβ} = ĥt_β} ≅ ∏_{O∈σ/h} T¹_{β_O}: t_{β_O} is free, and h³ = 1 makes the transport consistent. The same holds for T² over the step-one blocks.
- ĥ is a permutation of X̂, so v ∈ Q^ĥ is constant on its 3-element orbits. Grouping f(v) = ∏_{z∈X̂} φ(v_z) by orbits gives factors φ(·)³ = φ(·). So f(v) is the product over singleton orbits of X of φ(e_{r(o)}), times the product over block orbits O of the φ⁸-weights on the 16 new-and-old coordinates of β_O.
- Summing over t² ∈ T²_B for the two step-one blocks B of β_O gives λ(wt u_B), by Lemma A with u = H₁(e, t¹). Summing over t¹ ∈ T¹_{β_O} then gives λ(|supp e ∩ β_O|), by Lemma B for the split of β_O.
- This proves the first identity. The second is the same computation, with the weight λλ on N_{B,0} and N_{B,1} for B ∈ 𝓑. These new blocks form ĥ-orbits {N_{B,s}, N_{hB,s}, N_{h²B,s}}, and Lemma B for the transposed split gives λ(wt u_B) again. □
- Consequence: along an h-equivariant chain, T_h(E_j) = R^h_{σ₀}(E₀) for every j ≥ 1. This uses no collapsed code, only the fixed subspace and one weight per orbit.
- [V: Part 4] 24 random h-invariant self-dual codes of length 36 (h = twelve 3-cycles), σ = 1 or 2 orbits of blocks, one step with `mainq_equivariant.quad_eq`. Both identities hold in 24/24 cases, 12 of them nonzero (values 48, −24, 36, −96, …).

**Lemma 2.4 (the fixed code of a self-dual code) [P; V: Part 2].** Let E be self-dual and h ∈ Aut(E) of order 3 without fixed coordinate. Let the orbits be o = (i, hi, h²i), and write h e_j = s_j e_{hj}.
- Define π(c)_o := c_i + s_i c_{hi} + s_i s_{hi} c_{h²i}.
- Define the expansion x̄ ↦ x by x_i = x̄_o, x_{hi} = s_i x̄_o, x_{h²i} = s_i s_{hi} x̄_o.

Then the expansion is a bijection from π(E)^⊥ ⊂ F^{X/h} onto E^h. In particular dim E^h = |X|/3 − rank π(E).

*Proof.*
- The expansion is injective, and its image is exactly the set of h-fixed vectors of F^X.
- For such x and any c, ⟨x, c⟩ = Σ_o x̄_o π(c)_o = ⟨x̄, π(c)⟩.
- So x ∈ E^h ⟺ x ⊥ E (self-duality) ⟺ x̄ ⊥ π(E). □

*Certificate.* The rows of π(E), computed from a generator matrix, and their rank. Then E^h is explicit and small: dimension 6 for the ℤ/12 seeds and 12 for the Q₈×ℤ/3 seed.

**Lemma 2.5 (information sets) [P; V: Part 2].** Let I be an information set of E, i.e. restriction E → F^I is bijective, with inverse `enc`. Let K ⊂ F^I be the set of a such that:
- a_i ≠ 0 for i ∈ I ∩ S;
- for every block β, a|_{β∩I} extends to a vector of weight 1 or 4 on β. For |β ∩ I| = 4 this means weight ∈ {1, 4}; otherwise it means a|_{β∩I} is nowhere zero or has weight ≤ 1.

Then R_σ(E) = Σ_{a∈K} w_σ(enc a), and
      |K| = 2^{|I∩S|} ∏_{β∈σ} N(|β∩I|),   N(0..4) = (1, 3, 9, 15, 24).

*Proof.* w_σ(c) ≠ 0 forces c_i ≠ 0 on S and block weights in {1, 4}, so c|_I ∈ K. Restriction is injective on E. □

- For the Index (σ = ∅) this gives 2^{dim E}.
- Choosing I to contain whole blocks pays off: N(4) = 24 < 3⁴.

**Lemma 2.6 (signs) [P; = EQ Rem 4.13, Lemma 5.3].** Let d be diagonal. Then E ↦ dE, G ↦ dGd⁻¹ preserves self-duality, relations, cycle types and the local types.
- It multiplies Index, R_σ, T_h and R^h by the constant ∏_{i∈S} d_i, or ∏_i d_i for f.
- One use: make h a permutation. Each 3-cycle of h has sign product +1, since h³ = 1.
- The other use: turn R = −24 into +24 by flipping one singleton.

**Lemma 2.7 (keeping the Lean placement T_L) [P; V: Part 3].** Suppose that at stage 0:
- (i) every pair map μ_{g,π} (g ∈ G, π a split pair) is a rotation;
- (ii) every block map μ_{g,β} (g ∈ G, β ∈ σ₀) lies in Mon(T_L).

Use the transposed split with σ″-blocks ordered (x, y, y**, x**). Then at every later stage, every block map and every step-one-block map, in `r₁` labels, lies in Mon(T_L). So "T_L on every block" is a G-equivariant placement family, and [Lean]'s `Tfin` can be kept.

*Proof.* Induction on the stage.
- *Step-one blocks.* The map of B = (x, x*, y, y*) is (b, s) ↦ (r(b), s), where r = μ_{g,π} is a rotation. For r = ±id this is ±id. For r = ±J₊ it is y_{±1}. Both lie in Mon(T_L) (Lemma 2.1(b)).
- *New blocks.* On (x, y, y**, x**) the map is (r, R r R⁻¹) with R the order reversal. Since R r R⁻¹ = r⁻¹ for a rotation, the map is ±(id, id) or (±J₊, ∓J₊) = x_{±1,∓1}, both in Mon(T_L).
- The new pair maps r and r⁻¹ are again rotations, so (i) holds at the next stage. □

Remarks on the hypotheses:
- (i) is necessary: for a reflection r the step-one map (b, s) ↦ (r(b), s) is diagonal ≠ ±1 or an involutive double transposition, and neither preserves any placement ([EQ] Prop 4.9(e)). If (★) holds, (i) can always be arranged. Stabilisers act on pairs by rotations, so orient one pair per orbit and transport. This fixes each pair orbit's orientations up to reversing the whole orbit; reversing a single pair turns rotations into reflections.
- The elements of Mon(T_L) that preserve the split {π₀, π₁} form a group of order 16 [V: Part 1]. In the other 8, both pair maps are reflections. The 8 whose two pair maps are rotations are exactly:
  - (r, r⁻¹) with r ∈ {±1, ±J₊}, keeping the pairs;
  - (r, −r⁻¹), swapping them (y_ε is the case r = ±1).
- So (ii) says: along every step of an orbit, the two pair maps of a block are mutually inverse (up to the sign −1 when the pairs are swapped).
- For the ℤ/12 systems, a J-pair {6c + i, 6c + i + 3} has *offset* i ∈ {0, 1, 2}. Both g and h raise every offset by 1 mod 3. The 6-cycle "wraps" (g e_{6c+5} = −e_{6c}) at the step where the offset is 2: there the pair map is ±J₊, elsewhere it is id.
- A block whose two pairs have equal offsets wraps in both pairs at once, so its maps are (id, id) or (J₊, J₊⁻¹) up to orientation, and (ii) holds.
- With unequal offsets (σ_B: offsets 0 and 1) some step of the orbit has pair maps (id, ±J₊). Reversing a whole pair orbit replaces ±J₊ by its inverse and keeps id. So that step is of neither form, whichever orderings are chosen, and **no ordering of σ_B satisfies (i) and (ii)**. [V: Part 3] confirms: the orbit-wise search satisfies (ii) at stage 0, and then fails on the step-one blocks.

--------------------------------------------------------------------------------------------

## 3. The chains

### 3.1 m ∈ {1, 2} (Cor 2.1 of [MQ]) [P, given T: GJF Thm 5.6; Lean]

- *Codes.* [I Thm 5.9] = [Lean] `GJF.Ex.exists_selfDual_index24`: a self-dual C_k of length 12k with Index = +24 for every k ≥ 1.
- *Group.* g = 1 (m = 1) or g = −1 (m = 2). −1 ∈ Aut(C) for every linear C, and condition 2 of GJF Thm 5.6 is empty.
- *Certificates.* None beyond [Lean]: `index_golay`, `R_golay₁` and `R_golay₂`, each a kernel `decide` over 729 codewords.
- MQcode(k) for m ∈ {1, 2} is already formalizable from [Lean] in a few lines.

### 3.2 The J-chain (m = 4; [MQ] Thm 4.2) [P, given EQ; V]

**Seed.** E₀ = Golay (`golayRow` of [Lean] = `existence_common.GOLAY` = GJF Ex 1.5), with
      J = (0 1)(2 3)…(10 11), signs: J e₀ = −e₁, J e₁ = e₀, J e₂ = −e₃, J e₃ = e₂, J e₄ = e₅, J e₅ = −e₄, J e₆ = −e₇, J e₇ = e₆, J e₈ = e₉, J e₉ = −e₈, J e₁₀ = −e₁₁, J e₁₁ = e₁₀.
- This is `mainq_jchain.J`, one of the 792 such elements of Aut(Golay).
- G = ⟨J⟩ ≅ ℤ/4, J² = −1, cycle shape 2⁶.
- σ₀ = {β = (0, 1 | 2, 3)}, split into the J-stable pairs {0,1} and {2,3}. G_β = G.

**Inductive statement (Proposition 3.2).** For j ≥ 0 let 𝒮_J(24 + 24j) be the statement: there is a self-dual E_j of length m_j = 24 + 24j with J_j ∈ Aut(E_j), J_j² = −1, J_j fixed-point-free on coordinates (all cycles 2-cycles), and a J_j-compatible system σ_j of 2 blocks satisfying (★), each block J_j-stable, with R_{σ_j}(E_j) = 24 and Index(E_j) = 24. Then:
- *Base.* Q_β(Golay) has length 24 and two step-one blocks. Refine the one through the pair {0, 1}; its J-orbit has size 1 since G_{\{0,1\}} = G. This gives 𝒮_J(24), with σ₀″ = {(0, 1, 18, 16), (12, 13, 19, 17)} in the numbering of `quad_eq`.
- *Step.* 𝒮_J(m) ⟹ 𝒮_J(m + 24). Take E′ = Q_σ(E), and refine one step-one block; each is J-stable, so its orbit has size 1. By Lemma 2.2, b stays 2 and R = Index = 24.
- So for every even k there is C with Index 24 and J² = −1 (MQcode(k) for m = 4 whenever k ≡ 4, 20 mod 24).

**Seed certificates** [V: Part 2]:

| # | fact | size | Lean route |
|---|---|---|---|
| J1 | J ∈ Aut(Golay) | 6 membership tests (systematic form) | `decide` |
| J2 | J² = −1 | 12 coordinates | `decide` |
| J3 | σ₀ J-compatible, (★) | G of order 4 | `decide` |
| J4 | placements: T_L-compatible ordering (0, 1 \| 3, 2) (Lemma 2.7(ii)) | 4 of the 8 orderings work | `decide` |
| J5 | R_β(Golay) = 24 | 729 codewords | [Lean] `R_golay₁` with c₁ = (0,1\|2,3). R ignores orderings, so reuse it through a relabelling lemma |

Note: `Tfin` is **not** J-invariant in the ordering (0, 1, 2, 3), since J acts there as x_{−1,−1} ([EQ] issue 4). The reordered block (0, 1, 3, 2) fixes this (J acts as x_{−1,+1}).

### 3.3 The ℤ/12-chains (m ∈ {3, 6, 12}; [MQ] Thm 4.4) [P, given EQ and T: GJF Thm 5.6; V]

**Group.** On 36 coordinates, g = six signed 6-cycles, e_{6c+i} ↦ e_{6c+i+1} (i < 5) and e_{6c+5} ↦ −e_{6c} (`signed_cycles(36, 6)`).
- g¹² = 1 and g⁶ = −1.
- J := g³ has J e_{6c+i} = e_{6c+i+3} (i < 3) and J e_{6c+i} = −e_{6c+i−3} (i ≥ 3). The J-pairs are {6c+i, 6c+i+3} with offset i < 3.
- h := g⁴ has the orbits {6c, 6c+4, 6c+2} and {6c+1, 6c+5, 6c+3}. It carries 24 sign changes, so Lemma 2.6 normalises it for Lemma 2.3.

**Seeds and systems** [V: Part 2; `mainq_seed_search.py`, `mainq_z12chain.py`]. Blocks are two J-pairs from different 6-cycles. Each system is a union of ⟨g⟩-orbits of 3 blocks, and G_β = ⟨J⟩.

| seed | Index | system | blocks | R_σ | R^h_σ = R_σ̄(D) | offsets matched (Lemma 2.7) |
|---|---|---|---|---|---|---|
| `z12seed_len36_3` | +24 | σ_A (b = 3) | (24,27\|30,33), (28,25\|34,31), (26,29\|32,35) | −24 | 0 | yes |
| same | | σ_B (b = 6) | (0,3\|7,10), (4,1\|11,8), (2,5\|9,6), (12,15\|25,28), (16,13\|29,26), (14,17\|27,24) | −24 | 0 | **no** (0 vs 1) |
| `z12seed_len36_6` | −24 | σ_A6 (b = 3) | (0,3\|12,15), (4,1\|16,13), (2,5\|14,17) | **+24** | 0 | yes |
| same | | σ_B6 (b = 6) | (0,3\|30,33), (4,1\|34,31), (2,5\|32,35), (6,9\|12,15), (10,7\|16,13), (8,11\|14,17) | **+24** | 0 | yes |

- For both seeds, T_h(E) = 0, rank π(E) = 6 and D = π(E)^⊥ has dimension 6 and length 12 (Lemma 2.4).
- *How σ_A6, σ_B6 were found* [V: Part 7].
  - There are 15 offset-matched 3-block systems and 45 offset-matched 6-block systems (out of 45 and 405).
  - Over the 8 committed seeds, the matched systems with R^h = 0 and |R_σ| = 24 are:
    - b = 3: seed 3 (σ_A), seed 4 (2), seed 6 (σ_A6);
    - b = 6: seed 2, seed 5, seed 6 (σ_B6).
  - Seed 6 is the only seed with both.

**Inductive statement (Proposition 3.3).** 𝒮_ℤ₁₂(m, b) is the statement: there are a self-dual E of length m, g ∈ Aut(E) with g⁶ = −1 and all coordinate cycles of length 6, and a g-compatible system σ of b blocks with (★) on which h acts freely, such that R_σ(E) = ε·24 and R^h_σ(E) = 0. Then:
- *Step.* 𝒮(m, b) ⟹ C := Q_σ(E) has length m + 12b, Index(C) = ε·24 and T_h(C) = 0 (Lemma 2.3), with g extended. And 𝒮(m + 12b, 6) holds: refine one ⟨g⟩-orbit of step-one blocks, which has |G|/|⟨J⟩| = 3 elements, into 6 blocks (Lemma 2.2).
- *Chain A:* 𝒮(36, 3) → codes at k = 6, 12, 18, … (lengths 72j).
- *Chain B:* 𝒮(36, 6) → codes at k = 9, 15, 21, … (lengths 36 + 72j).
- *k = 3:* the seed itself (Index ±24, T_h = 0).
- *GJF Thm 5.6 with x = g^{12/m}* (the element of order m):
  - m = 3: x = h, cycle shape 3^{4k}, T_h = 0;
  - m = 6: x = g², with x³ = −1 and x² = h;
  - m = 12: x = g, with g⁶ = −1 and g⁴ = h.
  - For m ∈ {6, 12} every cycle of x has length m/2 and an odd number of sign changes (Frame shape (m/2)^{−24k/m} m^{24k/m}), which GJF's anomaly proof uses. For m = 3 the Frame shape of h is 3^{4k}.
- *Signs.* With seed 3, ε = −1 (flip one singleton, Lemma 2.6). With seed 6's systems, ε = +1.
- *Coverage.* Chain A covers k ≡ 6, 12, 18 mod 24 (from k = 6). Chain B plus the seed covers k ≡ 3, 9, 15, 21 mod 24 [V: Part 3, k ≤ 100].

**Seed certificates** (seed 3 or seed 6; sizes are the same) [V: Part 2]:

| # | fact | size | Lean route |
|---|---|---|---|
| Z1 | E self-dual (18 × 36, rows orthogonal, systematic) | 171 dot products | `decide` / checker |
| Z2 | g ∈ Aut(E) | 18 membership tests | `decide` / checker |
| Z3 | g⁶ = −1, g¹² = 1; h without fixed coordinate | 36 coordinates | `decide` |
| Z4 | σ_A, σ_B g-compatible, (★), h free on blocks, placements (Lemma 2.7 orderings for σ_A, σ_A6, σ_B6) | \|G\| = 12 | `decide` |
| Z5 | R_{σ_A}(E) = ε24 | **262,144** candidates (I = 18 singletons) | verified bit-sliced checker |
| Z6 | R_{σ_B}(E) = ε24 | **589,824** candidates (I = 10 singletons + 2 whole blocks: 2¹⁰·24²) | verified bit-sliced checker |
| Z7 | rank π(E) = 6; R^h_{σ_A}(E) = R^h_{σ_B}(E) = 0 | 729 fixed codewords each | `decide` |
| Z8 | (k = 3 only) Index(E) = ±24; T_h(E) = 0 | 262,144; 729 | checker; `decide` |

- A plain enumeration of E would need 3¹⁸ ≈ 3.9·10⁸ codewords.
- [EQ] §6 gives 2¹²·3⁶ ≈ 3·10⁶ for σ_B. Whole blocks in I lower this 5-fold (Lemma 2.5).
- *Smaller alternative for k = 3.* GJF's own length-36 example (`gjf_ex57_len36`, shift h) needs the same 2¹⁸ index computation.

### 3.4 The Q₈-chain (m = 8; [MQ] Cor 8.2) [P, given EQ, Thm 8.1 and [OI]; V]

**Seed.** E₀ = `q8chain_len24.txt` (12 × 24), found by `mainq_q8chain.py`, random seed 7.
- On each group of 4 coordinates, J = (0 1)(2 3) with signs (+, −, +, −) and K = (0 2)(1 3) with signs (+, −, −, +). These are `mainq_q8chain.q8(24)` and coincide with [MQ] §9's Morita generators on one block.
- J² = K² = −1 and JK = −KJ; |G| = 8.
- σ₀ = {(9, 8 | 11, 10), (13, 12 | 15, 14)}: coordinate groups 2 and 3 (Q₈-orbits), split into J-pairs. G_β = Q₈, and K swaps the two pairs.

**Inductive statement (Proposition 3.4).** 𝒮_Q(m, b) is the statement: there are a self-dual E of length m, J, K ∈ Aut(E) with the Q₈ relations, and a Q₈-compatible σ of b blocks with (★), such that R_σ(E) = 24. Then:
- *Step.* 𝒮_Q(m, b) ⟹ C = Q_σ(E) has length m + 12b, Index 24 and Q₈ ⊂ Aut(C). And 𝒮_Q(m + 12b, 4) holds: the stabiliser of a J-pair is ⟨J⟩, so an orbit of step-one blocks has 2 elements, giving 4 blocks.
- 𝒮_Q(24, 2) → k = 4; then 𝒮_Q(48, 4) → k = 8, 12, 16, …, all k ≡ 0 mod 4.
- For 8 | k, Q₈ is non-anomalous ([MQ] Thm 8.1) and V//Q₈ has index 3 ([OI] Theorem O).

**Seed certificates** [V: Part 2]:

| # | fact | size | Lean route |
|---|---|---|---|
| Q1 | E self-dual | 12 × 24 | `decide` |
| Q2 | J, K ∈ Aut(E); relations | 24 membership tests; 4 coordinates | `decide` |
| Q3 | σ₀ Q₈-compatible, (★); T_L-compatible orderings (9,8\|10,11), (13,12\|14,15) | \|G\| = 8 | `decide` |
| Q4 | R_σ(E) = 24 | **4,096** candidates (I = 12 of the 16 singletons); plain 3¹² = 531,441 | `decide` over a Finset of 4,096 candidates (Lemma 2.5): ≈ minutes [H] |

### 3.5 The Q₈×ℤ/3-chain (m = 24; [MQ] Thm 10.1) [P, given EQ, Thm 8.1, [OI] and GJF's ℤ/3 anomaly; V]

**Seed.** U = `q8z3_seed72.U.txt` (18 × 36) is a Lagrangian for Ω = ⊕_b ω_b in F₃^{36}; block b = coordinates 2b, 2b+1, with r = 18 blocks.
- U is h-invariant and free over F₃[u]/u³ (dim U^h = 6).
- E₀ = F₃² ⊗ U = `q8z3_seed72.txt` (36 × 72) in quaternion coordinates; the stored file equals `code_from_U(U)`.
- J, K are left multiplication by i, j on each Q₈-orbit 4b..4b+3 (J = (0 1)(2 3) with signs (+,−,+,−), K = (0 2)(1 3) with signs (+,−,−,+)).
- h permutes blocks, 3s + t ↦ 3s + (t + 1 mod 3). It is a pure permutation, so no normalisation is needed.
- σ₀ = the orbit blocks 0..5 (h-triples 0 and 1), split into J-pairs.

**Inductive statement (Proposition 3.5).** 𝒮_{Q×3}(m, b) is 𝒮_Q(m, b) together with: h ∈ Aut(E) a permutation of order 3 without fixed coordinate, commuting with J and K, acting freely on σ, and R^h_σ(E) = 0. Then:
- *Step.* 𝒮_{Q×3}(m, b) ⟹ C = Q_σ(E) has length m + 12b, Index 24, G = Q₈×⟨h⟩ ⊂ Aut(C) and T_h(C) = 0 (Lemma 2.3). And 𝒮_{Q×3}(m + 12b, 12) holds: an orbit of step-one blocks has |G|/|⟨J⟩| = 6 elements, giving 12 blocks.
- 𝒮_{Q×3}(72, 6) → k = 12; then 𝒮(144, 12) → k = 24, 36, …, all k ≡ 0 mod 12.
- For 24 | k, V//G has index 1 ([OI] Theorem O).

**Seed certificates** [V: Part 2, Part 6]:

| # | fact | size | Lean route |
|---|---|---|---|
| T1 | U Lagrangian (18 × 36) ⟹ E self-dual; or check E directly (36 × 72) | 171 Ω-products / 666 dot products | `decide` / checker |
| T2 | hU = U; dim U^h = 6 | 18 membership tests | `decide` |
| T3 | J, K, h ∈ Aut(E); relations; h without fixed coordinate | 108 membership tests on E, or automatic from Morita + T2 | checker |
| T4 | σ₀ G-compatible, (★); T_L-compatible orderings (4b, 4b+1 \| 4b+3, 4b+2) | \|G\| = 24 | `decide` |
| T5 | rank π(E) = 12, so D = π(E)^⊥ has dimension 12 and length 24; R^h_σ(E) = R_σ̄(D) = 0 with σ̄ = {0..3}, {4..7} | **4,096** candidates on D (plain 3¹² = 531,441) | `decide` over candidates |
| T6 | **R_σ(E) = 24** | Morita form ([MQ] Cor 9.2): **5,812,449** normalised SL₂-words. First rows x₁ run over an affine subspace of U of dimension r − 2 = 16 (3¹⁶ ≈ 4.3·10⁷ points, pruned) and x₂ solves an 18-variable linear system. Information sets: ≥ 2³⁶ ≈ 6.9·10¹⁰ | **not kernel-feasible** (§4) |

- The Morita formula: R_σ(F₃²⊗U) = 8 Σ_{Π} Σ_{s∈F₃} ∏_b ρ_b(ψ_b(Π) + s).
  - Π runs over the SL₂-orbits of SL₂-words, normalised by X_{b₀} = 1.
  - ψ: SL₂(F₃) → ℤ/3 is the abelianisation (`PSI_TAB`).
  - ρ = (−2, 1, 1) on σ and φ = (0, −1, 1) elsewhere.
- For a Lean checker this needs [MQ] Lemma 9.1 and Cor 9.2 formalised first (§5, item C9).
- Seed values not used by the chain: Index(E₀) = −1608 (sl2words; |Index| also by `ternary60 index`) and T_h(E₀) = 0.

### 3.6 Coverage (the code half of [MQ] Cor 10.2) [P; V: Part 3]

- Every k ≥ 1 falls into exactly one row of §0, and the chains above give MQcode(k).
  - m ∈ {1, 2}: every k (3.1).
  - m = 4: k ≡ 4, 20 mod 24 ⊂ even k (3.2).
  - m = 3: k ≡ 3, 9, 15, 21 mod 24 ⊂ {3} ∪ {9, 15, 21, …} (3.3, B).
  - m ∈ {6, 12}: k ≡ 6, 12, 18 mod 24 ⊂ {6, 12, 18, …} (3.3, A).
  - m = 8: k ≡ 8, 16 mod 24 ⊂ 4ℕ (3.4).
  - m = 24: k ≡ 0 mod 24 ⊂ 12ℕ (3.5).
- [V: Part 3] simulates all chains on block data only, for k ≤ 100. Nothing is missed with the transposed split. With [Lean]'s canonical split, k = 18, 21, 30, 33, 42, 45, … are missed.

--------------------------------------------------------------------------------------------

## 4. Certificates: sizes, methods, kernel feasibility

**Calibration [H].** The present [Lean] build takes ≈ 2 min. Most of it is three kernel `decide`s over the 729 Golay codewords, plus 2 × 81 × 9 local-identity cases. So `decide` on `Fin n → ZMod 3` functions costs roughly 10⁻² to 5·10⁻² s per codeword evaluation at length 12, and more at larger length.

A *verified checker* is a `Bool`-valued function on bit-sliced `Nat` data (two masks per vector), defined by structural recursion, with a soundness theorem, and evaluated by `decide`/`rfl`. The kernel accelerates `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftRight` and so on through GMP, so it pays 10²–10³ kernel steps per candidate rather than thousands of `ZMod` unfoldings. This is an estimate, not measured here; no Lean toolchain is installed in this container.

| certificate | enumeration | `decide` style | verified checker | smarter proof |
|---|---|---|---|---|
| J5, `R_golay₁` | 729 | done (≈ 30 s) | – | – |
| Z7, T5 (twined, on D) | 729; 4,096 | seconds; minutes | – | – |
| Q4 | 4,096 | minutes | seconds | – |
| Z5, Z8 | 262,144 | ≈ 3–10 h: no | minutes | g-orbits (size 12) only save a constant factor; not worth it |
| Z6 | 589,824 | no | minutes | – |
| T6 | 5.8·10⁶ planes × an 18-variable solve (Rust: 3 s) | no | ≈ 10⁹–10¹⁰ steps: no | none known |

Options for T6, the only obstacle to a fully kernel-checked code-level answer:
- (a) `native_decide` on a verified sl2words-type checker. This adds the axiom `Lean.ofReduceBool`, and the project currently excludes `native_decide`, so it needs the user's decision.
- (b) State T6 as an explicit hypothesis of the k ≡ 0 mod 24 theorem, and cross-check it by an independent second implementation (§7 issue 4; done: `rsigma_is`, +24).
- (a′) `native_decide` on the information-set sum instead (2³⁶ patterns): its soundness is only Lemma 2.5 (item C4), with no Morita form or Cor 9.2. It is simpler than (a), but slower to run [H].
- (c) Search for a seed with a cheap certificate. For example: a length-72 G-invariant seed whose σ-part and complement are glued along a small glue group ([I] Lemma 5.3), so that R_σ is a short sum of products [H]. Direct sums cannot work, since R is multiplicative (24·24 ≠ 24), and seeds at k = 3 are ruled out by the 72-rule ([MQ] §8.1).
- (d) The ⟨h⟩-symmetry of the good planes saves at most a factor 3.

--------------------------------------------------------------------------------------------

## 5. Lean plan for this component, and its size

**Status (2026-09-27, later): done** as planned below, in `lean/GJF/` (`ChainJ`, `ChainQ8`, `ChainZ12`, `ChainQ8Z3`, `Twined`, `Eval`, `SeedCert`, `TierA`), with R_σ(E₇₂) = 24 as the hypothesis `Q8Z3.E72Hyp`. Differences from the plan:
- The ℤ/12 seeds are normalised (Lemma 2.6) so that h = g⁴ is a pure permutation; with this normalisation every block map of g on σ_A6 and σ_B6 is `A 1` (orderings found by `ternary60/theory/lean_seed_data.py`, log `lean_seed_data_z12.log`). σ_B6 is labelled `Fin 3 × Fin 2` and is already a uniform chain state. For k = 3 the unnormalised seed 3 is used (T_h for the signed h).
- Fixed subcodes are certified by a sparse left inverse of the fixedness forms (`Eval.comp_of_cert`), not by Lemma 2.4.
- The seed sums use a verified bit-sliced tree with pruning at information coordinates (Lemma 2.5), split into chunks of ≤ 4,500 leaves per declaration because of kernel memory (§4).

**Encoding choices** (on top of [EQ] §7):
- *Refinement.* Add `refdᵗ` (split by the second label of the step-one block, i.e. {x, y} | {x*, y*}) and `localBᵗ`, a `decide` over 81 cases [V: Part 1, Lemma B for all 3 splits]. Add a regrouping `r₂ᵗ` sending new-block label (a′, b′) to the doubled step-one coordinate ((a′ ⊕ b′, s), a′). This is the order (x, y, y**, x**). Generalise `newState` from one refined block to a G-stable set 𝓑 ([EQ] §7 item 3).
- *Placements.* With Lemma 2.7, keep `Tfin` everywhere. The stage-0 orderings are data: J (0,1\|3,2); σ_A (24,27\|33,30), …; σ_A6, σ_B6; Q₈ (9,8\|10,11), (13,12\|14,15); Q₈×ℤ/3 (4b, 4b+1\|4b+3, 4b+2). This avoids [EQ]'s per-block placement generalisation `Dp`, provided chain B uses σ_B6 (seed 6). With seed 3's σ_B, `Dp` is needed.
- *Twined count.* Use R^h (Lemma 2.3) on the fixed subspace in the original coordinates. This is an alternative to [EQ]'s collapse into model coordinates `Blk (S̄ × Fin 3) (B̄ × Fin 3)`; either works. R^h needs only "(T¹)^ĥ ≅ ∏_{orbits} T¹_{β_O}" and the cube identity φ³ = φ.
- *Seeds.* Store generator matrices in systematic form, so that `enc` is injective by a symbolic lemma. `decide` over F₃^{18} would be infeasible, unlike [Lean]'s `enc_sys` for Golay. Membership is then `v = enc (v|_I)`.

**Size estimate for this component** (on top of [EQ] items 1–7, ≈ 1,200–1,900 lines):

| item | lines |
|---|---|
| C1 seed data as literals (seed 6 or 3: 18 × 36; Q₈: 12 × 24; E₇₂: 36 × 72 or U: 18 × 36), generators, stage-0 orderings | 150–250 |
| C2 systematic-form toolkit: \|C\| = 3^k, membership, self-duality from orthogonality plus cardinality (generalising [Lean]'s Golay section) | 120–200 |
| C3 per-seed small certificates: Aut, relations, compatibility, (★), T_L orderings (`decide`) | 150–250 |
| C4 Lemma 2.5 (information-set sums) as a `Finset` statement, with soundness | 120–200 |
| C5 bit-sliced evaluator and soundness, for Z5, Z6, Z8 | 300–500 |
| C6 Lemma 2.4 and the twined sums over D | 100–180 |
| C7 Lemma 2.3 (orbit-weighted), if used instead of [EQ]'s collapse (replaces its 200–300; not counted in the subtotal) | 150–250 |
| C8 five chain instantiations, MQcode(k) for every k, residue bookkeeping | 250–400 |
| **subtotal** | **≈ 1,200–2,000** |
| C9 (k ≡ 0 mod 24 only) Morita form ([MQ] Lemma 9.1), Cor 9.2, good-plane enumerator and its soundness | 800–1,200, plus `native_decide` or a hypothesis |

- **Code-level Main Question in total:** ≈ 2,400–3,900 lines with T6 as a hypothesis, ≈ 3,200–5,100 with C9. For comparison, [Lean] Existence.lean is 805 lines.
- **VOA side.** GJF Thm 3.1, 4.2 and 5.6, [OI] Theorem O and [MQ] Thm 8.1 cannot be stated in current Mathlib (no VOAs, orbifolds or anomalies). They enter as a single hypothesis "MQcode(k) ⟹ an N=1 SVOA of central charge 12k and index 24/m". Scaffolding for that statement: ≈ 100–200 lines. A real formalization of that side would be a separate project of a different order of magnitude.

--------------------------------------------------------------------------------------------

## 6. Data files [V: Part 5]

| file | content | written by |
|---|---|---|
| `ternary60/codes/z12seed_len36_{1..8}.txt` | seeds (18 × 36 generators) | `mainq_seed_search.py` (with `--write`) |
| `z12chain_len{72,108,144}.txt`, `.g.txt` | chain codes and g | `mainq_z12chain.py` |
| `jchain_len{24,…,144}.txt`, `.J.txt` | chain codes and J | `mainq_jchain.py` |
| `q8chain_len{24,48,96}.txt` | seed and chain codes (J, K implicit: `q8(n)`) | `mainq_q8chain.py` |
| `q8z3_seed72.U.txt`, `q8z3_seed72.txt` | U and E₀ = F₃² ⊗ U | `mainq_q8z3_seed72.py`, `mainq_q8z3_chain24.py` |
| `q8z3_chain_len{144,288}.txt`, `.gens.txt` | chain codes; J, K, h space-separated | `mainq_q8z3_chain24.py` |

The generator files `jchain_len<n>.J.txt` and `z12chain_len<n>.g.txt` hold two lines:
- the permutation p as concatenated decimal numbers with no separators;
- the signs as a string over {1, 2}, with 2 meaning −1. This line is unambiguous.

The first line is ambiguous for n > 10. [V: Part 5] counts every parse of it into a permutation of 0..n−1:
- `jchain_len<n>.J.txt`: 3, 18, 60, 136, 888, 888 parses for n = 24, 48, 72, 96, 120, 144;
- `z12chain_len<n>.g.txt`: 24, 120, 400 parses for n = 72, 108, 144.

- In every file exactly one parse satisfies the stated relation (J² = −1, resp. ord g = 12 and g⁶ = −1). That parse is an automorphism of the code, and it is the one the backtracking parser of `mainq_orbifold_index.py` returns first.
- So the data are recoverable, but only with the code at hand.
- A Lean development should take its generators from the seeds (§3), not from these files. *Done 2026-09-27:* `mainq_gens_files.py` writes unambiguous `jchain_len<n>.gens.txt` and `z12chain_len<n>.gens.txt` (exactly one valid parse per file, confirmed), and the chain scripts now write them directly.

--------------------------------------------------------------------------------------------

## 7. Issues found

*Status (2026-09-27): the items below are tracked, with what has been fixed since, in `README.md` §5.*

None of these breaks a result: the chain codes were built by `quad_eq`, which uses the transposed split and invariant placements. They concern the written statements and the path to Lean.

1. **The committed chain-B system σ_B cannot use a single fixed placement** (Lemma 2.7) [P; V: Part 3].
   - Its blocks pair J-pairs of offsets 0 and 1. By the remarks after Lemma 2.7, no ordering of its blocks makes all block and step-one maps lie in Mon(T_L).
   - So a Lean chain B from seed 3 needs per-block placements ([EQ]'s `Dp`).
   - Seed 6 has offset-matched systems σ_A6, σ_B6 with R = +24 and R^h = 0 (§3.3), for which `Tfin` suffices and no sign flip is needed. This is a formalization trap, not an error in [MQ].
2. **Refinement split.**
   - [MQ] §4's "Conventions" reads a refined block as (w, w**, x, x**) with pairs {w, w**}, {x, x**}. That is the canonical split, which is also [Lean]'s `refd`/`r₂`.
   - With it the ℤ/12 chains miss k ≡ 6, 9 mod 12 for k ≥ 18, i.e. part of gcd ∈ {3, 6} [V: Part 3; also EQ issue 2].
   - [MQ] Thm 4.4's "k grows by 6" holds only with the transposed split. The scripts do use it (`choose_splits` prefers stabiliser-fixed pairs).
   - The J-, Q₈- and Q₈×ℤ/3-chains still cover their target classes with either split.
3. **Ambiguous generator files** (§6). `jchain_len<n>.J.txt` and `z12chain_len<n>.g.txt` have up to 888 parses. Exactly one satisfies the relation and is an automorphism [V: Part 5].
4. **R_σ(E₇₂) = 24 rests on one program.**
   - [MQ] §10 cites three agreeing computations: sl2words with b₀ = 0, with b₀ = 9, and "the older enumeration". The last is the `SL2_SLOW` code path of the same `ternary60 sl2words` subcommand.
   - The Morita formula itself (Cor 9.2) was cross-checked against direct enumeration only at n ≤ 36.
   - Nothing independent checks the value that decides k ≡ 0 mod 24. Worth doing before publication (e.g. a separate implementation of Cor 9.2 in another language).
   - *Resolved 2026-09-27.* `ternary60/src/bin/rsigma_is.rs` (no code shared with src/main.rs) enumerates the definition of R_σ over an information set: 2³⁶ sign patterns, since all 36 information coordinates lie outside σ. It gives R_σ(E₇₂) = +24 and Index(E₇₂) = −1608, and agrees with sl2words on four more systems of E₇₂ and on random n = 36 codes (`mainq_e72_infoset.py`, log beside it). A third evaluator written by a reviewer, `rsigma_mitm`, agrees.
5. **Sign in [MQ] Thm 4.4.** Chains A and B from seed 3 have Index −24 (R_σA = R_σB = −24). GJF Thm 5.6 is stated for index 24, so one singleton must be re-signed (Lemma 2.6), as [MQ] Cor 2.1 says for its case; Thm 4.4 says "±24" without the remark. Seed 6's systems give +24 directly.
6. **Collapse with a signed h.** `mainq_z12chain.collapsed` and `mainq_seed_search` collapse the fixed code of the signed h = g⁴ to orbit representatives without normalising. So "T_h = R_σ̄(D)" holds there only up to a global sign (Lemma 2.4's expansion carries the signs). Harmless, since all values are 0; [EQ] Lemma 5.3 states the sign.
7. **Dangling reference.** `notes/orbifold-index.md` §4 cites `notes/lean-blueprint.md`, which does not exist (also [EQ] issue 5).
8. (Bookkeeping.) `ternary60/theory/blueprint_chains.py` has no row in README's layout yet; this task could not edit existing files.
