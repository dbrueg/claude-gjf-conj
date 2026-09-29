# The GJF Main Question: holomorphic N=1 SCFTs of minimal index from ternary codes

Working notes, started 2026-09-26. Companion to `notes/ternary-code-index.md` (cited as **[I]**; e.g. [I §5.1(f‴)] is the partial-quadrupling section). Status labels as there: [P] proved here, [V] exact computation (script cited), [T] cited theorem, [C] conjecture, [H] heuristic.

GJF = Gaiotto, Johnson-Freyd, *Holomorphic SCFTs with small index*, arXiv:1811.00589 (numbering of arXiv v1; `scripts/fetch_gjf_source.sh` downloads the TeX). Scripts live in `ternary60/theory/mainq_*.py` and write a `.log` beside themselves.

--------------------------------------------------------------------------------------------

## 0. Summary

- **GJF's Main Question** asks for a holomorphic N=1 VOA with c = 12k and index 24/gcd(k,24) for every k. GJF answer k ≤ 5, via Thm 5.6: orbifold the code VOA V_{Λ(C)} of an index-24 code C by an automorphism g of order m = gcd(k,24) with (1) g^{m/2} = −1 and (2) g^{m/3} a balanced fixed-point-free order-3 map (§1).
- **Answered here for every k** (§2, §4, §8, §10), modulo GJF Thm 5.6 [T, via T*: its orbifold step is the fermionic Thm 4.2], the fermionic GJF Thm 4.2 [T*] and [I Thm 5.9]; previously k ≤ 5.
  - [T*]: the super case of GJF Thm 4.2 (anomaly in S̃H³, trivialisation ⇒ holomorphic orbifold with W_R = ⊕ V_{R,g}^{C(g)}) is only sketched in GJF. What is used is isolated as Hypothesis ORB in `notes/blueprint/orbifold-foundations.md` (§5); the index computation for all groups used is `notes/orbifold-index.md` (Theorem O). The Lean blueprint is `notes/blueprint/README.md`.
  - gcd(k,24) ∈ {1, 2}: any index-24 code from [I], with g = 1 or g = −1 (Cor 2.1).
  - gcd(k,24) = 4: a J-equivariant version of [I]'s construction, seeded by J ∈ Aut(Golay) with J² = −1 (Thm 4.2).
  - gcd(k,24) ∈ {3, 6, 12}: a ℤ/12-equivariant version, seeded by one length-36 code found by GJF's search method; the twined count of the order-3 part is carried along by Lemma 4.3 (Thm 4.4).
- **Our [I Thm 5.9] codes as they stand** (§3): the length-48 code satisfies Thm 5.6 (it has J with J² = −1); the lengths-36 and 72 codes do not (their automorphism groups are 2-groups). So the symmetry has to be built in, which §4 does.
- **Obstruction** (§5): if g ∈ Aut(C) has g⁴ = −1 then 48 | Index(C). So Thm 5.6 can never be applied when 8 | k (m ∈ {8, 24}). The proof uses a new Hermitian four-code identity (◇). The quaternion group Q₈ escapes the obstruction and would give index 3 if its action is non-anomalous [C].
- **Q₈ anomaly** (§8): for Q₈ ⊂ Aut(C) with centre −1 the anomaly is 3k·a with a of order 8 (reduction to free fermions in the regular representation; eta invariants on S³/Q₈ give 5/8). So Q₈ is non-anomalous iff 8 | k, and the Q₈-chain codes answer the Main Question for **k ≡ 8, 16 mod 24** (index 3).
- **k ≡ 0 mod 24 (index 1)** (§9, §10): answered with G = Q₈ × ℤ/3, which is non-anomalous there.
  - At length 36, T_h = 0 forces 72 | Index (the "72-rule", §8.1), which blocks chains seeded at k = 3. **The rule is false at length 72** (§9).
  - A length-72 seed with R_σ = 24 and R_σ̄(D) = 0, found by a targeted search, gives a G-equivariant chain with Index 24 and T_h = 0 at every k ≡ 0 mod 12, k ≥ 12. So V//G has index 1 for k ≡ 0 mod 24 (Thm 10.1).
  - **So the Main Question has a positive answer for every k** (Cor 10.2), modulo the cited results and caveats.
  - An independent check of GJF's anomaly analysis is not attempted here.
- **The coprime-gauging step of Thm 8.1 is checked** (§8.2): it is correct.
  - Its only non-elementary input is the standard coprime-gauging lemma (Naidu, Uribe; Tachikawa; Johnson-Freyd). That lemma is a theorem for fusion categories and follows from known results for bosonic VOAs with solvable group. It reaches the super case through the bosonic shadow.
  - One gap is closed: the 3-primary part of the anomaly of Ŵ ⋊ Q₈ vanishes.
  - GJF's cyclic formula, applied directly to V_{Λ(C)}, confirms Thm 8.1 on all cyclic subgroups (`mainq_q8_gauging.py`). The order-2 part 4a is invisible there.
- **The (−1)-twisted sector, computed directly** (§8.3, `mainq_q8_twisted.py`).
  - Its ground states are the spinor module of the frame's Clifford algebra, so with its Q₈-action the sector does not depend on C.
  - Compare the Q₈-linearised lifts of J, K, JK there with their modular (ℤ₄-canonical) normalisation. This gives μ = e^{−2πik/8} = exp(2πi·3k·5/8), the S³/Q₈ value of Thm 8.1.
  - So for k ≡ 4 mod 8 Q₈ is proved anomalous (the class 4a) directly on V_{Λ(C)}, without the gauging lemma.
- **Non-anomaly for 8 | k, proved directly** (§8.4, `mainq_q8_nonanomaly.py`).
  - In rSH³(Q₈) ≅ ℤ₈ ⊕ ℤ₂², all of it realised by free fermions, the classes with zero cyclic restrictions are {0, κ}.
  - μ = −1 identifies κ at k ≡ 4 mod 8. For 8 | k, α_C = α_{C⊕C′} − α_{C′} = κ − κ = 0.
  - This gives a second proof of Thm 8.1 for all k. The Main Question no longer depends on the gauging lemma.
- **The facts behind μ, proved** (§8.5, `mainq_q8_orbifold_character.py`).
  - The modular covariance used is three exact eta identities (multipliers cancel; N = (√2e^{2πi/48})^{n/2}).
  - Trivial phases: a would-be Q₈-orbifold has an S-invariant character only if ψ(J)+ψ(K)+ψ(JK) = 3e^{2πik/8}, i.e. only for 8 | k and ψ = 1.
- **Morita form** (§9): Q₈-invariant codes are F₃² ⊗ U with U Lagrangian in F₃^{2r}. Maximal words are SL₂(F₃)-blocks, and the index is a sum over "good planes" of U weighted by ψ: SL₂(F₃) → ℤ/3. This gives a sign-exact index at length 72 in seconds (`ternary60 sl2words`).

--------------------------------------------------------------------------------------------

## 1. The question and GJF's theorem

**Main Question [GJF, intro and §5, unnumbered].** *For each k, does there exist a holomorphic N=1 VOA with central charge c = 12k and supersymmetric index 24/gcd(k,24)?*
- 24/gcd(k,24)·Δᵏ is the smallest multiple of Δᵏ in the image of π_{24k}TMF → MF_{12k} [T: Hopkins ICM 2002, Prop 4.6]. GJF Conj 5.5 (Stolz–Teichner) predicts that every such SCFT has index divisible by it; the Main Question asks for the converse (attainment).
- Sign: the index is defined up to sign (Ramond parity, GJF Rem 5.3), so "index 24/m" means ±24/m throughout.
- GJF's introduction also has four numbered questions, **Question 0.1–0.4** (0.1: a systematic construction of index-24 codes; 0.2: (0,1) full CFTs for Θ_Λ/ηʳ; 0.3: equivariant TMF; 0.4: physical meaning of torsion classes). [I §5.1(f‴)] said "0.1–0.3"; corrected there.
- GJF: "one way to affirmatively answer the Main Question is to construct self-dual ternary codes with index 24 (and an appropriate orbifoldable symmetry)". They answer it for k ≤ 5.

**Theorem 5.6 [T: GJF, `thm.answers`].** Let C be self-dual of length c = 12k with Index(C) = 24, and put m = gcd(24, k). Let g ∈ Aut(C) ⊂ 2^c:S_c (signed coordinate permutations) have order m, and suppose
1. if m is even, g^{m/2} = −1;
2. if 3 | m, g^{m/3} fixes as many even as odd maximal codewords, and its image in S_c has cycle shape 3^{c/3}.

Then the lift of g to V_{Λ(C)} is non-anomalous and V_{Λ(C)}//⟨g⟩ has index 24/m.
- *Mechanism.* The orbifold index is (1/m)Σ_{(a,b)} Z_RR(gᵃ, gᵇ). The untwisted term is 24/m. Every other term is related by SL₂(ℤ) to a twined index tr_{V_R}((−1)^F h) for a generator h of ⟨gᵃ, gᵇ⟩, which only sees the Ramond ground states, i.e. the h-fixed maximal codewords. If h has even order, a power of h is −1, which fixes no maximal codeword; if h has order 3, condition 2 makes the signed count vanish.
- *Anomaly.* For m even the conditions force every cycle of g to have length m/2 with an odd number of sign changes; GJF compute the anomaly from the Frame shape (m/2)^{−24k/m} m^{24k/m} and it vanishes because m | k. For m = 3 the Frame shape is 3^{4k}, again fine since 3 | k.
- *Examples [GJF Ex 5.7].* k = 2: g = −1. k = 3: the shift e_i ↦ e_{i+12} on 36 coordinates. k = 4: e_i ↦ e_{i+24} (i ≤ 24), e_i ↦ −e_{i−24} (i > 24). k = 5: Elkies' code, no g needed. Found "by randomly generating self-dual codes with an appropriate automorphism and then calculating the index". Generator matrices extracted from the TeX: `ternary60/codes/gjf_ex57_len{12,24,36,48,60}.txt` and the collapsed fixed code of the k = 3 example, `gjf_ex57_len36_fixed12.txt`.

--------------------------------------------------------------------------------------------

## 2. What Theorem 5.9 of [I] gives with no extra work

**Corollary 2.1 [P, given T: GJF Thm 5.6 and I Thm 5.9].** The Main Question has a positive answer for every k with gcd(k, 24) ∈ {1, 2}, i.e. for every k divisible by neither 3 nor 4.
- *Proof.* [I Thm 5.9] gives a self-dual C of length 12k with Index ±24 (re-sign one coordinate to make it +24). If m = 1 take g = 1: V_{Λ(C)} itself has index 24. If m = 2 take g = −1, which lies in Aut(C) for every linear code: condition 1 holds (g^{m/2} = −1) and condition 2 is empty, so V_{Λ(C)}//⟨−1⟩ has index 12. □
- These are 12 of the 24 residue classes of k mod 24; GJF had k ≤ 5.
- `paper/index24.tex` (final remark) stated only the gcd = 1 case; the gcd = 2 sentence was added 2026-09-26.

--------------------------------------------------------------------------------------------

## 3. Do our codes have the automorphisms Theorem 5.6 needs?

Monomial automorphism groups computed with nauty/Traces (`dreadnaut`, nauty 2.8.8) on the graph whose vertices are the ± coordinate vertices and the codewords of weight ≤ w (w = smallest weight whose words span C; the words come from `ternary60 words`, two complementary information sets). Every generator nauty returns is re-checked to preserve C. Script: `mainq_automorphisms.py` (log beside it).

**The [I Thm 5.9] chain codes `quad_index24_len<n>.txt` [V].**

| n | k | m = gcd(k,24) | \|Aut(C)\| | element Thm 5.6 needs | present? |
|---|---|---|---|---|---|
| 24 | 2 | 2 | 3072 | −1 | yes (always) |
| 36 | 3 | 3 | 256 (a 2-group) | order 3, cycle shape 3¹², balanced | **no** |
| 48 | 4 | 4 | 196608 | order 4, g² = −1 | **yes** (2816 such elements) |
| 60 | 5 | 1 | 8192 | none | – |
| 72 | 6 | 6 | divides \|Aut(W₁₂)\| = 2²⁵ | order 6, g³ = −1, g² of shape 3²⁴, balanced | **no** |
| 84 | 7 | 1 | – | none | – |

- The length-36 and length-72 codes fail: their automorphism groups are 2-groups, so they have no element of order 3 at all. (At n = 72 the words of weight ≤ 12 span only 34 of 36 dimensions and weight 15 is too big for the graph, so we bound: Aut(C) ⊂ Aut(W₁₂), the monomial maps preserving the set W₁₂ of words of weight ≤ 12, and nauty gives |Aut(W₁₂)| = 2²⁵.) So the Thm 5.9 codes do **not** automatically carry the needed symmetry.
- The length-24 and length-48 codes carry much more than they need: fixed-point-free order-3 elements with balanced fixed counts (T = 0) and order-12 elements g with g⁶ = −1 and cycle shape 6^{n/6}. [H] Presumably this comes from Aut(Golay) elements that stabilise the chain's block systems (Lemma 4.1) together with the internal pair swaps of the Hadamard gluing; not analysed.

**GJF's own codes [V].** |Aut| = 384, 6, 4, 2 at n = 24, 36, 48, 60: the k = 3 code has exactly ⟨−1, h⟩ (h the shift, T_h = 0), the k = 4 code exactly ⟨J⟩ (J² = −1). The random search found nothing beyond the prescribed symmetry.

**Seed and chains [V].** The ℤ/12 seed `z12seed_len36_3` has Aut = ⟨g⟩ exactly (order 12). The J-chain code of length 48 has |Aut| = 49152 with 2560 elements J, J² = −1.

**Golay [V].** |Aut| = 190080 = 2·|M₁₂|. Element types relevant to Thm 5.6: 792 elements J with J² = −1 and cycle shape 2⁶; 2640 fixed-point-free elements of order 3 (shape 3⁴, T = 0) and 1760 of shape 3³1³ (T = 6); 15840 elements of order 12 with g⁶ = −1 and shape 6²; **no element of order 8 with g⁴ = −1** and none of order 24.

--------------------------------------------------------------------------------------------

## 4. Carrying the symmetry through the construction

The engine of [I Thm 5.9] (partial quadrupling Q_σ) uses only tetracodes and coordinate-pair Hadamard maps, so it can be made equivariant. Code: `mainq_equivariant.py` (`quad_eq`).

Conventions. A block is a 4-tuple (a, b, c, d) read with the pair split {a, b}, {c, d}; the step-1 blocks of Q_σ are (a, a*, b, b*), (c, c*, d, d*), and refining a step-1 block B with a split {w, x}, {y, z} gives the 4-sets {w, w**, x, x**}, {y, y**, z, z**}. Lemma 5.6 and Lemma 5.8 of [I] hold for every choice of splits and placements, and for any linear E ([I §5.1(f″)], `paper_check.py`; [EQ] Thm 3.3).
- **Which splits the chains use (corrected 2026-09-27).** The splits are not the literal ones above. `mainq_equivariant.choose_splits` re-splits every new block so that its stabiliser fixes both pairs. For a J-stable step-1 block B = {p, p*, q, q*} this is the *transposed* refinement split {p, q}, {p*, q*}, and the σ″-blocks {x, y, x**, y**} are split {x, y}, {x**, y**}.
- With the literal splits the next step-1 blocks have stabiliser {±1}: with the canonical refinement split J maps each σ″-block onto the other, and with a canonical σ″-split J swaps its two pairs. Either way, from the third step on k grows by |G| instead of |G|/2, and the ℤ/12 chains would miss k ≡ 6, 18 mod 24 from k = 18 and k ≡ 9, 21 mod 24 from k = 21 ([EQ] Lemma 4.11 and its remark; [CS] §3.6; [V: `blueprint_chains.py` Part 3]).
- `lean/GJF/Existence.lean` hard-wires the canonical split (`refd`, `r₂`); a Lean version of the chains needs the transposed one (`refdᵗ`, [CS] §5 and §3.6).

**Lemma 4.1 (equivariant quadrupling) [P].** Let G ⊂ Aut(E) ⊂ 2^m:S_m be a finite group that permutes the blocks of σ and maps split pairs to split pairs. Extend each g ∈ G to the new coordinates by letting a Hadamard partner follow its partner with the same sign: g(e_x) = s e_{g·x} ⇒ g(e_{x*}) = s e_{(g·x)*} (same at step 2). Suppose the tetracodes are placed G-equivariantly (on one block per G-orbit a placement invariant under the stabiliser, elsewhere its transport). Then:
1. G acts faithfully on F₃^{m+12b} and G ⊂ Aut(Q_σ(E)).
2. Orders, the relation g^j = −1, and cycle lengths are inherited: a new coordinate lies in a cycle of the same length as its partner.
3. If the refined set of step-1 blocks is G-stable and its splits are chosen G-equivariantly, σ″ is again G-stable. The construction iterates *provided invariant placements exist again at both steps of the next stage*: a stabiliser acting on a split pair by an involutive swap or by diag(1, −1) admits no invariant step-2 placement ([EQ] Prop 4.10). With transposed splits, the three local types of block stabiliser (scalar, J-type, Q₈-regular) propagate, so placements exist at every stage of all four chains used here ([EQ] Lemma 4.11).
- *Proof.* On a Hadamard pair (x, x*) the map (u, v) ↦ (u + v, u − v) commutes with the scalar s, so each step-1 and step-2 Hadamard map commutes with G. E ⊕ T₁^b ⊕ T₂^{2b} is G-invariant by hypothesis, hence so is its image Q_σ(E). Item 2 and the G-stability of σ″ are immediate from the definition of the extension; the existence of invariant placements at the next stage is [EQ] Prop 4.10 and Lemma 4.11. □
- *When do invariant placements exist?* The stabiliser G_β acts on the new block β* as it acts on β, by signed permutations. A tetracode placement invariant under G_β exists iff that image lies in a conjugate of Aut(tetracode) ≅ GL₂(F₃) inside 2⁴:S₄ (8 conjugates = 8 placements). For the cases used here: J with J² = −1 acting as a double transposition (an element of Q₈ ⊂ GL₂(F₃)) — yes; a fixed-point-free order-3 map never stabilises a block (4 is not a multiple of 3), so its blocks come in orbits of 3 and no condition arises. `placement_on` finds the placement.
- *Consequence for k mod 3.* If an element of order 3 lies in G, every block orbit has size divisible by 3, so b ≡ 0 mod 3 and k mod 3 is invariant along a G-chain. Order-3 chains need a seed with 3 | k.

**Theorem 4.2 (m = 4) [P, given T: GJF Thm 5.6; V].** For every even k there is a self-dual ternary code of length 12k with Index ±24 and an automorphism J with J² = −1 whose coordinate cycles are all 2-cycles. Hence the Main Question has a positive answer for gcd(k,24) = 4.
- *Construction.* J ∈ Aut(Golay) with J² = −1, cycle shape 2⁶ (one of 792). The block β = (0,1,2,3) is J-stable with J-stable pairs {0,1}, {2,3}, and R_β(Golay) = 24 (as for all 495 blocks, [I Thm 5.9]). Apply Lemma 4.1 with G = ⟨J⟩ and, at each step, refine one J-stable step-1 block with a J-stable split; σ″ is again two J-stable blocks. Lengths 12 + 12 + 24j, i.e. every even k; Index = 24 by [I Lemma 5.8].
- *Theorem 5.6.* For k ≡ 4 mod 8 with 3 ∤ k, m = 4 = ord J and J^{m/2} = J² = −1; condition 2 is empty. So V_{Λ(C)}//⟨J⟩ has index 6.
- [V: `mainq_jchain.py`, log beside it] J-invariance, J² = −1, cycle shape 2^{n/2} and self-duality at n = 24, 48, 72, 96, 120, 144; Index = 24 sign-exact at n = 24, |Index| = 24 (Rust) at n = 48, 72. Codes `ternary60/codes/jchain_len<n>.txt`, J in `jchain_len<n>.gens.txt` (the older `.J.txt` files have no separators and are ambiguous; `mainq_gens_files.py`).

**Lemma 4.3 (fixed codes collapse) [P].** Let h ∈ G have order 3 and no fixed coordinate; after a diagonal sign change (which changes Index and the twined count T_h := Σ_{x∈C^h} f(x) by the same global sign) h is a permutation. Collapse h-fixed vectors to one coordinate per h-orbit; φ³ = φ gives f(x) = f(x̄). Then the collapsed fixed code of Q_σ(E) is Q_σ̄(D), where D is the collapsed fixed code of E and σ̄ the collapsed blocks (one per orbit of 3 blocks; the fixed part of a transported triple of tetracodes is a tetracode). Therefore
      **T_h(Q_σ(E)) = R_σ̄(D),   and   R_σ̄″(Q_σ̄(D)) = R_σ̄(D)**,
so T_h is constant along an h-equivariant chain.
- *Proof.* Q_σ(E) is the G-equivariant image of E ⊕ T₁^b ⊕ T₂^{2b}, so its fixed vectors are the images of fixed vectors. The Hadamard maps commute with the collapse. [I Lemma 5.8] is a local identity (sum over the tetracode variables block by block), valid for any linear code, self-dual or not. □
- So on a chain, Index = R_σ(seed) and T_h = R_σ̄(D_seed): both are decided on the seed.

**Theorem 4.4 (m = 3, 6, 12) [P, given T: GJF Thm 5.6; V].** For every k divisible by 3 there is a self-dual ternary code of length 12k with Index ±24 and an automorphism g of order 12 with g⁶ = −1, all coordinate cycles of length 6, and T_{g⁴} = 0. Hence the Main Question has a positive answer for gcd(k,24) ∈ {3, 6, 12}.
- *Seed [V: `mainq_seed_search.py`].* g on 36 coordinates: six signed 6-cycles e_{6j+i} ↦ e_{6j+i+1} (i < 5), e_{6j+5} ↦ −e_{6j}. GJF's method (random g-invariant self-dual codes, keep Index = ±24 and T_{g⁴} = 0) found 8 seeds in 300 samples (`ternary60/codes/z12seed_len36_<i>.txt`).
- *Block systems.* J = g³ pairs coordinates inside each 6-cycle, h = g⁴ cycles those pairs. A g-stable block is two J-pairs from different 6-cycles; its h-orbit gives 3 blocks. On seed 3, 2 of the 45 such 3-block systems have R_σ = ±24 and R_σ̄(D) = 0, and 3 of the 405 six-block systems do.
- *Chains.* Refining one h-orbit of J-stable step-1 blocks gives 6 new blocks (k grows by 6). From k = 3: with b₀ = 3 the chain reaches k = 6, 12, 18, 24, …; with b₀ = 6 it reaches k = 9, 15, 21, … . Together with k = 3 itself: every multiple of 3.
- *Theorem 5.6.* m = 3: g⁴ = h has order 3, cycle shape 3^{n/3}, T_h = 0. m = 6: g² has order 6, (g²)³ = −1, (g²)² = h. m = 12: g itself. (m = 24 needs an element of order 24; see §5.)
- *Sign (added 2026-09-27).* The chains from seed 3 have Index = R_σ(seed 3) = −24, while GJF Thm 5.6 is stated for Index 24. Replace (C, g) by (dC, dgd⁻¹) for a diagonal d with an odd number of −1's. Since f(dx) = (Π d_i)·f(x), this multiplies Index and T_h by −1. It keeps self-duality, the relations, the cycle types and the cycle sign products: on a cycle, dgd⁻¹ has signs d_{i_j}s_j d_{i_{j+1}}, whose product is Π s_j ([CS] Lemma 2.6, [EQ] Rem 4.13). (k = 3 is seed 3 itself, Index +24.) Alternatively, chains from seed 6 (`z12seed_len36_6`: R_σA6 = R_σB6 = +24, [CS] §3.3) have Index +24 from k = 6 on. The orbifold index only changes sign, so the Main Question is unaffected.
- [V: `mainq_z12chain.py`, log beside it] (results below in §6).

--------------------------------------------------------------------------------------------

## 5. An obstruction for m ∈ {8, 24}, and what is left

**Theorem 5.1 [P; V].** Let C be self-dual of length 12k and let g ∈ Aut(C) ⊂ 2^{12k}:S_{12k} satisfy g⁴ = −1. Then **48 | Index(C)**, and Index(C) = 0 if k is odd.
- g⁴ = −1 forces every coordinate cycle of g to have length 4 with an odd number of sign changes (a cycle of length 1 or 2 gives g⁴ = +1 there).
- *k odd.* For a maximal word, f(gx) = (Π_i s_i) f(x) = (−1)^{#cycles} f(x) = (−1)^{3k} f(x). So Index = −Index = 0.
- *k even.* Then f∘g = f, and ⟨g⟩ ≅ ℤ/8 acts freely on nonzero vectors (every nontrivial subgroup contains g⁴ = −1), so F(X) := Σ_X f ∈ 8ℤ for every g-invariant X ⊂ F₃ⁿ∖{0}.
  - *Structure.* Over F₃, x⁴ + 1 = (x² + x + 2)(x² + 2x + 2). On each 4-cycle F₃⁴ = V₊ ⊕ V₋ with V_± = ker of the two factors; both are Lagrangian (V_±^⊥ = V_±) and paired with each other. So g-invariant self-dual codes are C = C₊ ⊕ C₋ with C₊ ⊂ V₊^{3k} ≅ F₉^{3k} any F₉-subspace and C₋ its annihilator.
  - *Four-code identity (◇).* J = g² makes C an F₉-space with the ternary form the real part of a Hermitian form. For a J-invariant D ⊂ C of codimension 2, D^⊥/D is a Hermitian hyperbolic plane: it has 32 nonzero isotropic vectors, forming exactly 4 isotropic F₉-lines, so exactly 4 J-invariant self-dual codes C₁, …, C₄ ⊇ D. Poisson (F(D^⊥) = 9F(D)) and "maximal words are isotropic" give
        **Index(C₁) + Index(C₂) + Index(C₃) + Index(C₄) = 12·F(D).**
  - *g-neighbours.* Take D = D₊ ⊕ C₋ with D₊ ⊂ C₊ an F₉-hyperplane. D^⊥/D = L₊ ⊕ L₋ (the g-eigenlines), so C = D + L₊ and C′ = D + L₋ = D₊ ⊕ D₊^⊥ are g-invariant, while g maps F₉(u + u′) to F₉(u − u′) and so swaps C₃ ↔ C₄. Hence Index(C₃) = Index(C₄), and (◇) gives Index(C) + Index(C′) = 12F(D) − 2Index(C₃) ∈ 96ℤ + 48ℤ.
  - *Induction.* C₊ ↦ D₊ lowers dim C₊ by one, and C₊ = 0 gives C = V₋^{3k}, a sum of tetracodes (V₋ is a self-dual [4,2] code), with Index 0. □
- [V: `mainq_obstruction.py`, log beside it] (◇) sign-exact on random J-invariant configurations at n = 24 (8 Lagrangians over D, exactly 4 J-invariant); g-neighbour configurations at n = 24, 48 (2 g-invariant + 2 swapped J-invariant codes, F(C) + F(C′) ≡ 0 mod 48, 8 | F(D)); random g-invariant codes at n = 24, 36, 48, 60, 72: |Index| ∈ 48ℤ always, and Index = 0 for k odd.
- (◇) is a Hermitian analogue of the neighbour identity (★) of [I §1]; it holds for every J-invariant configuration, with no g.

**Corollary 5.2 [P].** Theorem 5.6 of GJF never applies when 8 | gcd(k, 24), i.e. k ≡ 0 mod 8: condition 1 asks for g of order m ∈ {8, 24} with g^{m/2} = −1, so h = g^{m/8} has h⁴ = −1, and then 48 | Index(C), contradicting Index(C) = 24. The same holds for any cyclic orbifold whose twisted sectors are killed this way.

**What could still work for k ≡ 0 mod 8 [C].**
- *Quaternion groups.* Q₈ = ⟨J, K⟩ ⊂ Aut(C) with J² = K² = −1, JK = −KJ has no element of order 8, so Theorem 5.1 does not apply. Random Q₈-invariant codes do reach |Index| = 24 [V: 27 of 100 at n = 24; also at n = 36, 48]. All abelian subgroups of Q₈ are cyclic and every nontrivial one contains −1, so every commuting pair (g′, g″) generates a cyclic group whose twined index vanishes, exactly as in GJF's proof: **if the Q₈ action is non-anomalous, V_{Λ(C)}//Q₈ has index 24/8 = 3.** Likewise Q₈ × ℤ/3 (with T_h = 0) would give index 1 at k ≡ 0 mod 24.
- *Q₈-equivariant chains exist [V: `mainq_q8chain.py`, log beside it].* A random Q₈-invariant code of length 24 with |Index| = 24 has a Q₈-stable 2-block system (two coordinate groups, splits into J-pairs) with R_σ = 24. Lemma 4.1 with G = Q₈ (refining the Q₈-orbit of one step-1 block, 4 new blocks per step) gives Q₈-invariant self-dual codes with Index ±24 at n = 48 (|Index| = 24, Rust) and n = 96 (k = 8; Index 24 by [I Lemma 5.8]), and at every k ≡ 0 mod 4. So for k ≡ 8, 16 mod 24 **everything is in place except the anomaly**.
- The missing piece is the anomaly. Restrictions to the three cyclic ℤ/4's vanish when 4 | k (GJF), but for bosonic anomalies H⁴(Q₈; ℤ) = ℤ/8 restricts onto each H⁴(ℤ/4; ℤ) = ℤ/4 with kernel {0, 4}, so cyclic subgroups do not detect everything. Heuristically the anomaly is additive over the 3k free Q₈-orbits of coordinates (it is determined by the action on the frame VOA V_{√3ℤ}^{⊗n}), so it is 3k times that of one orbit and vanishes if its order divides 24 and 8 | k. This needs a real computation (spin bordism of BQ₈; cf. Johnson-Freyd–Treumann, H⁴(Co₀; ℤ) = ℤ/24).

--------------------------------------------------------------------------------------------

## 6. Status by residue class, and verification

| k mod 24 | m = gcd(k,24) | index target | how | status |
|---|---|---|---|---|
| 1, 5, 7, 11, 13, 17, 19, 23 | 1 | 24 | [I Thm 5.9], g = 1 | [P] |
| 2, 10, 14, 22 | 2 | 12 | [I Thm 5.9], g = −1 | [P] |
| 4, 20 | 4 | 6 | J-chain from Golay (Thm 4.2) | [P; V] |
| 3, 9, 15, 21 | 3 | 8 | ℤ/12-chain B, and the seed itself for k = 3 (Thm 4.4) | [P; V] |
| 6, 18 | 6 | 4 | ℤ/12-chain A, g² (Thm 4.4) | [P; V] |
| 12 | 12 | 2 | ℤ/12-chain A, g (Thm 4.4) | [P; V] |
| 8, 16 | 8 | 3 | cyclic route impossible (Thm 5.1); Q₈ chain + Q₈ non-anomalous for 8 \| k (Thm 8.1, Cor 8.2) | [P; V] |
| 0 | 24 | 1 | cyclic route impossible (Thm 5.1); Q₈ × ℤ/3-chain from a length-72 seed (§9, Thm 10.1) | [P; V] |

"[P]" here means: proved here given GJF Thm 5.6 [T, via T*] (including its anomaly analysis; its orbifold step is the fermionic GJF Thm 4.2, [T*], in the form ORB of `notes/blueprint/orbifold-foundations.md` Hyp 5.5) and [I Thm 5.9] (not yet independently read).

Verification [V]:
- `mainq_jchain.py` (log): J-chain n = 24 … 144.
- `mainq_z12chain.py` (log): chain A (σ₃, b₀ = 3): seed Index = +24, T_h = 0, R_σ₃ = −24, R_σ̄₃(D) = 0; n = 72 (k = 6): g-invariant, ord g = 12, g⁶ = −1, 6-cycles, |Index| = 24 (Rust), T_h = 0 by enumeration; n = 144 (k = 12): same with T_h = 0 by enumeration (3²⁴ words, Rust) and Index = −24 by [I Lemma 5.8]. Chain B (σ₆, b₀ = 6): R_σ₆ = −24, R_σ̄₆(D) = 0; n = 108 (k = 9): invariance and T_h = 0 by enumeration.
- `mainq_seed_search.py` (log): the seed search (8 of 300 random g-invariant codes are seeds; Index 0 is the most common value) and the good block systems (R_σ = ±24, R_σ̄(D) = 0): seed 3 has 2 of 45 (b = 3) and 3 of 405 (b = 6); seed 4 has 5 of 45 and 2 of 405. (Exploratory runs found 2–3 good b = 6 systems on seeds 1 and 2 as well.)
- `mainq_obstruction.py` (log): Theorem 5.1 and (◇).
- `mainq_q8chain.py` (log): the Q₈ chain n = 24, 48, 96.
- `mainq_q8_anomaly.py` (log): Theorem 8.1 (the reduction checks on the Q₈-chain codes; eta invariants).
- `mainq_orbifold_index.py` (log): `notes/orbifold-index.md` (Lemma 2.1 and SL₂(ℤ/3)-transitivity; on the actual codes: self-duality, ε = 1, fixed-point-free coordinate permutations for g ≠ ±1, and E_g = n/24 + n/(12m²) exactly for every element of even order; the vanishing table).
- `mainq_gens_files.py` (log): unambiguous `.gens.txt` generator files for the J- and ℤ/12-chains.
- `blueprint_*.py` (logs): the checks for the Lean blueprint files in `notes/blueprint/`.
- `mainq_q8_orbifold_character.py` (log): §8.5 (exact eta multipliers and identities (i)–(iii); S-invariance of the would-be orbifold character for each ψ at k = 4, 8, 12, 16).
- `mainq_q8_nonanomaly.py` (log): §8.4 (free fermions exhaust rSH³(Q₈), cyclic kernel {0, κ}; the codes at n = 48, 96 and their direct sums at n = 144: Majorana layer, cyclic anomalies, μ).
- `mainq_q8_twisted.py` (log): §8.3 (the frame Clifford module T and the Pin lifts of J, K on the Q₈-chain codes; T ≅ (H ⊕ 2ψ)^{⊗3k}; the modular normalisation N = 2^{3k}e^{2πik/8}; μ against the S³/Q₈ eta values for k ≤ 48).
- `mainq_q8_gauging.py` (log): §8.2 (the multi-neighbour data of Step 1 on the Q₈-chain codes and random Q₈-invariant codes; GJF's cyclic anomaly against 3k·a on ⟨J⟩, ⟨K⟩, ⟨JK⟩, ⟨−1⟩ in ℤ_{2m} and on lens spaces; w₁(Reg) = 0).
- `mainq_automorphisms.py` (log, needs nauty): §3.
- `mainq_72rule.py` (log): §9 (sl2words vs rsigma; the exact laws at n = 12, 24, 36; counterexamples to the 72-rule at n = 72).
- `mainq_q8z3_seed72.py` (log): §9.4 (seed search statistics; the chain pipeline in the Morita layout).
- `mainq_q8z3_chain24.py` (log): §10 (the seed, R_σ = 24 three ways, R_σ̄(D) = 0; the chain at n = 144, 288).
- `mainq_e72_infoset.py` (log): §10, R_σ(E₇₂) = +24 and Index(E₇₂) = −1608 by information-set enumeration (`rsigma_is`), independent of sl2words.
- The four-code identity and Lemma 4.3 are local/Poisson identities; all numerics are sign-exact where stated (Rust `rsigma` enumerates the code, no sign normalisation).

## 7. Remarks and further directions

- **Nonzero twisted sectors [H].** If the twisted–twined RR indices of an order-3 h all equal T_h (no phases), then V//⟨h⟩ has index (Index(C) + 8T_h)/3, and similarly (Index + 8T_h)/m for m ∈ {6, 12} when g^{m/2} = −1. This would allow T_h ≠ 0 (e.g. Index = −168, T_h = 24). Consistent with Bantay's formula for cyclic permutation orbifolds of E³ ((I³ + 8I)/3) and with integrality: T_h ≡ 0 mod 3 whenever 3 | k (next item). Not needed for the results above.
- **Trace formula for T_h [P; V].** For h of order 3 (a permutation after a sign change) with a fixed and b 3-cycles, let π(C) be the code of orbit sums (fixed coordinates kept, each 3-cycle summed), N = a + b, d = dim π(C). Then the collapsed fixed code is π(C)^⊥, and Poisson gives **T_h = ±3^{N/2 − d} · i^N · F(π(C))**. Checked on all order-3 elements of Aut(Golay) (T = 6 for shape 3³1³, T = 0 for 3⁴) and of the length-24 chain code (`mainq_common.twined_count_trace`). For fixed-point-free h, N = 4k and π(C) ⊂ π(C)^⊥ = D is self-orthogonal, so d ≤ 2k. If d < 2k then T_h ∈ 2·3^{2k−d}ℤ (F(π(C)) is even, x ↔ −x); if d = 2k then D is self-dual and T_h = Index(D) ∈ 24ℤ when 3 | k. Either way T_h ≡ 0 mod 3 for 3 | k.
- **Fixed points.** An order-3 element with fixed coordinates cannot stabilise a block with an invariant split (a 3-cycle on 4 points preserves no perfect matching), so it gives nothing new for the chains.
- **Literature.** GJF is the only source found for the Main Question; the citation search of [I §5.1(f‴)] is still open, and the same caveat applies here.

--------------------------------------------------------------------------------------------

## 8. The Q₈ anomaly (2026-09-26, later session)

Notation: A(G) := Hom(Ω₃^Spin(BG), U(1)), the group of anomalies of a G-action on a 2d fermionic theory (for G acting by even automorphisms, symmetry G × ℤ₂^F). GJF's anomaly lies in extended supercohomology S̃H³(G) [GJF Thm 4.2], which is A(G): the spectrum of extended supercohomology is a connective cover of the Pontryagin dual of spin bordism [JF §2.4]. Restricted supercohomology rSH³(G) ⊂ S̃H³(G) is the part with vanishing Majorana layer; it contains all classes met here.

**Theorem 8.1 [P, given T: GJF Thm 3.1 and the coprime-gauging lemma (§8.2, Lemma E); V. Second proof without the gauging lemma: §8.4].** Let C be self-dual of length n = 12k and Q₈ = ⟨J, K⟩ ⊂ Aut(C) with J² = K² = −1 (so the centre acts as −1). Then the anomaly of the Q₈-action on V_{Λ(C)} is **3k·a**, where a ∈ A(Q₈) is the anomaly of Q₈ acting on 8 Majorana fermions in the real regular representation. **a has order exactly 8.** So the action is non-anomalous iff **8 | k**.

*Proof.*
- **Step 0 (orbits).** J² = −1 means J fixes no coordinate, and likewise K and JK. So V₄ = Q₈/±1 acts freely on coordinates: there are n/4 = 3k orbits of size 4.
- **Step 1 (reduction to a model code) [P, given T: Lemma E of §8.2; V].** On each orbit O choose a Q₈-invariant tetracode T_O; in Morita form these are F₃² ⊗ ℓ for the 4 lines ℓ ⊂ F₃² (Lemma 9.1), so there are exactly 4. Put C₀ = ⊕_O T_O. Details and proofs are in §8.2:
  - C₀ is the multi-neighbour of C along a Q₈-stable W ⊂ C₀ ([I §5.1(d)]), so V_{Λ(C₀)} = V_{Λ(C)}//Ŵ, where Ŵ ≅ W is a 3-group of phases ζ^{w·c} normalised by Q₈ (Lemmas A, B).
  - The anomaly of Γ = Ŵ ⋊ Q₈ is inflated from Q₈: its 2-part because BQ₈ → BΓ is a ℤ₍₂₎-homology equivalence, its 3-part because it restricts injectively to Ŵ, which is non-anomalous (Lemma D).
  - Gauging the normal subgroup Ŵ of coprime order leaves an inflated anomaly unchanged (Lemma E: Naidu, Uribe; Tachikawa; Johnson-Freyd). So Q₈ has the same anomaly on V_{Λ(C₀)}, with the induced action.
  - The induced action is conjugate to GJF's canonical one for C₀: both act on the frame V_{√3ℤ}^{⊗n} in the standard way, and two such lifts differ by a cocycle Q₈ → C₀^*, a 3-group, so H¹ = 0 (Lemmas C, F).
- **Step 2 (free fermions) [P].** Λ(T) ≅ ℤ⁴ (the only odd unimodular lattice of rank 4), so V_{Λ(C₀)} = ⊗_O V_{ℤ⁴} = ⊗_O Fer(8), with Q₈ acting factor by factor.
  - An automorphism of Fer(8) is determined by its action on the weight-½ space, which is spanned by the e^{t/√3}, t ∈ T∖0.
  - Q₈ permutes these up to sign, and freely: every nontrivial subgroup contains −1, and −t ≠ t. So the character is regular, and V_{½} ≅ Reg = 1 ⊕ χ_i ⊕ χ_j ⊕ χ_k ⊕ H as orthogonal real representations (H = the 4-dim quaternionic irreducible).
  - Hence the anomaly is 3k·a with a := A(Fer(Reg)).
- **Step 3 (8a = 0) [P, T].** Anomalies add under tensor products, so a = A(χ_i) + A(χ_j) + A(χ_k) + A(H).
  - A(χ) = χ*ν, where ν ∈ A(ℤ/2) ≅ ℤ/8 is the class of one Majorana odd under ℤ/2 (Kitaev).
  - A(H) = ρ_H*κ_L, where ρ_H: Q₈ → SU(2)_L ⊂ SO(4) and κ_L is the anomaly of SU(2)_L on 4 Majoranas (SO(4)₁ = SU(2)₁ × SU(2)₁). This is level-1 Chern–Simons, a bosonic class c₂ ∈ H⁴(BSU(2); ℤ), so ρ_H*κ_L is the image of ρ_H*c₂ ∈ H⁴(BQ₈; ℤ) = ℤ/8. (κ_L is not the class κ = A(Fer(4H)) = 4a of §8.4.)
  - So 8a = 0.
- **Step 4 (order exactly 8; cross-check) [V: `mainq_q8_anomaly.py`, log beside it].**
  - For chiral Majoranas in a real representation ρ, on a spherical space form M = S³/Γ (Γ ⊂ SU(2), spin structure ε: Γ → ±1), the anomaly is A_ρ(M) = ½(η(ρ) − dim ρ·η(1)) mod 1. Here η(ρ) = −(1/|Γ|)Σ_{g≠1} ε(g)χ_ρ(g)/(2 − tr g) (Donnelly's equivariant formula).
  - Calibration: one Majorana odd under ℤ/2 on RP³ gives 1/8, 7/8, the Kitaev generator.
  - Results, all spin structures:

    | M | A_{χ_i}, A_{χ_j}, A_{χ_k} | A_H | A_Reg |
    |---|---|---|---|
    | RP³ = S³/⟨−1⟩ | 0 | 1/2 | 1/2 |
    | S³/⟨i⟩ (and ⟨j⟩, ⟨k⟩) | 0, 1/4 or 3/4 | 3/4 | 1/4 |
    | S³/Q₈ | 1/4 or 3/4 or 0 | 7/8 | **5/8** |

  - So a has order 8. 3k·a vanishes on these space forms exactly when 8 | k. Its restrictions vanish exactly when 2 | k (on ⟨−1⟩) and when 4 | k (on ℤ/4), which is GJF's anomaly clause "m | k" of Thm 5.6 for m = 2, 4: an independent check of the normalisation.
- **TMF consistency.** When 8 ∤ k and 4 | k, a non-anomalous Q₈ would give index 3, but TMF demands 24/gcd(k,24) ∈ {6, 2} | index. The theorem says Q₈ is anomalous exactly there. □

**Corollary 8.2 (Main Question for k ≡ 8, 16 mod 24) [P, given T*: GJF's orbifold theorem for non-anomalous finite groups (their §4; fermionic case sketched, ORB), the index computation `notes/orbifold-index.md`; T: Thm 8.1 (by §8.2 or, without the gauging lemma, §8.4), and I Thm 5.9].** For every k ≡ 0 mod 8 there is a holomorphic N=1 SVOA of central charge 12k and index 3. In particular, the Main Question has a positive answer for gcd(k,24) = 8.
- *Proof.* The Q₈-chain (`mainq_q8chain.py`) gives, for every k ≡ 0 mod 4, a self-dual C of length 12k with Index ±24 and Q₈ ⊂ Aut(C) of the kind in Theorem 8.1. For 8 | k the Q₈-action is non-anomalous, so V_{Λ(C)}//Q₈ exists; it is N=1 because Q₈ fixes the supercurrent. Every commuting pair in Q₈ generates a cyclic group, and every nontrivial one contains −1, which fixes no maximal codeword. So all twisted–twined RR terms vanish as in GJF's proof, and the index is 24/8 = 3. □ The index computation is proved in detail in `notes/orbifold-index.md` (Theorem O): for Q₈ every twisted term vanishes directly, with no modular transformation.
- Checked explicitly at k = 8 (n = 96): Q₈-invariance, J² = K² = −1, JK = −KJ, self-duality; Index = 24 by [I Lemma 5.8].

**k ≡ 0 mod 24 (m = 24, index 1).** Use G = Q₈ × ℤ/3 with h of order 3, fixed-point-free and balanced (T_h = 0).
- *Anomaly.* It vanishes for 24 | k: the Q₈ part by Theorem 8.1, the ℤ/3 part by GJF's Frame-shape computation (3 | k), and the mixed part by coprimality.
- *Twisted sectors.* All abelian subgroups of G are cyclic; the nontrivial ones not containing −1 are ⟨h⟩, whose twined index T_h vanishes. So the index would be 24/24 = 1.
- *What is needed.* A G-invariant seed with Index ±24 and T_h = 0, and a G-stable block system of the right size.

### 8.1 Q₈ × ℤ/3: the "72-rule" — true at length 36, false at length 72 [V: `mainq_q8z3.py`, `mainq_72rule.py`, logs beside them]

Setting: 36 coordinates in nine Q₈-orbits, with h fixed-point-free, of order 3, commuting with Q₈, and cycling the Q₈-orbits in three triples. Because h is fixed-point-free, every block orbit has size divisible by 3, so k mod 3 is invariant. After the first step the increments are multiples of 12, because a step-1 block has a G-orbit of size 6. From k = 3 one therefore needs b₀ = 9, i.e. every coordinate in blocks; then k runs through 12, 24, 36, ….
- **Observed rule at n = 36.** In 272 random G-invariant codes: T_h = 0 or ±72 always comes with Index ≡ 0 mod 72, and T_h = ±24 with Index ≡ 0 or T_h mod 72.
  - In orbit terms: G acts on maximal words with orbits of size 8 (h-fixed) and 24 (free), so Index = T_h + 24X with X the signed count of free orbits. The rule says X ≡ 0 or −T_h/24 mod 3.
- **Consistent chain search.** There are 19 G-stable 9-block systems. On about 290 random codes with Index ≡ 24 mod 48 (exploratory runs plus the logged run), every system with R_σ̄(D) = 0 had |R_σ| ≥ 72, and 72 occurs. Such a chain would have T_h = 0 and Index R_σ, so this is what the rule predicts.
- **Update (later session): the rule is false in general (§9).** At n = 72 (k = 6), 5 of 30 random G-invariant codes violate it; `ternary60/codes/q8z3_len72_T0.txt` has T_h = 0 and Index = −3840 ≡ 48 mod 72, and one random code even has Index = 24 with T_h = 0. At n = 36 the rule is explained by an exact law (§9.3). So it is **not** an obstruction to k ≡ 0 mod 24: it only says that chains seeded at k = 3 (whose index is R_σ of the seed) cannot work. Seeds at k = 6 are not constrained this way (§9.4).
- (Superseded heuristics: an h-orbifold argument for extra divisibility; the fallback list of other groups. Both are moot now.)

### 8.2 The coprime-gauging step of Theorem 8.1, checked (2026-09-26, later session) [P, T; V: `mainq_q8_gauging.py`, log beside it]

**Verdict: Step 1 is correct.** Its code-theoretic and group-cohomological parts are elementary (Lemmas A–D, F). Its one non-elementary input is the standard coprime-gauging lemma (Lemma E). That lemma is a theorem for fusion categories. For bosonic VOAs with solvable group (as Γ is) it follows from known results [JF Prop 2.2.1; Carnahan–Miyamoto]. Here it is applied to a super VOA through the bosonic shadow, which is the level of rigour of GJF Thm 4.2 itself. The check closed one gap: the 3-primary part in Lemma D, needed so that the anomaly of Γ is inflated on the nose. It also made the hypotheses of the gauging lemma explicit.

Setting: C = F₃² ⊗ U in Morita form (Lemma 9.1): U ⊂ F₃^{2r} is Lagrangian for Ω, r = 3k, and Q₈ acts on each block by left multiplication.
- Frame F = V_{√3ℤ}^{⊗n}. V_{Λ(C)} = ⊕_{c∈C} M_c with M_c = V_{√3ℤⁿ + c̃/√3}, where c̃ ∈ {0, ±1}ⁿ lifts c.
- ζ = e^{2πi/3}. C^* ≅ Hom(C, ℂ^×) ≅ 3^{n/2} denotes the automorphisms trivial on the frame (GJF's notation).

**Lemma A (multi-neighbour data) [P; V].**
- On one block the Q₈-invariant codes are F₃² ⊗ ℓ with ℓ ⊂ F₃² (Lemma 9.1). So the invariant tetracodes are F₃² ⊗ ℓ for the 4 lines ℓ, and "exactly 4" is [P].
- Take U₀ = ⊕_b ℓ_b (one line per block) and C₀ = F₃² ⊗ U₀.
  - D := C ∩ C₀ = F₃² ⊗ (U ∩ U₀).
  - W := F₃² ⊗ X for a complement X of U ∩ U₀ in U₀.
  - Every subspace F₃² ⊗ X is Q₈-stable, so Maschke is not needed.
- In Morita form ⟨(x; x′), (y; y′)⟩ = Ω(x′, y) − Ω(x, y′), where x, x′ are the rows. So (F₃² ⊗ X)^⊥ = F₃² ⊗ X^Ω.
- Consequences:
  - (i) W ⊂ C₀ is totally isotropic, so 3 | wt(w) for w ∈ W.
  - (ii) W ∩ C = F₃² ⊗ (X ∩ U) = 0.
  - (iii) C ∩ W^⊥ = F₃² ⊗ (U ∩ X^Ω) = D. Indeed u ∈ U ∩ X^Ω is Ω-orthogonal to X and to U ∩ U₀, hence to U₀, so u ∈ U₀^Ω = U₀.
  - (iv) W → Hom(C, F₃) is injective. Indeed x ∈ X with Ω(x, U) = 0 lies in U^Ω ∩ X = U ∩ X = 0.
  - (v) C₀ = D ⊕ W.
- [V] Part 1 checks all of this on:
  - the Q₈-chain codes at n = 24, 48, 96, converted to Morita form by an explicit monomial map (checked to carry C onto F₃² ⊗ U and to intertwine J, K with left multiplication by i, j);
  - 12 random Q₈-invariant codes with n ≤ 96;
  - 6 codes with large U ∩ U₀, including C = C₀ (W = 0).

**Lemma B (V_{Λ(C₀)} = V_{Λ(C)}//Ŵ, and Ŵ is non-anomalous) [P].**
- For w ∈ W put h_w = w̃/√3. Then ĝ_w = exp(2πi h_w(0)) acts on M_c by ζ^{w·c}.
  - These ĝ_w form Ŵ ≅ W, which acts faithfully by A(iv).
  - Ŵ is a group of inner automorphisms of order 3^{dim W}, normalised by Q₈ (g ĝ_w g⁻¹ = ĝ_{gw}).
- The orbifold:
  - V^Ŵ = ⊕_{c ∈ C ∩ W^⊥} M_c = V_{Λ(D)}, by A(iii).
  - The ĝ_w-twisted module is V_{Λ(C)+h_w}. Its Ŵ-invariant part is V_{Λ(D)+h_w}, by the same computation, since w ∈ W^⊥.
  - By A(v), ⊕_{w∈W} V_{Λ(D)+h_w} = V_{Λ(D⊕W)} = V_{Λ(C₀)}.
- So the Ŵ-orbifold exists and is V_{Λ(C₀)}. Equivalently, all shifts h_w lie in the integral lattice Λ(C₀): |h_w|² = wt(w)/3 ∈ ℤ and ⟨h_w, h_{w′}⟩ ∈ ℤ.
- Orbifolds correspond to trivialisations of the anomaly [GJF Thm 4.2; JF Prop 2.2.1]. So **α|_Ŵ = 0**.
- The extension V_{Λ(C₀)} ⊃ V_{Λ(D)} is stable under Q₈'s action on V_{Λ(D)}: GJF's lift for C₀ restricts to that action up to conjugation by D^* (as in Lemma C). So its discrete torsion is Q₈-invariant, as Lemma E requires.

**Lemma C (the lifts) [T: GJF Thm 3.1; P].**
- GJF Thm 3.1: Aut(C) acts on V_{Λ(C)} (the extension Λ̂[2].Aut(C) splits), through the standard action of 2ⁿ:S_n on the frame.
  - So Q₈ acts genuinely, by even automorphisms (it fixes the supercurrent), and the symmetry is Q₈ × ℤ₂^F.
  - The lift of −1 acts on each V_{√3ℤ} by the reflection θ, not by (−1)^F.
- The automorphisms trivial on F form C^*:
  - such an automorphism preserves each M_c, since the M_c are pairwise non-isomorphic F-modules;
  - it acts on each M_c by a scalar (Schur);
  - the scalars are multiplicative, since M_c · M_{c′} = M_{c+c′}.
- So two lifts of Q₈ that agree on F differ by a 1-cocycle Q₈ → C^*. Since H¹(Q₈; C^*) = 0 (coprime orders), they are conjugate by an element of C^*.

**Lemma D (the anomaly of Γ = Ŵ ⋊ Q₈ is inflated from Q₈) [P].**
- Γ := ⟨Ŵ, Q₈⟩ ⊂ Aut(V_{Λ(C)}) equals Ŵ ⋊ Q₈, since Ŵ is normal and Ŵ ∩ Q₈ = 1. A(Γ) = A(Γ)₍₂₎ ⊕ A(Γ)₍₃₎.
- **2-part.** Ŵ has odd order, so BQ₈ → BΓ is an isomorphism on ℤ₍₂₎-homology, hence on Ω₃^Spin(−)₍₂₎ (Atiyah–Hirzebruch).
  - So inflation A(Q₈) → A(Γ)₍₂₎ is an isomorphism, inverse to restriction.
  - Hence α_{Γ,(2)} = infl(α_{Q₈}), where α_{Q₈} is Q₈'s anomaly on V_{Λ(C)}.
- **3-part.** At odd primes Ω₃^Spin(BΓ)₍₃₎ = H₃(Γ; ℤ)₍₃₎.
  - Corestriction H₃(Ŵ) → H₃(Γ)₍₃₎ is onto, since corestriction ∘ transfer is multiplication by [Γ : Ŵ] = 8, a unit.
  - So restriction A(Γ)₍₃₎ → A(Ŵ) is injective, and α_{Γ,(3)} = 0 by Lemma B.
- So **α_Γ = infl(α_{Q₈})** on the nose. The original Step 1 treated only the 2-part.

**Lemma E (coprime gauging) [T].** Let Γ = A ⋊ K act by even automorphisms on a holomorphic (S)VOA V, with A abelian and gcd(|A|, |K|) = 1, and with anomaly α_Γ = infl(ε), ε ∈ A(K) (with vanishing Majorana layer in the super case). Let V′ = V//A, with any K-invariant discrete torsion. Then:
- Γ′ = Â ⋊ K acts on V′, extending the action of K on V^A (= V′^Â), with anomaly infl(ε).
- In particular a complement K′ ≅ K acts on V′ with anomaly ε. The complement is unique up to conjugacy, since H¹(K; Â) = 0.

Sources and status:
- *Fusion categories.* V//A with discrete torsion μ corresponds to the module category M(A, μ) over Vec(Γ, α_Γ). For μ = 1 the dual category is Vec(Â ⋊ K, infl ε):
  - [Naidu, Thm 4.9]; explicitly [Uribe, Thm 3.7] with F = F̂ = 0, which gives ω = ω̂ = ε.
  - The dual extension Â.K splits because H²(K; Â) = 0.
  - A K-invariant class μ extends to a 2-cocycle μ̃ on Γ, since H²(Γ; U(1))₍₃₎ = H²(A; U(1))^K. Twisting the tensor structure by μ̃ is an autoequivalence of Vec(Γ, α_Γ) that carries M(A, 1) to M(A, μ), so the dual is the same.
- *VOAs.* Rep(V^Γ) ≅ Z(Vec(Γ, α_Γ)), and holomorphic extensions of V^Γ correspond to Lagrangian algebras, i.e. to module categories; V//A is the one for M(A, μ).
  - This is [JF Prop 2.2.1] together with the argument in the proof of [JF Prop 2.3.1], which does the case of cyclic A.
  - For bosonic VOAs the remaining input is regularity of V^Γ, which holds because Γ is solvable [Carnahan–Miyamoto]. JF notes that no single complete proof of Prop 2.2.1 is written down, but that it follows from the cited literature.
- *Physics.* [Tachikawa §2.4, Claim] with e = ẽ = 0: gauging A leaves the anomaly ω(g) of the quotient group unchanged. The argument never uses the spin structure, so it applies verbatim to fermionic anomalies.
- *Super VOAs.* The Majorana layer of α_{Q₈} vanishes on V_{Λ(C)}:
  - J and K are products of n/2 transpositions with sign product −1, so ⟨χ, (1−g)χ⟩ = 3n ∈ 4ℤ (GJF Ex 4.4's criterion; [V] Part 2).
  - The Majorana layer is a homomorphism Q₈ → ℤ/2, so it vanishes on Q₈. Consistently, w₁(Reg) = 0 (Part 3).
  - So the super fusion category of twisted sectors has the bosonic shadow Vec(Γ̃, ω̃), with Γ̃ = Ŵ ⋊ 2.Q₈ and ω̃ = infl(ε̃) [JF §2.4, BGK].
  - Gauge Ŵ there and divide by the central 2, as in JF's super T-duality.
- *Status.* This is standard, but no complete written proof for super VOAs was found in the literature consulted. GJF Thm 4.2 (the fermionic anomaly itself) is at the same level.

**Lemma F (the induced action is GJF's, up to conjugacy) [P, given T: GJF Thm 3.1].**
- K′ ⊂ Γ′ acts on V′^{Â} = V_{Λ(D)} as Q₈ does on V^Ŵ = V_{Λ(D)}. In the construction behind Lemma E, K acts on the A-invariant parts of the twisted sectors through its action on those sectors, and the untwisted sector is V^A.
- So K′ acts on the frame F ⊂ V_{Λ(D)} by the standard monomial action. It preserves F and maps onto Q₈ ⊂ Aut(C₀) (the same signed permutations).
- GJF's lift for C₀ has the same frame action. By Lemma C (for C₀) the two lifts are conjugate by an element of C₀^*, and conjugate actions have equal anomalies.

**Conclusion.** GJF's Q₈-action on V_{Λ(C₀)} = ⊗_O Fer(8) has the same anomaly as on V_{Λ(C)}, as Step 1 claims.
- Lemmas A and B are the gauging; C and D are its hypotheses; E is the invariance; F identifies the action.
- Steps 2–4 then give 3k·a.

**Independent cross-check on cyclic subgroups [V: Part 2, exact arithmetic].** GJF Ex 4.4 computes the anomaly of ⟨g⟩ on V_{Λ(C)} directly, for fixed-point-free g of even order m with vanishing Majorana layer and g^{m/2} = −1 (so the lift has order m). The formula is α/(2m) ≡ m·ρ_g mod 1, where ρ_g = (1/24)Σ_k d_k (k − 1/k) is the weight of the twisted module.
- **J, K, JK.** Frame shape 2^{−6k}4^{6k} and ρ = 3n/64, so α = 2k ∈ ℤ₈.
  - Free fermions: a rotation plane of angle 2πq/m has twisted weight (q/m)²/2, so it contributes q².
  - Reg|_{⟨i⟩} has two planes of angle π/2 and one of angle π, so α(Fer(Reg)) = 1 + 1 + 4 = 6, and 3k·6 ≡ 2k ∈ ℤ₈.
- **−1.** Frame shape 1^{−12k}2^{12k} and ρ = n/16, so α = 2k ∈ ℤ₄.
  - Free fermions: two planes of angle π give α(Fer(Reg)) = 2, and 3k·2 ≡ 2k ∈ ℤ₄.
- **Lens spaces.** The same agreement holds on S³/⟨i⟩ and RP³ (eta invariants, both spin structures). The eta values obey the quadratic rule A(rotation by 2πq/m) = q²·A(generator).
- **Coverage.** Frame shapes, fixed-point-freeness, Majorana layers and g^{m/2} = −1 are computed from the actual J, K of the Q₈-chain codes (n = 24, 48, 96), and from the Frame shapes for k = 1..48.
- So Thm 8.1 holds on every cyclic subgroup without Step 1.
- **Limitation.** 4a restricts to 0 on every cyclic subgroup (4·A_Reg ∈ ℤ on S³/⟨i⟩ and RP³), and every abelian subgroup of Q₈ is cyclic, yet 4a ≠ 0 (4·5/8 ≡ 1/2 on S³/Q₈).
  - So no check done one cyclic subgroup at a time can distinguish 3k·a from 3k·a + 4a. This includes GJF's Frame-shape formula, the lens-space values, and each twisted–twining function Z(g, h) normalised within ⟨g, h⟩.
  - For 8 | k versus k ≡ 4 mod 8 the argument therefore rests on Step 1.
  - The (−1)-twisted sector does see 4a, once the Q₈-linearised lifts of J, K, JK there are compared with their modular (ℤ₄-canonical) normalisation. This is done in §8.3: for k ≡ 4 mod 8 the class 4a is proved nonzero directly on V_{Λ(C)}. (An earlier guess here, comparing lifts of −1, was wrong: the Q₈-module structure of the (−1)-twisted sector alone carries no such information.)
- **2-local picture [H].** Λ(C) ⊗ ℤ₍₂₎ = √3ℤ₍₂₎ⁿ = Λ(C₀) ⊗ ℤ₍₂₎ Q₈-equivariantly, since √3ℤⁿ has odd index in both. The 2-primary anomaly should depend only on this 2-local data; Step 1 proves that in the case at hand. §8.3 makes it precise for the (−1)-twisted sector (Lemma 8.3).

References:
- [Naidu] D. Naidu, Categorical Morita equivalence for group-theoretical categories, Comm. Algebra 35 (2007) 3544–3565, arXiv:math/0605530.
- [Uribe] B. Uribe, On the classification of pointed fusion categories up to weak Morita equivalence, Pacific J. Math. 290 (2017) 437–466, arXiv:1511.05522 (theorem numbers of the arXiv version).
- [Tachikawa] Y. Tachikawa, On gauging finite subgroups, SciPost Phys. 8 (2020) 015, arXiv:1712.09542.
- [JF] T. Johnson-Freyd, The moonshine anomaly, Comm. Math. Phys. 365 (2019) 943–970, arXiv:1707.08388.
- [Carnahan–Miyamoto] S. Carnahan, M. Miyamoto, Regularity of fixed-point vertex operator subalgebras, arXiv:1603.05645.
- [BGK] L. Bhardwaj, D. Gaiotto, A. Kapustin, State sum constructions of spin-TFTs and string net constructions of fermionic phases of matter, JHEP 04 (2017) 096, arXiv:1605.01640.

### 8.3 The Q₈-action on the (−1)-twisted sector, computed directly (2026-09-27) [P, T; V: `mainq_q8_twisted.py`, log beside it]

**Result.** For k ≡ 4 mod 8 the Q₈-action on V_{Λ(C)} is anomalous. This is proved here directly on V_{Λ(C)}, without Step 1 (the gauging lemma) and without the free-fermion eta invariants. It is exactly the class 4a of Thm 8.1, invisible to every cyclic check (§8.2). The invariant μ used for this equals exp(2πi·3k·5/8) for every k, the value of 3k·a on S³/Q₈ from Thm 8.1 Step 4.

Setting: C, Q₈ = ⟨J, K⟩ as in Thm 8.1, with GJF's lift (Lemma C of §8.2). The lift of −1 is the lattice involution θ. The (−1)-twisted module is V_{−1} = S[θ] ⊗ T, where S[θ] is the Fock space of the Heisenberg modes α(m), m ∈ ½ + ℤ, and T holds the ground states (weight n/16).

**Lemma 8.3 (the twisted sector depends only on the frame) [P, given T: twisted modules of odd lattice SVOAs (Bakalov–Kac 2004 Thm 4.2, Rem 4.4; FLM/Dong–Lepowsky treat even lattices), GJF Thm 3.1; V].** (Complete reducibility of θ-twisted frame modules and dim T = 2^{n/2}, which the step "same character ⇒ same module" needs, are supplied in `notes/blueprint/orbifold-foundations.md` Prop 4.7.)
- Each V_{√3ℤ} has a Majorana-type θ-twisted module. For L = √3ℤ, L/2L = F₂ is spanned by the odd vector √3, so the zero-mode algebra is Cl(1): one odd zero mode γ_i with γ_i² = 1.
- The frame F = V_{√3ℤ}^{⊗n} therefore has a unique irreducible θ-twisted module S[θ] ⊗ S_n, where S_n (dim 2^{n/2}) is the spinor module of the Clifford algebra Cl(n) = ⟨γ_1, …, γ_n⟩.
- V_{−1} has the same character, so as an F-module it is this irreducible module, and T = S_n.
  - [V] Consistently, the commutator form ⟨α,β⟩ + |α|²|β|² mod 2 on Λ(C)/2Λ(C) is nondegenerate (rank n on the chain codes).
- g ∈ Q₈ acts on F by the standard signed permutation (GJF Thm 3.1). By Schur, its action on V_{−1} is determined up to a scalar by that: on T it is the Pin(n)-element φ_g with φ_g γ_i φ_g⁻¹ = s_i γ_{p(i)}.
- **So V_{−1}, with its projective Q₈-action, does not depend on C.** It is the same for C and the model C₀ = ⊕ tetracodes. This is the 2-local picture made precise.

**The ground states [V: Part 1].** Q₈ acts on ℝⁿ = 3k·H (one H per orbit), so T = ⊗_O S_4 with S_4 = S⁺ ⊕ S⁻ for Spin(4) = SU(2)_L × SU(2)_R.
- Linearised, T ≅ (H ⊕ 2ψ)^{⊗3k}: on each orbit H in one parity and one 1-dim character ψ, twice, in the other.
- ρ̃(−1) = ±(parity), as it must be for the lift of θ on its own twisted sector.
- The traces t_x = Tr_T ρ̃(x) are t_J = t_K = t_{JK} = 2^{3k}·(a character), so I := t_{JK}/(t_J t_K) = 2^{−3k}. I does not depend on the linearisation.
- Checked on the Q₈-chain codes at n = 24, 48, 96, with the actual J, K: Pin lifts per transposition, the conjugation action, the Q₈ relations after linearisation, and the per-orbit decomposition. At n = 24 the traces were also computed on the full Cl(24).

**Modular normalisation [V: Part 2].** Z(1, J) = Tr_V J q^{L₀−c/24} = η(2τ)^{6k}/η(4τ)^{6k} (only λ = 0 contributes; the same for every C). The chain S T² S (in Γ_θ, so NS-NS throughout) carries it to Z(−1, J^{±1}). This fixes a lift of J^{±1} on V_{−1} with all phases trivial; its trace on T is

  N = Z(1,J)(τ/(1−2τ)) / (q^{n/48} Π_{r odd}(1 + q^r)^{−n/2}) = 2^{3k}·e^{2πik/8}.

- N is constant in τ to 10⁻¹⁴ at four points, and exact for all k, since both sides are k-th powers of the n = 12 case.
- The chain S T^{−2} S gives 2^{3k}·e^{−2πik/8}, the same iff 4 | k. So for 4 | k (where ⟨J⟩ is non-anomalous, §8.2) this is the canonical ℤ₄-lift, and N = (−1)^{k/4}·2^{3k}.
- Convention check: Z(−1, 1) = Z(1,−1)(−1/τ) equals dim T × the Fock character.

**The invariant μ [P, given T; the two facts used are proved in §8.5].**
- Write the canonical lifts on V_{−1} as x̂ = λ_x ρ̃(x) for x = J, K, JK (the same N for all three). Then Ĵ K̂ = μ·(JK)^ with μ = λ_J λ_K/λ_{JK} = 1/(N·I).
- If Q₈ were non-anomalous, the lifts of V_{Λ(C)}//Q₈ on V_{−1} would form a genuine Q₈-representation. Their restrictions to each ⟨x⟩ are trivial-phase ℤ₄-structures, i.e. the canonical lifts. Hence μ = 1.
- Here **μ = e^{−2πik/8}**: μ = −1 for k ≡ 4 mod 8, and μ = 1 for 8 | k.
- So for k ≡ 4 mod 8 the canonical lifts of J, K, JK do not multiply correctly, and Q₈ is anomalous, although all cyclic restrictions vanish (§8.2). This is the 4a part of Thm 8.1, obtained on V_{Λ(C)} directly.

**Agreement with the eta invariants [V: Part 3].** μ = exp(2πi·3k·A_Reg(S³/Q₈)) with A_Reg(S³/Q₈) = 5/8 (all four spin structures), for every k = 1..48, e.g. μ = e^{2πi·7/8} at k = 1. So this twisted-sector computation reproduces the S³/Q₈ value of Thm 8.1 Step 4, including the order-8 generator.
- For 4 ∤ k the chain lifts are not canonical, so there the agreement is an observation, not an invariant statement.

**What remains.** For 8 | k, μ = 1 alone is necessary but not sufficient. §8.4 closes this: with the structure of rSH³(Q₈) and a direct sum, non-anomaly follows.

### 8.4 Non-anomaly for 8 | k, proved directly: a second proof of Thm 8.1 (2026-09-27) [P, T; V: `mainq_q8_nonanomaly.py`, log beside it]

**Theorem 8.4.** For every Q₈-invariant self-dual C of length 12k (J² = K² = −1), the anomaly of Q₈ on V_{Λ(C)} is 3k·a. In particular it vanishes iff 8 | k. The proof uses neither the coprime-gauging lemma (Step 1, §8.2) nor eta invariants of V_{Λ(C)}.

Inputs:
- [T] the layer sequence of GJF §4: |rSH³(Q₈)| ≤ |H³(Q₈;U(1))|·|H²(Q₈;ℤ₂)| = 8·4 = 32.
- [T] GJF Ex 4.4 for cyclic subgroups.
- [T] additivity of anomalies under tensor products. V_{Λ(C⊕C′)} = V_{Λ(C)} ⊗ V_{Λ(C′)}, and GJF's lift for C ⊕ C′ is the tensor product of the lifts up to conjugation (Lemma C of §8.2).
- [T] the anomaly of free fermions on S³/Q₈ is given by eta invariants. This is used only to count classes, in step 1.
- [P, given T] "non-anomalous ⇒ μ = 1" for 4 | k (§8.5, Prop 8.5.2: S-invariance of the orbifold character).

*Proof.*
1. **The cyclic kernel of rSH³(Q₈) is {0, κ}** [V: Part 1]. Free fermions Fer(ρ), with ρ = n_iχ_i + n_jχ_j + n_kχ_k + n_H H and w₁(ρ) = 0, realise 32 distinct values of two sets of invariants:
   - the restrictions to ⟨i⟩, ⟨j⟩, ⟨k⟩, each in rSH³(ℤ₄) = ℤ₈ (the q² rule of GJF Ex 4.4);
   - the values on S³/Q₈ for its 4 spin structures.
   All of these invariants are homomorphisms. With the bound 32, free-fermion classes are therefore all of rSH³(Q₈), and the invariants separate it. The classes with all cyclic restrictions zero are exactly 0 and κ := A(Fer(4H)), which takes the value ½ on S³/Q₈.
   - By hand: a class with nonzero Gu–Wen layer is b_χ + h, where b_χ = A(Fer(2χ)) restricts to 4 on the two ℤ₄'s with χ = −1, and h ∈ H³(Q₈;U(1)) = ℤ₈ restricts to the same element on all three ℤ₄'s. So its restrictions cannot all vanish. On H³ the kernel of restriction to ℤ₄ is {0, 4·gen}.
   - (Added 2026-09-27.) This remark silently uses that the Gu–Wen layers of the three b_χ are the three nonzero classes of H²(Q₈;ℤ/2), and that the generator of H⁴(Q₈;ℤ) restricts to the same element on each ℤ₄ (Aut(Q₈)-invariance). A shorter counting proof, with neither these facts nor eta invariants, is `notes/blueprint/anomalies.md` Prop 4.3 (|rSH³(Q₈)| = 32, the cyclic-restriction image has order 16).
2. **α_C ∈ {0, κ} when 4 | k.**
   - The Majorana layer vanishes: J and K are products of n/2 transpositions of sign product −1, so ⟨χ,(1−g)χ⟩ = 3n ∈ 4ℤ. Hence α_C ∈ rSH³(Q₈).
   - GJF Ex 4.4 gives α_J = α_K = α_{JK} = 2k ≡ 0 mod 8 and α_{−1} = 2k ≡ 0 mod 4.
3. **k ≡ 4 mod 8 ⇒ α_C = κ.** μ(C) = −1 (§8.3), and a non-anomalous action has μ = 1, so α_C ≠ 0. (The logical input is Prop 8.5.2, "non-anomalous and 4 | k ⇒ 8 | k"; μ is a consistency check. `notes/blueprint/anomalies.md` Prop 4.7, Remark 4.9.)
4. **8 | k ⇒ α_C = 0.** Take any Q₈-code C′ with k′ ≡ 4 mod 8 (e.g. `q8chain_len48`). Then k + k′ ≡ 4 mod 8, so α_{C⊕C′} = κ = α_{C′} by step 3, and α_C = α_{C⊕C′} − α_{C′} = 0.
5. **All k.** δ(C) := α_C − 3k·a lies in {0, κ} by step 1, since the cyclic restrictions agree (§8.2, Part 2 of `mainq_q8_gauging.py`).
   - δ is additive under ⊕.
   - δ vanishes on tetracode sums, whose V is Fer(Reg)^{⊗3k} equivariantly (Step 2).
   - For 4 | k: steps 3–4 give α_C = (k/4 mod 2)·κ. Also 3k·a = (k/4)·12a = (k/4)·κ, since the tetracode sum at k = 4 has anomaly 12a (Step 2) and μ = −1. So δ = 0.
   - In general, add a tetracode sum D with k_D ≡ −k mod 4: δ(C) = δ(C ⊕ D) − δ(D) = 0.
   - Finally 4a = κ ≠ 0, so a has order 8. □

[V: Part 2]
- The Q₈-chain codes at n = 48 and 96, the tetracode sums at n = 48 and 96, and three direct sums at n = 144 were each checked for self-duality, Q₈-invariance, the relations, the Majorana layer and all cyclic anomalies (all 0).
- μ: +1 at k = 8 and −1 at k = 4 and 12. For example, α(`q8chain_len96`) = α(`q8chain_len96` ⊕ `q8chain_len48`) − α(`q8chain_len48`) = κ − κ = 0.

**Status.**
- Theorem 8.1 now has two independent proofs:
  - §8.2, via Step 1 (the gauging lemma) and eta invariants;
  - §8.4, via the twisted sector (μ) and the structure of rSH³(Q₈).
- The Main Question consequences (Cor 8.2, Thm 10.1) now need only GJF's orbifold theorem for non-anomalous groups and the standard theorems listed in §8.5; they no longer need the gauging lemma.

### 8.5 The facts behind μ, proved (2026-09-27) [P, T; V: `mainq_q8_orbifold_character.py`, log beside it]

§8.3–8.4 used two facts:
- (MC) the S T² S chain carries Z(1,J) to the trace of a lift of J^{±1} on V(−1);
- (TP) for a non-anomalous Q₈ the orbifold's lifts have trivial phases, so μ = 1.

Both are now proved in the form needed. (MC) becomes three exact identities. (TP) is replaced by the S-invariance of the NS character of the holomorphic orbifold, a standard theorem.

**Setting.** 4 | k, x ∈ {±J, ±K, ±JK}. All functions below carry q^{L₀−c/24}.
- Untwisted twinings: e = Z(1,−1) = η(τ)ⁿ/η(2τ)ⁿ and f = Z(1,x) = η(2τ)^{n/2}/η(4τ)^{n/2}. Only λ = 0 is fixed, and the lift acts linearly on the Heisenberg modes.
- Twisted characters: E = ch V(−1) = 2^{n/2} q^{n/48} Π_{m∈½+ℤ≥0}(1−q^m)^{−n}, and g = ch V(x) = 2^{n/4} q^{n/192} Π_{j odd}(1−q^{j/4})^{−n/2}.
  - V(x) = S[x] ⊗ T_x, where T_x is the spinor module of Cl(n/2). Each signed 2-cycle of x on the frame contributes one Majorana zero mode (Bakalov–Kac 2004 Rem 4.4; `notes/blueprint/orbifold-foundations.md` Prop 4.7; Barron–Dong–Mason treat unsigned permutations of VOAs).
  - V(x) has weights in h_x + ¼ℤ, h_x = 3n/64.
- F = q^{n/48} Π_{r odd}(1+q^r)^{−n/2}, the trace of x on the Fock space S[θ].

**Lemma 8.5.1 (modular covariance, exact) [P; V].**
- (i) e|S = E.
- (ii) f|S = g.
- (iii) f|S T² S = N·F, with N = (√2·e^{2πi/48})^{n/2} = 2^{3k}·e^{2πik/8}.

*Proof.*
- (i) and (ii): η(−1/z) = √(−iz) η(z).
- (iii): with u = 2τ and τ′ = τ/(1−2τ), 2τ′ = γ₁u and 4τ′ = γ₂(τ−½), where γ₁ = (−1 0; 1 −1) and γ₂ = (−2 −1; 1 0).
  - Both eta multipliers exp(πi((a+d)/12c − s(d,c))) equal e^{−πi/6}, so they cancel.
  - The square roots give √(−i(2τ−1))/√(−i(τ−½)) = √2.
  - η(τ−½) = e^{−2πi/48} η(2τ)³/(η(τ)η(4τ)), by Euler's identity for Π(1 − (−q)^m).
  - Hence η(2τ′)/η(4τ′) = √2·e^{2πi/48}·η(τ)η(4τ)/η(2τ)². Also F = (η(τ)η(4τ)/η(2τ)²)^{n/2}. □
- [V] The multipliers are computed exactly (Dedekind sums), and every step is checked numerically to 10⁻¹⁴.
- *Shorter proof of (iii), no Dedekind sums (review 2026-09-28, `paper/review-2026-09-28.md` S1) [P; V: `review_q8_character.py`, log beside it].* Put w = τ/4. From g = 2^{n/4}(η(τ/2)/η(τ/4))^{n/2} (this is (ii)), the T-law η(z+1) = e^{2πi/24}η(z) and Euler's η(w+½) = e^{2πi/48}η(2w)³/(η(w)η(4w)):
  - η(τ/2+1)/η(τ/4+½) = e^{2πi/48} η(τ)η(τ/4)/η(τ/2)², so g(τ+2) = N·(η(τ)η(τ/4)/η(τ/2)²)^{n/2} = N·F(−1/τ) (the last step is the S-law of η; the factors √(−iτ) cancel);
  - hence f|ST²S = (g|T²)|S = N·F|S² = N·F.
  - In this form the S-defect of Prop 8.5.2 reads ch W|S − ch W = ¼(3N − T_ψ)(F − F|S).

**Proposition 8.5.2 (the trivial-phase fact, as needed) [P, given T*: GJF Thm 4.2 (fermionic), in the form (A11) of `notes/blueprint/anomalies.md` / ORB; T: modular invariance of the NS character of a holomorphic SVOA (Dong–Zhao 2005 Thms 4.12, 7.7 and positivity at τ = i, cf. `notes/blueprint/orbifold-foundations.md` Prop 4.8(c)); twisted modules of odd lattice SVOAs (Bakalov–Kac 2004 Thm 4.2, Rem 4.4; the FLM/Dong–Lepowsky references treat even lattices)].** If Q₈ acts non-anomalously on V_{Λ(C)} with 4 | k, then ψ(J)+ψ(K)+ψ(JK) = 3e^{2πik/8} for some ψ ∈ Hom(Q₈, ±1). Hence 8 | k and ψ = 1, which is exactly μ = 1.

*Proof.*
1. **The orbifold and its sectors.** A trivialisation gives the holomorphic SVOA W = V//Q₈ = ⊕_{[g]} V(g)^{C(g)} (GJF Thm 4.2), where V(g) is the unique g-twisted module. Regauge the parities of the V(g) by a cochain β with dβ = ω₂. Then all fusion maps are even, and so are the centraliser actions, which are genuine representations. The remaining choices (β ↦ β + ψ′, ψ′ ∈ H¹(Q₈;ℤ₂)) flip the parities of V(g) with ψ′(g) = 1. That never affects V(−1), and it changes the J-sector only by ε ↦ −ε.
2. **The (−1)-sector.** C(−1) = Q₈. By Schur and Lemma 8.3 the action is ψ ⊗ ρ̃. Its traces are ψ(h)·t_h·F for h = ±x, where t_x = Tr_T ρ̃(x) = 2^{3k} (Clifford computation), and 0 for h = −1, since Tr_T ρ̃(−1) = Tr zΓ = 0.
3. **The x-sectors.** C(x) = ⟨x⟩. e^{2πiL₀} implements x(−1)^F, so ρ_x(x) = ε·e^{2πiL₀}P.
   - Odd powers have trace 0, since sdim T_x = 0.
   - *W_x := V(x)^{⟨x⟩} ≠ 0* (step added 2026-09-27; `notes/blueprint/anomalies.md` Prop 4.7). On the weight space h_x + j/4 (Fock level j/4, tensor T_x), odd powers of ρ_x(x) have trace 0 and ρ_x(x²) is the scalar ε²e^{4πih_x}(−1)^j. So the projector onto W_x has trace ¼(1 + ε²e^{4πih_x}(−1)^j)·dim, nonzero for j = 0 or j = 1; both levels are nonzero, since T_x ≠ 0 and the modes lie in ±¼ + ℤ.
   - ε = ±1 because W is an SVOA: e^{2πiL₀} = ±parity on W_x ≠ 0, and ρ_x(x) = 1 there. (The earlier argument "ε⁴ = 1 because the weights lie in h_x + ¼ℤ" silently used 4h_x ∈ ℤ; it is not needed.)
   - So the sector contributes (1/4)(g + g(τ+2)).
4. **The character.** ch W = Z(1,1)/8 + e/8 + (6/8)f + E/8 + (1/4)T_ψ·F + (3/4)(g + g(τ+2)), where T_ψ = Σ_x ψ(x) t_x. Z(1,1) is S-invariant because V is holomorphic.
5. **S-invariance.** ch W is S-invariant, since holomorphic SVOA characters are. By Lemma 8.5.1, ch W|S − ch W = ¼(3N − T_ψ)·(F − g(τ+2)/N). F and g(τ+2) have different leading exponents (n/48 and n/192), so T_ψ = 3N, i.e. Σψ(x) = 3e^{2πik/8}. The left side is 3 or −1, so e^{2πik/8} = 1. □
- [V] For k = 4, 8, 12, 16 and all four ψ, the reduced S-defect vanishes exactly for (8 | k, ψ = 1). At k = 4 and 8 the t_x come from the Clifford computation on the chain codes.

**Consequences.**
- For k ≡ 4 mod 8 the anomaly is nonzero; this now rests on standard theorems only.
- §8.4 therefore goes through with (TP) replaced by Prop 8.5.2: non-anomaly for 8 | k, and α_C = 3k·a for all k. Neither the gauging lemma nor a general trivial-phase theorem is used.
- Remaining inputs, all cited:
  - GJF Thm 4.2 and Ex 4.4;
  - the rSH³ layer bound;
  - additivity of anomalies;
  - uniqueness and explicit form of twisted modules of lattice (S)VOAs;
  - S-invariance of holomorphic SVOA characters;
  - free-fermion eta values (only to count classes in §8.4).

--------------------------------------------------------------------------------------------

## 9. Q₈-invariant codes in Morita form; the 72-rule fails at n = 72 (2026-09-26, later session)

Code: `ternary60/theory/mainq_morita.py` (library), `mainq_72rule.py` (log beside it), Rust `ternary60 sl2words`.

### 9.1 Morita form and a fast index for Q₈-invariant codes

**Lemma 9.1 (Morita form) [P; V].** Let Q₈ = ⟨J, K⟩ act on F₃^{4r} by signed permutations with J² = K² = −1 (so r orbits of size 4).
- After a monomial change of coordinates, each orbit is the quaternion algebra A = F₃⟨i, j⟩ in the coordinates (a, b, c, d) of a + bi + cj + dk, with Q₈ acting by left multiplication, and the dot product is the norm form. *Proof:* the orbit module is Ind_{⟨−1⟩}^{Q₈}(sign) = F₃[Q₈]/(1 + z) = A, with basis the images of 1, i, j, k.
- A ≅ M₂(F₃) via i ↦ [[0,1],[−1,0]], j ↦ [[1,1],[1,−1]]; the norm is det, and its polar form is ⟨X, Y⟩ = −tr(X adj Y).
- **Q₈-invariant codes are exactly C = F₃² ⊗ U** := {X ∈ M_{2×2r}(F₃) : both rows of X lie in U}, U ⊂ F₃^{2r} (block b = coordinates 2b, 2b+1), since A-submodules of A^r are F₃² ⊗ U (Morita). On C the form is ⟨X, Y⟩ = −(Ω(x₁, y₂) − Ω(x₂, y₁)) with Ω = ⊕_b ω_b, ω(x, y) = x₀y₁ − x₁y₀. **So C is self-dual iff U is Lagrangian for Ω.**
- **Weights.** Norm ≡ weight mod 3 on F₃⁴. The weight-4 elements of A are the 16 norm-1 elements outside Q₈, and the weight-1 elements are Q₈: SL₂(F₃) ≅ 2T = Q₈ ∪ {(±1 ± i ± j ± k)/2}, and 1/2 = −1 in F₃. The weight f₄ = Π φ(coordinates) is Q₈-bi-invariant and takes opposite signs on the two nontrivial cosets, so **f₄(X) = φ(ψ(X)) with ψ: SL₂(F₃) → ℤ/3 the abelianisation** (and f₄ = 0 off SL₂∖Q₈).
- [V: `mainq_morita.py` checks ψ is a homomorphism and f₄ = φ∘ψ; J, K, h are automorphisms of F₃² ⊗ U with J² = K² = −1, JK = −KJ.]

**Corollary 9.2 (index via good planes) [P; V].** Call X ∈ C an SL₂-word if every block X_b ∈ SL₂(F₃). Left multiplication by SL₂(F₃) preserves C, acts freely on SL₂-words, and shifts every ψ_b by ψ(g). Hence
      **Index(C) = 8 Σ_Π Σ_{s∈F₃} Π_b φ(ψ_b(Π) + s),**
with Π running over the SL₂-orbits of SL₂-words ("good planes" of U), each represented by its unique basis with X_{b₀} = 1. The same holds for R_σ of [I Lemma 5.8] when σ consists of Q₈-orbit blocks, with φ replaced on σ by the λ-weight, which is (−2, 1, 1) as a function of ψ (weight 1 ⇔ X_b ∈ Q₈).
- `ternary60 sl2words` enumerates normalised SL₂-words: x₁ runs over an affine subspace of U of dimension r − 2, and x₂ is found by linear algebra. At n = 72 there are about 5.8·10⁶ good planes and a run takes 5 s. Direct enumeration (3³⁶ words) is impossible there, and `ternary60 index` gives only |Index|.
- [V: `mainq_72rule.py` Part 1] sign-exact agreement with `rsigma` for the index and random orbit-block R_σ, n = 12, 24, 36 (18/18). At n = 72, |Index| agrees with `ternary60 index`.

### 9.2 Adding h: modules over R = F₃[ℤ/3]

h permutes the blocks in triples (3s + t ↦ 3s + t + 1). So F₃^{2r} = F₃^{2k} ⊗ R with R = F₃[t]/(t³ − 1) = F₃[u]/u³, u = t − 1. **G-invariant self-dual codes ↔ Lagrangian R-submodules U**, of type R^α ⊕ (R/u²)^β ⊕ (R/u)^β with α + β = k.
- **Free U (β = 0) [P].** U = R·{e_i + u(A₁f)_i + u²((A₁ + S)f)_i}. Here Ū = span(e) is a Lagrangian of F₃^{2k}, f is a dual Lagrangian basis, A₁ is skew and S symmetric. This is the Hermitian condition for t ↦ t⁻¹, which acts by u ↦ −u + u². The collapsed fixed code is F₃² ⊗ Ū, so **T_h = Index(F₃² ⊗ Ū)**, and T_h ≠ 0 needs 3 | k.
- **Non-free U (β ≥ 1) [P].** The collapsed fixed code D is co-isotropic with dim D − 2k = 2β, so Poisson gives **T_h = 9^β·F(D^⊥) ∈ 72ℤ**, using 8 | F(D^⊥) from the free Q₈-action.
- **Gauge symmetries [P].** h_s (multiplication by t on triple s only) is a coordinate permutation that maps U to another lift of Ū, with A₁ ↦ A₁ + B_s, B_s = ω_s|_Ū. The reflection t ↦ t⁻¹ gives A₁ ↦ −A₁. Both preserve Index and T_h.

### 9.3 Exact laws for the index mod 72 [V: `mainq_72rule.py` Parts 2–3]

Write a := Index/24 mod 3 and t := T_h/24.
- **k = 1** (all 12 free lifts): Index = 24·S. So S = 0 gives the tetracode³ and S = ±1 gives the Golay code.
- **k = 2** (all 40 × 81 free lifts): a ≡ −A₁² if Ū = ℓ₁ ⊕ ℓ₂ is split (collapsed code = two tetracodes), and a ≡ 0 otherwise.
- **k = 3** (480 sampled lifts over 12 random Ū): **a ≡ t·A₁(P)²**. Here P ⊂ Ū is the plane spanned by the three lines Ū ∩ {zero on block s} (Golay type, t = ±1), and a ≡ 0 when t = 0.
  - A₁(P)² ∈ {0, 1} is well defined, and A₁(P) is exactly the gauge invariant of A₁: span(B_s) is the annihilator of P.
  - This is the 72-rule for free U at n = 36, sign-exact: Index ≡ T_h·A₁(P)² mod 72.
  - Non-free U had T_h ≡ Index ≡ 0 mod 72 in every sample.
- **k = 6: the rule fails** (Part 4). Among 30 random codes, 5 have T_h ≡ 0 but Index ≢ 0 mod 72, e.g. T_h = 0 with Index = −3840 (saved as `ternary60/codes/q8z3_len72_T0.txt`, U in `….U.txt`; |Index| re-checked with `ternary60 index`). Non-free U again always had Index ≡ 0 mod 72 [C for all k].
- Proofs of the k = 3 law (and of "β ≥ 1 ⇒ 72 | Index") are open. They are no longer needed for the Main Question.

### 9.4 Back to k ≡ 0 mod 24: seeds at k = 6

Consider a G-equivariant chain (Lemma 4.1 with G = Q₈ × ⟨h⟩) seeded at k = 6 with a G-stable system σ of b₀ = 6 Q₈-orbit blocks (two h-triples). It reaches k = 12, 24, 36, … and so every k ≡ 0 mod 24. Along it, Index = R_σ(seed) [I Lemma 5.8] and T_h = R_σ̄(D) (Lemma 4.3).
- **What is needed:** a G-invariant self-dual code of length 72 and two h-triples σ with R_σ = ±24 and R_σ̄(D) = 0. Then the orbifold by Q₈ × ℤ/3 would have index 1 at every k ≡ 0 mod 24, which would answer the last open class.
- b₀ = 18 (every orbit a block, straight to k = 24) is hopeless: |R_σ| ~ 10⁷–10⁸.
- [V] Pipeline check in the Morita layout: from k = 3 seeds and one h-triple, |Index(Q_σ E)| = |R_σ(E)| and T_h(Q_σ E) = R_σ̄(D) at n = 72.
- **Search** [V: `mainq_q8z3_seed72.py`, log beside it; longer exploratory runs in the session scratchpad].
  - Random free codes: about 2.5 of the 15 systems per code have R_σ̄(D) = 0, and on those R_σ is spread over {0, 24, 48} mod 72. So nothing forces 72 | R_σ, unlike at k = 3.
  - The magnitudes are large, typically |R_σ| ~ 10⁴–10⁵.
  - Targeted: reductions Ū whose collapsed code has R_σ̄ = 0 for all 15 systems, with random lifts (A₁, S). This makes every system admissible, about 3 s per code.
  - Split Ū (collapsed code = six tetracodes) is useless: there all R_σ ≡ 0 mod 72, as at k = 3.
  - **A seed was found (§10)** after about 7000 targeted systems (466 lifts over 14 reductions), consistent with the heuristic density ~2·10⁻⁴ of |R_σ| = 24.

--------------------------------------------------------------------------------------------

## 10. The Main Question for k ≡ 0 mod 24 (2026-09-26, later session) [V: `mainq_q8z3_chain24.py`, log beside it]

**Seed [V].** `ternary60/codes/q8z3_seed72.U.txt`: a Lagrangian U ⊂ F₃³⁶, h-invariant and free over R. E = F₃² ⊗ U (length 72, `q8z3_seed72.txt`) is self-dual, with G = Q₈ × ⟨h⟩ ⊂ Aut(E) as in §9: J² = K² = −1, JK = −KJ, h³ = 1 commuting with J, K, and h of cycle shape 3²⁴.
- Index(E) = −1608 (sl2words, sign-exact; |Index| confirmed by `ternary60 index`). T_h(E) = 0.
- σ = the six Q₈-orbit blocks of h-triples 0 and 1. **R_σ(E) = +24**: sl2words with normalisation block 0, with block 9, and by the older enumeration all agree.
- **Independent second computation (2026-09-27) [V: `mainq_e72_infoset.py`, log beside it].** `rsigma_is` (`ternary60/src/bin/rsigma_is.rs`, no code shared with sl2words) sums the definition of R_σ over an information set: φ(0) = 0 leaves 2³⁶ sign patterns on the 36 information coordinates outside σ, walked in Gray-code order, ≈ 1 min on 4 threads. It uses no Morita form and no symmetry. It gives **R_σ(E) = +24** and Index(E) = −1608, sign-exact. It agrees with sl2words on four further block systems of E (values −7944, +132792, +68664, −7896) and on a random monomial copy of E with the sign flipped. It also agrees with sl2words and with full enumeration on 4 random Q₈ × ℤ/3-invariant codes at n = 36 × 6 systems, and with brute force on 292 small codes (random, rank-deficient, and random self-dual).
  - A code review found no error in it. The reviewer also wrote a third evaluator, `rsigma_mitm` (reverse pivot order, a 2²⁰-word table instead of the Gray walk), which also gives R_σ(E) = +24 and Index(E) = −1608.
- **R_σ̄(D) = 0** on the collapsed fixed code D (length 24, self-dual), by direct enumeration (rsigma, independent of sl2words).

**Theorem 10.1 [P, given T*: GJF Thm 4.2 (orbifolds by non-anomalous groups; fermionic case sketched, ORB); T: their Frame-shape anomaly for ℤ/3; I Lemma 5.8, Thm 5.9; Lemma 4.1, 4.3; Thm 8.1; V].** For every k ≡ 0 mod 12 with k ≥ 12 there is a self-dual ternary code C_k of length 12k with Index(C_k) = 24, G = Q₈ × ℤ/3 ⊂ Aut(C_k) of the type above (J² = K² = −1, h fixed-point-free of cycle shape 3^{4k}), and T_h(C_k) = 0. For k ≡ 0 mod 24, V_{Λ(C_k)}//G is a holomorphic N=1 SVOA of central charge 12k and **index 1**. So the Main Question has a positive answer for gcd(k, 24) = 24.
- *Construction.* Lemma 4.1 with G, starting from (E, σ) and refining the G-orbit of one step-1 block at each step (12 blocks, +12 in k). Lengths are 72 + 72 = 144 (k = 12), then 288 (k = 24), 432, …; k runs over all multiples of 12 from 12 on.
- *Invariants.* Index(C_k) = R_σ(E) = 24 at every step [I Lemma 5.8]. T_h(C_k) = R_σ̄(D) = 0 (Lemma 4.3), with the collapsed systems carried along in the same way.
- *Anomaly.* It vanishes for 24 | k: the Q₈ part is 3k·a = 0 since 8 | k (Thm 8.1); the ℤ/3 part is zero since 3 | k (GJF); mixed terms vanish by coprimality.
- *Twisted sectors.* Every abelian subgroup of G is cyclic. Those containing −1 have vanishing twisted–twined indices, since −1 fixes no maximal codeword; the only other nontrivial one is ⟨h⟩, with T_h = 0. So the index is Index(C_k)/|G| = 24/24 = 1. The orbifold is N=1 because G fixes the supercurrent. □ Detailed proof: `notes/orbifold-index.md` (Theorem O).
- [V: `mainq_q8z3_chain24.py`, log beside it]
  - At n = 144 and n = 288: self-duality, J, K, h ∈ Aut, the relations, and h fixed-point-free.
  - At n = 144: T_h = 0 directly (`ternary60 index` on the collapsed fixed code, length 48).
  - Index = 24 at n = 144, 288 is by [I Lemma 5.8]; direct computation is out of reach (3⁷² words; sl2words would need 3³⁴ steps).
  - Codes: `ternary60/codes/q8z3_chain_len{144,288}.txt` (+ `.gens.txt`).

**Corollary 10.2 (the Main Question) [P, given the same T, T* (ORB) and I].** Together with §2, §4 and §8: **for every k ≥ 1 there is a holomorphic N=1 SVOA of central charge 12k and index 24/gcd(k, 24)**, the TMF minimum. The sources by residue class:
- gcd(k, 24) ∈ {1, 2}: [I Thm 5.9], with g = 1 or −1.
- gcd = 4: the J-chain (Thm 4.2).
- gcd ∈ {3, 6, 12}: the ℤ/12-chains (Thm 4.4).
- gcd = 8: the Q₈-chain (Cor 8.2).
- gcd = 24: the Q₈ × ℤ/3-chain (Thm 10.1).
- *TMF.* For k = 24 (c = 288, index ±1) the SVOA represents, under Stolz–Teichner, a unit of π₅₇₆TMF: the periodicity class Δ²⁴ up to torsion (`notes/tmf-context.md`, last section).
- *Caveats.* This relies on GJF's orbifold and anomaly theorems, on Thm 8.1, and on [I] (not yet independently read). Thm 8.1 has two proofs. One uses the coprime-gauging lemma (§8.2). The other (§8.4–8.5) uses only cited standard theorems: S-invariance of holomorphic SVOA characters, lattice twisted modules, the rSH³ layer bound, and additivity of anomalies.

--------------------------------------------------------------------------------------------

## 11. Simpler seeds (review of 2026-09-28, `paper/review-2026-09-28.md` §5 S4)

Two experiments of the review; every number below was re-checked with fresh code in `ternary60/theory/review_seed_verify.py` (log beside it).

**11.1 gcd(k,24) ∈ {3, 6} from GJF's own k = 3 code [V: `review_gjf36_z6.py`, `review_seed_verify.py`].** E = `gjf_ex57_len36` (GJF Ex 5.7), h = the plain shift by 12, G = ℤ/6 = ⟨−h⟩ (Aut(E) = ⟨−1, h⟩ exactly, §3).
- Index(E) = +24, T_h(E) = 0, dim E^h = 6; the collapsed fixed code is GJF's printed length-12 code (self-dual, index 0).
- h moves every block, so every block stabiliser in ⟨−h⟩ is {±1} (type τ₀ of [EQ] Lemma 4.11): placements and splits are transported along h-orbits, and no split rule is needed.
- 3-block systems {β, hβ, h²β}: all 13,365 enumerated; 803 have R_σ(E) = ±24 and R_σ̄(D) = 0 (7.2%; seed 3 of §4 had 2 of 45). 6-block systems: 1.50% of a uniform sample of 2,000 admissible ones.
- σ_A = {(0,25|2,5), (12,1|14,17), (24,13|26,29)}: R = +24, twined 0; chain A (k = 6, 12, 18, …), Index +24 with no sign flip. At n = 72: self-dual, −h ∈ Aut, T_h = 0 (enumeration), Index = +24 sign-exact. A control system with R_σ̄(D) = −48 gives T_h = −48 at n = 72 (Lemma 4.3, sign-exact).
- σ_B = {(2,15|28,21), (14,27|4,33), (26,3|16,9), (5,6|31,10), (17,18|7,22), (29,30|19,34)}: R = +24, twined 0; chain B (k = 9, 15, 21, …). At n = 108: self-dual, invariant, T_h = 0.
- Both chains checked one step further (n = 144, 180). Codes: `ternary60/codes/gjf36_z6chain_len{72,108}.txt` (+ `.gens.txt`).
- m = 3 uses h, m = 6 uses −h. **gcd(k,24) = 12 then comes from the Q₈ × ℤ/3-chain of §10 with g = Jh**: order 12, g⁶ = J² = −1, g⁴ = h (shape 3^{n/3}, T_h = 0), Index +24, so GJF Thm 5.6 applies as it stands. So the searched ℤ/12 seeds (`z12seed_len36_*`) are not needed.

**11.2 gcd(k,24) ∈ {4, 8} from the Golay code [V: `review_golay_q8.py`, `review_seed_verify.py`].**
- Aut(Golay) has 792 elements J with J² = −1 and 1320 subgroups Q₈ = ⟨J, K⟩ (J² = K² = −1, KJ = −JK), one conjugacy class; each acts through a free Klein four-group with three coordinate orbits of size 4.
- **The three Q₈-orbits never work: R_σ(Golay) = +72 for every Q₈** [P]. For a partition into three 4-sets, R_σ = 24 − 48 + 8H (weight 12: +24; weight 9: each 3-set is the zero set of two words, −2·2·12 = −48; weight 6: +8 per hexad containing one block and meeting the others once). A hexad through an orbit meeting another orbit in {x, y} would be stable under the t ∈ Q₈ swapping x, y, so t·c = ±c and t² = −1 gives c = −c. Hence H = 12. (The 1320 orbit partitions are exactly the R = 72 class among the 5775 partitions, cf. §5.1(f″) of [I].)
- **A mixed system works:** σ = {(0,1|2,3), (4,5|11,10), (6,7|8,9)} with J = ((1,0,3,2,5,4,7,6,9,8,11,10), (−,+,−,+,+,−,−,+,+,−,−,+)) (the J of §4) and K = ((2,3,0,1,6,7,4,5,11,10,9,8), (−,+,+,−,−,−,+,+,+,−,+,−)): one orbit block (type τ_Q) and two blocks made of a J-pair from each remaining orbit (type τ_J, swapped by K). Q₈-stable, R_σ(Golay) = −24.
- The Q₈-chain from it: n = 48 (k = 4) self-dual, Q₈-invariant, Index = −24 sign-exact, next system R = −24; n = 96 (k = 8) passes the structural checks; it continues through all k ≡ 0 mod 4. One diagonal sign change gives +24. Codes: `ternary60/codes/golay_q8chain_len{48,96}.txt` (+ `.gens.txt`).
- This replaces the random length-24 seed of §5 and, since J ∈ Q₈, the J-chain of Thm 4.2.
- The centraliser of each Q₈ in Aut(Golay) is S₃ × ⟨−1⟩ and contains h of order 3 without fixed coordinate, T_h = 0: Golay carries Q₈ × ℤ/3. Not usable for 24 | k (chains from Golay have k ≡ 1 mod 3, and h preserves no mixed system).

**11.3 Consequence.** Seeds: Golay (gcd 1, 2, 4, 8), GJF's k = 3 code (gcd 3, 6), E₇₂ (gcd 12, 24). Only E₇₂ comes from our own search. The Lean formalization (Tier A) uses the older seeds and need not change; the certificates for GJF's code would be larger than those of seed 6.
