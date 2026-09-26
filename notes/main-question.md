# The GJF Main Question: holomorphic N=1 SCFTs of minimal index from ternary codes

Working notes, started 2026-09-26. Companion to `notes/ternary-code-index.md` (cited as **[I]**; e.g. [I §5.1(f‴)] is the partial-quadrupling section). Status labels as there: [P] proved here, [V] exact computation (script cited), [T] cited theorem, [C] conjecture, [H] heuristic.

GJF = Gaiotto, Johnson-Freyd, *Holomorphic SCFTs with small index*, arXiv:1811.00589 (numbering of arXiv v1; `scripts/fetch_gjf_source.sh` downloads the TeX). Scripts live in `ternary60/theory/mainq_*.py` and write a `.log` beside themselves.

--------------------------------------------------------------------------------------------

## 0. Summary

- **GJF's Main Question** asks for a holomorphic N=1 VOA with c = 12k and index 24/gcd(k,24) for every k. GJF answer k ≤ 5, via Thm 5.6: orbifold the code VOA V_{Λ(C)} of an index-24 code C by an automorphism g of order m = gcd(k,24) with (1) g^{m/2} = −1 and (2) g^{m/3} a balanced fixed-point-free order-3 map (§1).
- **Answered here for every k with 8 ∤ k** (§2, §4), modulo GJF Thm 5.6 [T] and [I Thm 5.9]; previously k ≤ 5.
  - gcd(k,24) ∈ {1, 2}: any index-24 code from [I], with g = 1 or g = −1 (Cor 2.1).
  - gcd(k,24) = 4: a J-equivariant version of [I]'s construction, seeded by J ∈ Aut(Golay) with J² = −1 (Thm 4.2).
  - gcd(k,24) ∈ {3, 6, 12}: a ℤ/12-equivariant version, seeded by one length-36 code found by GJF's search method; the twined count of the order-3 part is carried along by Lemma 4.3 (Thm 4.4).
- **Our [I Thm 5.9] codes as they stand** (§3): the length-48 code satisfies Thm 5.6 (it has J with J² = −1); the lengths-36 and 72 codes do not (their automorphism groups are 2-groups). So the symmetry has to be built in, which §4 does.
- **Obstruction** (§5): if g ∈ Aut(C) has g⁴ = −1 then 48 | Index(C). So Thm 5.6 can never be applied when 8 | k (m ∈ {8, 24}). The proof uses a new Hermitian four-code identity (◇). The quaternion group Q₈ escapes the obstruction and would give index 3 if its action is non-anomalous [C].
- **Open**: k ≡ 0, 8, 16 mod 24 (needs a non-cyclic group such as Q₈, or another idea); an independent check of GJF's anomaly analysis is not attempted here.

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

Conventions. A block is a 4-tuple (a, b, c, d) read with the pair split {a, b}, {c, d}; the step-1 blocks of Q_σ are (a, a*, b, b*), (c, c*, d, d*), and refining a step-1 block B with a split {w, x}, {y, z} gives (w, w**, x, x**), (y, y**, z, z**). Lemma 5.6 and Lemma 5.8 of [I] hold for every choice of splits ([I §5.1(f″)], `paper_check.py`).

**Lemma 4.1 (equivariant quadrupling) [P].** Let G ⊂ Aut(E) ⊂ 2^m:S_m be a finite group that permutes the blocks of σ and maps split pairs to split pairs. Extend each g ∈ G to the new coordinates by letting a Hadamard partner follow its partner with the same sign: g(e_x) = s e_{g·x} ⇒ g(e_{x*}) = s e_{(g·x)*} (same at step 2). Suppose the tetracodes are placed G-equivariantly (on one block per G-orbit a placement invariant under the stabiliser, elsewhere its transport). Then:
1. G acts faithfully on F₃^{m+12b} and G ⊂ Aut(Q_σ(E)).
2. Orders, the relation g^j = −1, and cycle lengths are inherited: a new coordinate lies in a cycle of the same length as its partner.
3. If the refined set of step-1 blocks is G-stable and its splits are chosen G-equivariantly, σ″ is again G-stable, so the construction iterates.
- *Proof.* On a Hadamard pair (x, x*) the map (u, v) ↦ (u + v, u − v) commutes with the scalar s, so each step-1 and step-2 Hadamard map commutes with G. E ⊕ T₁^b ⊕ T₂^{2b} is G-invariant by hypothesis, hence so is its image Q_σ(E). Items 2–3 are immediate from the definition of the extension. □
- *When do invariant placements exist?* The stabiliser G_β acts on the new block β* as it acts on β, by signed permutations. A tetracode placement invariant under G_β exists iff that image lies in a conjugate of Aut(tetracode) ≅ GL₂(F₃) inside 2⁴:S₄ (8 conjugates = 8 placements). For the cases used here: J with J² = −1 acting as a double transposition (an element of Q₈ ⊂ GL₂(F₃)) — yes; a fixed-point-free order-3 map never stabilises a block (4 is not a multiple of 3), so its blocks come in orbits of 3 and no condition arises. `placement_on` finds the placement.
- *Consequence for k mod 3.* If an element of order 3 lies in G, every block orbit has size divisible by 3, so b ≡ 0 mod 3 and k mod 3 is invariant along a G-chain. Order-3 chains need a seed with 3 | k.

**Theorem 4.2 (m = 4) [P, given T: GJF Thm 5.6; V].** For every even k there is a self-dual ternary code of length 12k with Index ±24 and an automorphism J with J² = −1 whose coordinate cycles are all 2-cycles. Hence the Main Question has a positive answer for gcd(k,24) = 4.
- *Construction.* J ∈ Aut(Golay) with J² = −1, cycle shape 2⁶ (one of 792). The block β = (0,1,2,3) is J-stable with J-stable pairs {0,1}, {2,3}, and R_β(Golay) = 24 (as for all 495 blocks, [I Thm 5.9]). Apply Lemma 4.1 with G = ⟨J⟩ and, at each step, refine one J-stable step-1 block with a J-stable split; σ″ is again two J-stable blocks. Lengths 12 + 12 + 24j, i.e. every even k; Index = 24 by [I Lemma 5.8].
- *Theorem 5.6.* For k ≡ 4 mod 8 with 3 ∤ k, m = 4 = ord J and J^{m/2} = J² = −1; condition 2 is empty. So V_{Λ(C)}//⟨J⟩ has index 6.
- [V: `mainq_jchain.py`, log beside it] J-invariance, J² = −1, cycle shape 2^{n/2} and self-duality at n = 24, 48, 72, 96, 120, 144; Index = 24 sign-exact at n = 24, |Index| = 24 (Rust) at n = 48, 72. Codes `ternary60/codes/jchain_len<n>.txt`, J in `jchain_len<n>.J.txt`.

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
| 8, 16 | 8 | 3 | cyclic route impossible (Thm 5.1); Q₈-invariant index-24 codes exist (Q₈ chain), orbifold index 3 if non-anomalous | [C] |
| 0 | 24 | 1 | cyclic route impossible (Thm 5.1); Q₈ × ℤ/3 route open | [C] |

"[P]" here means: proved here given GJF Thm 5.6 [T] (including its anomaly analysis) and [I Thm 5.9] (not yet independently read).

Verification [V]:
- `mainq_jchain.py` (log): J-chain n = 24 … 144.
- `mainq_z12chain.py` (log): chain A (σ₃, b₀ = 3): seed Index = +24, T_h = 0, R_σ₃ = −24, R_σ̄₃(D) = 0; n = 72 (k = 6): g-invariant, ord g = 12, g⁶ = −1, 6-cycles, |Index| = 24 (Rust), T_h = 0 by enumeration; n = 144 (k = 12): same with T_h = 0 by enumeration (3²⁴ words, Rust) and Index = −24 by [I Lemma 5.8]. Chain B (σ₆, b₀ = 6): R_σ₆ = −24, R_σ̄₆(D) = 0; n = 108 (k = 9): invariance and T_h = 0 by enumeration.
- `mainq_seed_search.py` (log): the seed search (8 of 300 random g-invariant codes are seeds; Index 0 is the most common value) and the good block systems (R_σ = ±24, R_σ̄(D) = 0): seed 3 has 2 of 45 (b = 3) and 3 of 405 (b = 6); seed 4 has 5 of 45 and 2 of 405. (Exploratory runs found 2–3 good b = 6 systems on seeds 1 and 2 as well.)
- `mainq_obstruction.py` (log): Theorem 5.1 and (◇).
- `mainq_q8chain.py` (log): the Q₈ chain n = 24, 48, 96.
- `mainq_automorphisms.py` (log, needs nauty): §3.
- The four-code identity and Lemma 4.3 are local/Poisson identities; all numerics are sign-exact where stated (Rust `rsigma` enumerates the code, no sign normalisation).

## 7. Remarks and further directions

- **Nonzero twisted sectors [H].** If the twisted–twined RR indices of an order-3 h all equal T_h (no phases), then V//⟨h⟩ has index (Index(C) + 8T_h)/3, and similarly (Index + 8T_h)/m for m ∈ {6, 12} when g^{m/2} = −1. This would allow T_h ≠ 0 (e.g. Index = −168, T_h = 24). Consistent with Bantay's formula for cyclic permutation orbifolds of E³ ((I³ + 8I)/3) and with integrality: T_h ≡ 0 mod 3 whenever 3 | k (next item). Not needed for the results above.
- **Trace formula for T_h [P; V].** For h of order 3 (a permutation after a sign change) with a fixed and b 3-cycles, let π(C) be the code of orbit sums (fixed coordinates kept, each 3-cycle summed), N = a + b, d = dim π(C). Then the collapsed fixed code is π(C)^⊥, and Poisson gives **T_h = ±3^{N/2 − d} · i^N · F(π(C))**. Checked on all order-3 elements of Aut(Golay) (T = 6 for shape 3³1³, T = 0 for 3⁴) and of the length-24 chain code (`mainq_common.twined_count_trace`). For fixed-point-free h, N = 4k and π(C) ⊂ π(C)^⊥ = D is self-orthogonal, so d ≤ 2k. If d < 2k then T_h ∈ 2·3^{2k−d}ℤ (F(π(C)) is even, x ↔ −x); if d = 2k then D is self-dual and T_h = Index(D) ∈ 24ℤ when 3 | k. Either way T_h ≡ 0 mod 3 for 3 | k.
- **Fixed points.** An order-3 element with fixed coordinates cannot stabilise a block with an invariant split (a 3-cycle on 4 points preserves no perfect matching), so it gives nothing new for the chains.
- **Literature.** GJF is the only source found for the Main Question; the citation search of [I §5.1(f‴)] is still open, and the same caveat applies here.
