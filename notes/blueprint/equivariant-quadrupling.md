# Blueprint: partial quadrupling, its equivariance, and collapsed fixed codes

Proof file, 2026-09-27. Purpose: give Lean-ready proofs of the code-level machinery behind the answer to GJF's Main Question. It covers:
- **[I] Lemma 5.8** (Index(Q_σ E) = R_σ(E), R_σ''(Q_σ E) = R_σ(E)) in the generality in which the Main Question uses it;
- **[MQ] Lemma 4.1** (equivariant quadrupling), including which tetracode placements exist and why the chains can be iterated;
- **[MQ] Lemma 4.3** (fixed codes collapse: T_h(Q_σ E) = R_σ̄(D)).

Every definition is explicit, every step is proved, and each statement is marked as a finite check (kernel `decide`) or as needing a structural proof or induction. The existing formalization `lean/GJF/Existence.lean` is the reference for names; Remark 3.5 and §7 say what it already covers.

Sources: [I] = `notes/ternary-code-index.md` (§5.1(f‴)); [MQ] = `notes/main-question.md` (§4, §8, §10); [OI] = `notes/orbifold-index.md`; [Lean] = `lean/GJF/Existence.lean`; paper = `paper/index24.tex` (Lemmas A, B, main lemma). Status labels: [P] proved in this file, [V] exact computation (script cited), [T] cited theorem, [Lean] already formalized.

Script: `ternary60/theory/blueprint_equivariant.py` (stdlib Python plus the Rust binary), log `blueprint_equivariant.log` beside it. Parts 1–8 are cited below as [V: Part n].

--------------------------------------------------------------------------------------------

## 0. Summary for the formalizer

| # | statement | status | kind of proof | in [Lean]? |
|---|---|---|---|---|
| 1.5 | tetracode placements = the 8 self-dual codes in F₃⁴ = the [4,2,3] codes; Mon(T) ≅ GL₂(F₃) | [P; V] | finite | no (only the fixed `Tfin`) |
| 2.1, 2.2 | Lemmas A, B for **every** placement and every split | [P; V] | finite (`decide`) | only `Tfin`, standard split |
| 3.3 | Q_σ self-dual; F(Q_σ E) = R_σ(E); R_σ''(Q_σ E) = R_σ(E) for any linear E, any refined set 𝓑, any splits, any placements | [P; V] | structural (sum manipulation) | only `Tfin`, one refined block, canonical splits |
| 4.3–4.8 | extension g ↦ ĝ is an injective homomorphism commuting with both Hadamard layers; G ⊂ Aut(Q_σ E); orders, relations, signed cycle data inherited; refinement stability | [P; V] | structural | no |
| 4.9, 4.10 | which stabilisers admit invariant placements (steps one and two) | [P; V] | finite | no |
| 4.11 | local types τ₀, τ_J, τ_Q propagate, so every stage has invariant placements | [P; V] | structural + finite | no |
| 5.2–5.7 | sign normalisation; c(Q_σ(E)^ĥ) = Q_σ̄(D); T_h = R_σ̄(D₀) along a chain | [P; V] | structural + induction | no |
| 6.1 | the equivariant engine (all four chain families) | [P; V] | induction on the step | no |

**Issues found**: see §9. None of them breaks a result. The main points:
- Lemma 4.1(3) of [MQ] ("so the construction iterates") omits the placement condition at later stages.
- The σ''-splits must be re-chosen (Lemma 4.11). With the default splits written in [MQ] §4, the step size doubles, and the ℤ/12-chains would miss k ≡ 6, 9, 18, 21 mod 24.
- Lean's fixed tetracode `Tfin` is not invariant under the J-chain's J.

--------------------------------------------------------------------------------------------

## 1. Definitions

**Definition 1.1 (weights).** F = F₃ = `ZMod 3`.
- φ: F → ℤ, φ(0) = 0, φ(1) = −1, φ(2) = +1 (`phi`). φ is odd, φ(−a) = −φ(a), and φ³ = φ.
- For a finite set Z and x ∈ F^Z: wt(x) = #{z : x_z ≠ 0}, and f(x) = ∏_{z∈Z} φ(x_z) (`fG`).
- For a linear code C ⊂ F^Z: F(C) := Σ_{x∈C} f(x) (`indexG C`; defined for every linear C). For self-dual C this is GJF's Index(C) = #even − #odd maximal codewords.
- λ: {0,…,4} → ℤ, λ = (0, −2, 0, 0, 1) (`lam`).
- ψ(a, b) := φ(a+b)·φ(a−b) ∈ {0, ±1}. It is nonzero iff exactly one of a, b is nonzero, with ψ(a, 0) = 1 and ψ(0, b) = −1 [V: Part 2].
- κ(a, b) := wt(a+b, a−b) ∈ {0, 1, 2}. It is 2 if exactly one of a, b is nonzero, 1 if both are, and 0 if a = b = 0.

**Definition 1.2 (signed permutations).** Mon(Z) = {g = (π, s) : π ∈ Sym(Z), s: Z → {±1}}, acting on F^Z by (g·x)_{π(i)} = s_i x_i. This is GJF's 2^|Z|:S_|Z| and the convention of `mainq_common.mono_apply`.
- A *diagonal* element has π = id; −1 := (id, −1).
- Aut(C) := {g : g·C = C}.

**Lemma 1.3 [P].** f(g·x) = (∏_i s_i)·f(x). Hence F(g·C) = (∏ s)·F(C), and F(C^g) is defined for every g.
- *Proof.* f(g·x) = ∏_i φ(s_i x_i) = ∏_i s_i φ(x_i), since φ is odd. □

**Definition 1.4 (tetracode placement).** A *placement* on a 4-element set Y is a self-dual code T ⊂ F^Y (dot product). The standard one is T₀ = ⟨(1,1,1,0), (0,1,2,1)⟩ on Y = {0,1,2,3} (`Tfin` / `inT`, positions (a,b) ↦ 2a+b). Mon(T) := {g ∈ Mon(Y) : gT = T}.

**Lemma 1.5 (the placements) [P; V: Part 1].**
- (a) The placements on Y are exactly the [4,2,3] codes, and there are exactly 8. They form one Mon(Y)-orbit, the orbit of T₀.
- (b) Each 3-subset Z ⊂ Y supports exactly one line {0, ±w_Z} of a placement T. The nonzero words of T are these 8 vectors.
- (c) Mon(T) has order 48 and meets the diagonal in {±1}. Its permutation image is all of S₄, and Mon(T) ≅ GL₂(F₃) via its action on T ≅ F₃². The permutation action of Mon(T) on Y corresponds to the action of PGL₂(F₃) on the 4 lines of T, with coordinate i ↔ the line supported on Y ∖ {i}.
- (d) Mon(T) is self-normalising in Mon(Y) (order 384). So the 8 placements have 8 distinct stabilisers ("8 conjugates = 8 placements", [MQ] Lemma 4.1).
- (e) The 8 placements form two rulings of 4. Two distinct placements meet in 0 if they lie in the same ruling and in a line if not.

*Proof.*
- (a) A self-dual T has dim 2 and all its words are isotropic, so their weights are ≡ 0 mod 3, i.e. 0 or 3. Conversely, if all nonzero weights of T are 3, then T is isotropic: x·x = wt x = 0, and 2x·y = (x+y)·(x+y) − x·x − y·y = 0. [V] Of the 130 planes in F₃⁴, 8 are self-dual; they are exactly the [4,2,3] codes and exactly the orbit of T₀.
- (b) If two independent words were supported in one 3-set Z, their span would be a 2-dimensional subspace of F^Z ≅ F₃³. Every plane in F₃³ meets the plane {x_z = 0} (any z ∈ Z) in at least a line, so it contains a nonzero vector of weight ≤ 2, contradicting (a). So each 3-set carries at most one line, and 8 nonzero words = 4 lines fill all four 3-sets.
- (c) Kernel of Mon(T) → S₄: a diagonal d with dT = T maps w_Z to ±w_Z, so d is constant on each 3-set Z, hence constant: d = ±1.
  - By (a), |Mon(T)| = 384/8 = 48, so the image has order 24, i.e. it is all of S₄.
  - Restriction Mon(T) → GL(T) is injective: an element fixing T pointwise fixes every w_Z, hence every 3-set, hence π = id and then s = 1. Since |GL₂(F₃)| = 48, this is an isomorphism.
  - The coordinate/line correspondence is (b).
  - [V] The element orders are {1:1, 2:13, 3:8, 4:6, 6:8, 8:12}, those of GL₂(F₃); the binary octahedral group has only one involution.
- (d), (e) [V: Part 1]: the normaliser has order 48; the pairwise intersections are 0 (12 pairs) or a line (16 pairs); the "meet in 0" classes have sizes 4, 4. □
- *Lean.* Enumerate the 8 placements explicitly: `plc : Fin 8 → Finset (P → F)`, e.g. images of `Tfin` under 8 explicit monomial maps. Self-duality/isotropy and |plc i| = 9 then hold by `decide`. The classification (a) is not needed; any family of placements drawn from `plc` suffices.

**Definition 1.6 (split block system).** On a finite set X, a *split block system* σ is a set of pairwise disjoint 4-subsets β (*blocks*), each with a *split* {π₁(β), π₂(β)} into two 2-subsets (*split pairs*).
- X_σ := ⋃β, and S(σ) := X ∖ X_σ are the *singletons*; b := |σ|.
- [Lean] `Blk S B = S ⊕ (B × P)`, P = Fin 2 × Fin 2: block β = {β} × P, with split pairs {(a,0), (a,1)} for a ∈ Fin 2. Any other split is realised by relabelling P (`blockEquiv`-style, per block).

**Definition 1.7 (block weight).** For x ∈ F^X,
  w_σ(x) := ∏_{i∈S(σ)} φ(x_i) · ∏_{β∈σ} λ(wt(x|_β)),   R_σ(C) := Σ_{x∈C} w_σ(x).
- [Lean] `Rw`, `R`.
- R_∅ = F. R_σ depends on the blocks as sets, not on the splits.
- w_σ is invariant under any g ∈ Mon(X) that maps S(σ) to itself with ∏_{S} s = 1 and permutes the blocks (λ∘wt is invariant under signed permutations of a block).

**Definition 1.8 (quadrupling data and Q_σ).** Let E ⊂ F^X be linear and σ a split block system.
- *Oriented Hadamard map.* For distinct coordinates (x, y), h_{x,y}: (v_x, v_y) ↦ (v_x + v_y, v_x − v_y), the identity elsewhere. Since 2 = −1 in F, h_{x,y}² = −1 on the pair, so h_{x,y} is bijective.
- *Step one.* X' := X ⊔ X_σ*, with X_σ* = {x* : x ∈ X_σ} a disjoint copy, and β* := {x* : x ∈ β}. Put H₁ := ∏_{x∈X_σ} h_{x,x*}.
  - The *step-one blocks* are B_π := π ⊔ π* for each split pair π of σ. They form σ' (2b blocks), a block system on X' with X_{σ'} = X_σ ⊔ X_σ* and S(σ') = S(σ).
  - Its *canonical split* is {{p, p*}, {q, q*}} for π = {p, q}. The splits of σ' play no role in Q_σ.
- *Step two.* X̂ := X' ⊔ (X_{σ'})**, with (X_{σ'})** = {y** : y ∈ X_σ ⊔ X_σ*} and B** := {y** : y ∈ B}. Put H₂ := ∏_{y∈X_{σ'}} h_{y,y**}.
- *Placements.* T¹ = (T¹_β)_{β∈σ} with T¹_β a placement on β*, and T² = (T²_B)_{B∈σ'} with T²_B a placement on B**.
  - E ⊕ T¹ ⊕ T² := {v ∈ F^{X̂} : v|_X ∈ E, v|_{β*} ∈ T¹_β, v|_{B**} ∈ T²_B}.
- **Q_σ(E; T¹, T²) := H₂H₁(E ⊕ T¹ ⊕ T²) ⊂ F^{X̂}**, of length |X| + 12b. The intermediate code is E' := H₁(E ⊕ T¹) ⊂ F^{X'}.
- [Lean] `Φ e t` = H₁ on `Dbl S B = S ⊕ (B × (P × Fin 2))`, with (p, 0) = p and (p, 1) = p*. `D E` = H₁(E ⊕ T¹) with all T¹_β = `Tfin`. `E1 β₀ E` = E' regrouped by `r₁` (step-one block (β, a) has positions (b, s), canonical split by b). `Qc β₀ E` = Q_σ.

**Definition 1.9 (refinement).** Choose a set 𝓑 ⊂ σ' of step-one blocks and, for each B ∈ 𝓑, a split {ϖ, ϖ'} of B (any of the 3).
- σ'' := {ϖ ⊔ ϖ**, ϖ' ⊔ ϖ'** : B ∈ 𝓑}, a block system on X̂ with 2|𝓑| blocks.
- Its singletons are S(σ) ⊔ ⋃_{B∉𝓑}(B ⊔ B**).
- The splits of the σ''-blocks are **free data**: they enter the next Q_{σ''}, but not R_{σ''}. Two uniform choices for A = ϖ ⊔ ϖ** with ϖ = {y₁, y₂}:
  - *canonical*: {{y₁, y₁**}, {y₂, y₂**}}, as in [Lean] `r₂` and [MQ] §4 "(w, w**, x, x**)";
  - *transposed*: {{y₁, y₂}, {y₁**, y₂**}}.
- The *transposed refinement split* of B_π = {p, p*, q, q*} (π = {p, q}) is {{p, q}, {p*, q*}}; the canonical one is {{p, p*}, {q, q*}}.

--------------------------------------------------------------------------------------------

## 2. Local identities (finite checks)

Fix a 4-set Y, a placement T on Y, and u ∈ F^Y. For t ∈ F^Y write dbl(u, t) ∈ F^{Y×{0,1}} for (u_y + t_y, u_y − t_y)_y (`dbl`).

**Lemma 2.1 (Lemma A) [P; V: Part 2, 648/648; Lean: `localA` for T₀].**  Σ_{t∈T} ∏_{y∈Y} ψ(u_y, t_y) = λ(wt u).
- *Proof (paper Lemma A).* ∏ψ ≠ 0 iff supp t = Y ∖ supp u, and then the term is (−1)^{wt t}.
  - T has only weights 0 and 3, with two words on each 3-set (Lemma 1.5(b)).
  - So the sum is 1 if wt u = 4 (t = 0), 2·(−1)³ = −2 if wt u = 1, and 0 otherwise. □

**Lemma 2.2 (Lemma B) [P; V: Part 2, 1944/1944; Lean: `localB` for T₀ and the split by a].** For every split {ϖ₁, ϖ₂} of Y,
  Σ_{t∈T} λ(Σ_{y∈ϖ₁} κ(u_y, t_y)) · λ(Σ_{y∈ϖ₂} κ(u_y, t_y)) = λ(wt u).
- *Proof (paper Lemma B).* Write L(t) for the summand.
  - For t = 0, κ(u_y, 0) = 2[u_y ≠ 0], so L(0) = [wt u = 4].
  - For t ≠ 0, t vanishes at exactly one point z. Let z' be its partner in the split, and {x, y} the other pair. On {x, y} each κ ∈ {1, 2}, so λ(sum) = [u_x = u_y = 0]. On {z, z'} the sum is 2[u_z ≠ 0] + κ(u_{z'}, t_{z'}) with κ ∈ {1, 2}: it is 4 iff (u_z ≠ 0, u_{z'} = 0), and 1 iff (u_z = 0, u_{z'} ≠ 0).
  - So L(t) = [u_x = u_y = 0]·([u_z ≠ 0, u_{z'} = 0] − 2[u_z = 0, u_{z'} ≠ 0]). This vanishes unless wt u = 1.
  - If supp u = {w}: the two t vanishing at w give 2·1, and the two vanishing at w's partner give 2·(−2). Total −2 = λ(1). If wt u ≠ 1, only t = 0 contributes, giving [wt u = 4] = λ(wt u). □
- Both proofs use only Lemma 1.5(b), so they hold for all 8 placements and all 3 splits.
- *Lean (finite).* `∀ i : Fin 8, ∀ u, Σ_{t∈plc i} sgl (dbl u t) = lam (wtP u)` and `∀ i (sp : Fin 3) u, Σ_{t∈plc i} refdS sp (dbl u t) = lam (wtP u)` by `decide`. This is 32× the size of the present `localA`/`localB`.
  - Cheaper alternative: prove them from the T₀ versions by transport. For g = (π, s) ∈ Mon(Y): dbl(u, s·t) differs from dbl(u, t) only by swapping the two copies at coordinates with s_y = −1. `sgl` and each `refdS` are invariant under such swaps, and Σ_{t∈gT₀} G(dbl(u,t)) = Σ_{t∈T₀} G_{π}(dbl(u∘π, t)) with G_π the weight for the split π⁻¹(split). So Lemma B is needed for T₀ and all 3 splits only.

**Lemma 2.3 (weights on a doubled block) [P].** For v ∈ F^Y and t ∈ F^Y, with w = dbl(v, t) on Y ⊔ Y** (identify (y, 0) = y and (y, 1) = y**):
- f(w) = ∏_y ψ(v_y, t_y);
- for ϖ ⊂ Y, wt(w|_{ϖ⊔ϖ**}) = Σ_{y∈ϖ} κ(v_y, t_y).
- *Proof.* By definition of ψ and κ. □

--------------------------------------------------------------------------------------------

## 3. [I] Lemma 5.8 in the form used

**Lemma 3.1 (summation over one doubling layer) [P; Lean: `sum_D` for constant `Tfin`].**
- *Data.* L ⊂ F^{S ⊔ ⋃_{β∈σ} β} linear. Placements T_β on β* for each block. For each block, a weight G_β: F^{β⊔β*} → ℤ with Σ_{t∈T_β} G_β(dbl(u, t)) = λ(wt u) for all u ∈ F^β.
- *Claim.* Σ_{w∈H(L⊕T)} ∏_{i∈S} φ(w_i) ∏_β G_β(w|_{β⊔β*}) = R_σ(L), where H = ∏_{x∈X_σ} h_{x,x*}.
- *Proof.*
  1. (e, t) ↦ H(e, t) is a bijection L × ∏_β T_β → H(L ⊕ T). Injectivity is `pair_inj`: (a+c, a−c) determines (a, c), since 2 is invertible.
  2. H(e, t) equals e on S and dbl(e|_β, t_β) on β ⊔ β*.
  3. So the left side is Σ_{e∈L} ∏_S φ(e_i) · Σ_{t∈∏T_β} ∏_β G_β(dbl(e|_β, t_β)) = Σ_e ∏_S φ(e_i) ∏_β Σ_{t_β∈T_β} G_β(dbl(e|_β, t_β)), by distributivity (`Finset.prod_univ_sum`).
  4. By hypothesis this is Σ_e ∏_S φ(e_i) ∏_β λ(wt e|_β) = R_σ(L). □

**Lemma 3.2 (form transfer) [P; Lean: `block_sum`, `iso_D`].** For c ∈ F, write ⟨x, y⟩_c := ⟨x, y⟩_{S} + c⟨x, y⟩_{X_σ}, where ⟨,⟩_Y is the dot product summed over Y. If L is isotropic for ⟨,⟩_c and every T_β is isotropic, then H(L ⊕ T) is isotropic for ⟨,⟩_S − c⟨,⟩_{X_σ⊔X_σ*}.
- *Proof.* On one oriented pair, (a+b)(a'+b') + (a−b)(a'−b') = 2(aa' + bb') = −(aa' + bb'). Hence
  ⟨H(e,t), H(e',t')⟩_{X_σ⊔X_σ*} = −⟨e, e'⟩_{X_σ} − Σ_β t_β·t'_β = −⟨e, e'⟩_{X_σ}. The S-part is unchanged. □

**Theorem 3.3 (partial quadrupling) [P; V: Part 5, 60/60 on non-self-dual E with random placements and splits; Lean: special case].** Let E ⊂ F^X be **any** linear code, σ a split block system with b blocks, and T¹, T² any placements. Put Q := Q_σ(E; T¹, T²).
- (Q0) (e, t¹, t²) ↦ H₂H₁(e, t¹, t²) is a linear bijection E × ∏T¹ × ∏T² → Q. So dim Q = dim E + 6b and |Q| = |E|·3^{6b}.
- (Q1) If E is self-dual, then Q is self-dual (of length |X| + 12b).
- (Q2) F(Q) = R_σ(E).
- (Q3) For every 𝓑 ⊂ σ', every choice of refinement splits, and either convention for the σ''-splits: R_{σ''}(Q) = R_σ(E).

*Proof.*
- (Q0) H₁ and H₂ are bijective (Def 1.8), and the direct sum has dimension dim E + 2b + 4b.
- (Q1)
  - E self-dual ⇒ E is isotropic for ⟨,⟩_1 (the standard form).
  - Lemma 3.2 (c = 1): E' = H₁(E ⊕ T¹) is isotropic for ⟨,⟩_S − ⟨,⟩_{X_{σ'}}, i.e. for ⟨,⟩_{−1} relative to σ'.
  - Lemma 3.2 again (c = −1, blocks σ'): Q is isotropic for ⟨,⟩_S + ⟨,⟩_{X_{σ'}⊔X_{σ'}**}, which is the standard form on X̂.
  - |Q|² = |E|²·3^{12b} = 3^{|X|+12b}. An isotropic code C ⊂ F^Z with |C|² = 3^{|Z|} is self-dual, since |C|·|C^⊥| = 3^{|Z|} and C ⊂ C^⊥ ([Lean] `selfDual_of_iso_card`, via character sums, no dimension theory). □(Q1)
- (Q3) Write Q = H₂(E' ⊕ T²). By Lemma 2.3, for w = H₂(v, t²):
      w_{σ''}(w) = ∏_{i∈S(σ)} φ(v_i) · ∏_{B∉𝓑} ∏_{y∈B} ψ(v_y, t²_{B,y}) · ∏_{B∈𝓑} λ(Σ_{y∈ϖ_B} κ(v_y, t²_{B,y})) · λ(Σ_{y∈ϖ'_B} κ(v_y, t²_{B,y})).
  - Apply Lemma 3.1 to (L, σ, T) = (E', σ', T²), with G_B = ∏ψ for B ∉ 𝓑 (Lemma 2.1) and G_B = the λλ-weight of the chosen split for B ∈ 𝓑 (Lemma 2.2). This gives R_{σ''}(Q) = R_{σ'}(E').
  - Now E' = H₁(E ⊕ T¹). For β ∈ σ with split {π₁, π₂}, the step-one blocks B_{π₁}, B_{π₂} partition β ⊔ β*, and wt(H₁(e,t)|_{B_{πj}}) = Σ_{x∈πj} κ(e_x, t¹_{β,x}) (Lemma 2.3 with ** replaced by *). So w_{σ'}(H₁(e, t¹)) = ∏_S φ(e_i) ∏_β λ(Σ_{π₁}κ)·λ(Σ_{π₂}κ).
  - Apply Lemma 3.1 to (E, σ, T¹) with G_β = that λλ-weight for the split of β (Lemma 2.2). This gives R_{σ'}(E') = R_σ(E). □(Q3)
- (Q2) is (Q3) with 𝓑 = ∅ (then w_{σ''} = f). □
- Self-duality of E is used only in (Q1). (Q2) and (Q3) hold for every linear code; Lemma 4.3 of [MQ] (§5 below) needs exactly this.

**Corollary 3.4 (chains; [I] Thm 5.9 engine) [P; Lean: `engine`, `chain`].** Suppose (E_j, σ_j) satisfies E_{j+1} = Q_{σ_j}(E_j; …) and σ_{j+1} = (σ_j)'' for some 𝓑_j. Then R_{σ_j}(E_j) = R_{σ_0}(E_0) for all j (by (Q3) and induction), and F(E_{j+1}) = R_{σ_0}(E_0) (by (Q2)). If E₀ is self-dual, so is every E_j (by (Q1)). □

**Remark 3.5 (what [Lean] has and what the Main Question needs).**
- [Lean] has Theorem 3.3 with: T¹ = T² = `Tfin` everywhere; canonical step-one splits (`r₁`); 𝓑 = {β₀}, exactly one refined step-one block, the other step-one blocks becoming singletons (`newState`, `R_newState`); canonical σ''-splits (`r₂`); a self-duality proof valid for this placement.
- (Q2) and (Q3) carry no self-duality hypothesis there (`indexG_Qc`, `R_newState`), as needed.
- Missing, and needed by the equivariant chains:
  - (i) per-block placements from `plc` (G-invariant placements are in general **not** `Tfin` in the given coordinates; the J-chain's J does not preserve `Tfin`, [V: Part 3]);
  - (ii) refinement of a G-orbit of step-one blocks (|𝓑| = 1, 3, 2, 6 in the four chains);
  - (iii) transposed refinement splits and transposed σ''-splits (Lemma 4.11).
- (iii) can also be obtained from the canonical ones by a relabelling of P, (b, s) ↦ (s, b), on the blocks concerned. R and self-duality are invariant under such relabellings (`R_block`, `selfDual_relabel` generalised to per-block position permutations).

--------------------------------------------------------------------------------------------

## 4. Equivariance ([MQ] Lemma 4.1, expanded)

**Definition 4.1.** Mon_σ(X) := {g = (π, s) ∈ Mon(X) : π maps every block of σ onto a block and every split pair onto a split pair}. It is a subgroup (finite, closed under composition), and it maps S(σ) to itself. Diagonal elements and −1 lie in it.

**Definition 4.2 (extension).** For Y ⊂ Z and g = (π, s) ∈ Mon(Z) with π(Y) = Y, define ext_Y(g) ∈ Mon(Z ⊔ Y*) by
  π(y*) := π(y)*,   s_{y*} := s_y   ("a Hadamard partner follows its partner with the same sign").
- For g ∈ Mon_σ(X): g' := ext_{X_σ}(g) ∈ Mon(X') and ĝ := ext_{X_{σ'}}(g') ∈ Mon(X̂).
- g' maps B_π = π ⊔ π* onto B_{π(π)}, so g' permutes σ'. That is where "split pairs go to split pairs" is used.

**Lemma 4.3 (properties of ext_Y) [P; V: Part 4, 300/300].**
- (a) ext_Y is an injective group homomorphism {g : π_g(Y) = Y} → Mon(Z ⊔ Y*). ext_Y(−1) = −1, and ext_Y of a diagonal element is diagonal.
- (b) ext_Y(g) commutes with H_Y := ∏_{y∈Y} h_{y,y*}.
- (c) For every y ∈ Y, the ext_Y(g)-cycle of y* has the same length and the same sign product as the g-cycle of y.
- (d) As a signed permutation representation, ext_Y(g) ≅ g ⊕ g|_Y (via y* ↔ y).
- *Proof.*
  - (a) π_{ext(gk)}(y*) = π_g(π_k(y))* = π_{ext g}(π_{ext k}(y*)). The sign of gk at y is s^k_y·s^g_{π_k y}, and the same formula holds at y*. Restriction to Z recovers g, so ext is injective.
  - (b) At the pair (π y, (π y)*): (ext g·H v) = (s_y(v_y + v_{y*}), s_y(v_y − v_{y*})) = (H·ext g·v). Off Y ⊔ Y* both maps act as g and the identity.
  - (c), (d) are immediate from π(y*) = π(y)* and s_{y*} = s_y. □

**Lemma 4.4 (transport) [P].** For g ∈ Mon_σ(X):
  ĝ·Q_σ(E; T¹, T²) = Q_σ(g·E; ĝT¹, ĝT²),  with (ĝT¹)_{π_g β} := g'·T¹_β and (ĝT²)_{π_{g'} B} := ĝ·T²_B.
- *Proof.* ĝ preserves X, X_σ*, and (X_{σ'})**, and acts on them by g, by g' restricted to X_σ*, and by ĝ restricted to (X_{σ'})**. So ĝ(E ⊕ T¹ ⊕ T²) = gE ⊕ ĝT¹ ⊕ ĝT².
  - ĝ commutes with H₂ (Lemma 4.3(b) for Y = X_{σ'}). It commutes with H₁ because ĝ restricted to X' is g', which commutes with H₁ by Lemma 4.3(b), while H₁ is the identity on (X_{σ'})**, which ĝ preserves.
  - Hence ĝH₂H₁(V) = H₂H₁(ĝV). The images of placements are placements (monomial images of self-dual codes). □

**Corollary 4.5 (equivariance) [P; V: Part 7, "gens ∈ Aut(Q)"].** Suppose:
- G ⊂ Mon_σ(X) ∩ Aut(E);
- the families are G-invariant, i.e. g'T¹_β = T¹_{π_g β} and ĝT²_B = T²_{π_{g'}B} for all g ∈ G.

Then ĝ ∈ Aut(Q_σ(E; T¹, T²)) for all g ∈ G, and g ↦ ĝ is an injective homomorphism G → Aut(Q_σ(E)).
- *Proof.* Lemma 4.4 with gE = E, and Lemma 4.3(a) applied twice. □

**Lemma 4.6 (equivariant placements: existence and construction) [P].** For β ∈ σ let G_β be its stabiliser and ρ_β: G_β → Mon(β) the restriction (the *local image*). Identify β* with β by x* ↔ x; then g' acts on β* as ρ_β(g) (Lemma 4.3(d)).
- (a) A G-invariant family T¹ exists iff for every β some placement P_β on β satisfies ρ_β(G_β)·P_β = P_β.
- (b) *Construction.* Choose representatives β₁, …, β_r of the G-orbits on σ and ρ-invariant placements P_i, and set T¹_{π_g β_i} := g'·P_i*.
  - This is well defined: if π_g β_i = π_k β_i, then k⁻¹g ∈ G_{β_i} fixes P_i*, so g'P_i* = k'P_i*.
  - It is G-invariant because g ↦ g' is a homomorphism.
- (c) The same holds at step two, with σ', the stabiliser G_B = {g ∈ G_β : π_g(π) = π} of B = B_π, and its local image on B = π ⊔ π*. By Lemma 4.3(d) that image is the doubled action ρ_π(g) ⊕ ρ_π(g), where ρ_π(g) ∈ Mon(π) (a group of order 8).
- *Proof.* "Only if": an invariant family has g'T¹_β = T¹_β for g ∈ G_β. "If": (b). □

**Lemma 4.7 (inherited data) [P; V: Part 4].** For g, k ∈ G:
- ord ĝ = ord g; ĝ^j = −1 ⟺ g^j = −1; ĝk̂ = k̂ĝ ⟺ gk = kg. More generally every relation among elements of G holds among their extensions.
- ĝ ≅ g|_{S(σ)} ⊕ (g|_{X_σ})^{⊕4} as a signed permutation representation (Lemma 4.3(d) twice: x, x*, x**, x*^{**}). Hence:
  - every coordinate of X̂ lies in a ĝ-cycle of the same length and sign product as some g-cycle on X;
  - ĝ fixes a coordinate iff g does;
  - "all cycles of length d" is inherited;
  - the Frame shape of ĝ is (Frame of g|_S)·(Frame of g|_{X_σ})⁴;
  - ∏ŝ = ∏_{S(σ)} s.
- These are exactly the data used by GJF Thm 5.6 (order, g^{m/2} = −1, cycle shape 3^{c/3}, 6^{c/6}), by [MQ] Thm 8.1 (J² = K² = −1, JK = −KJ), and by [OI] Lemma 3.3 (eigenvalue types from signed cycles). □

**Lemma 4.8 (refinement stability) [P].** Let 𝓑 ⊂ σ' be G-stable (g' permutes 𝓑), with refinement splits that are G-equivariant (g' maps the split pairs of B to the split pairs of g'B). Then ĝ ∈ Mon_{σ''}(X̂) for all g ∈ G, for either convention of σ''-splits. So Corollary 4.5 applies to the next step, provided Lemma 4.6's condition holds there (see Lemma 4.11).
- *Proof.* ĝ(ϖ ⊔ ϖ**) = g'ϖ ⊔ (g'ϖ)**, a σ''-block, since g'ϖ is a split pair of g'B ∈ 𝓑.
  - Canonical σ''-split: ĝ{y, y**} = {g'y, (g'y)**}.
  - Transposed σ''-split: ĝ(ϖ) = g'ϖ and ĝ(ϖ**) = (g'ϖ)**. □
- Both uniform refinement splits are always G-equivariant. The canonical one because g' maps {p, p*} to {g p, (g p)*}. The transposed one because g' maps π = B ∩ X to g'B ∩ X and π* to (g'B ∩ X)*.

**Proposition 4.9 (step one: which local images admit a placement) [P; V: Part 3].**
- (a) H ⊂ Mon(β) admits an invariant placement iff H ⊂ Mon(P) for one of the 8 placements P. Maximal such H preserving a given split are Mon(P) ∩ W_split, of order 16 (the semidihedral group SD₁₆).
- (b) Elements (constant on signed cycle types): the number of placements preserved is 8 for ±1; 4 for type 2⁻2⁻ (double transposition with both 2-cycles of sign product −1, i.e. g² = −1) and for 2⁺1⁺1⁻; 2 for 3⁺1⁺, 3⁻1⁻, 4⁻; and **0** for all other types. In particular it is 0 for diagonal g ≠ ±1 and for 2⁺2⁺ (involutive double transpositions).
- (c) *J-type.* J(e_p) = s e_q, J(e_q) = −s e_p, J(e_r) = s' e_s, J(e_s) = −s' e_r (so J² = −1). Exactly 4 placements are J-invariant, among them the explicit
      T_{s,s'} := ⟨(1, s, 1, 0), (0, s, 2, 2s')⟩ in the coordinate order (p, q, r, s).
  - *Proof.* For s = s' = 1 the paper checks that ⟨(1,1,1,0), (0,1,2,2)⟩ is J-invariant. Conjugating by the diagonal d = (1, s, 1, s') gives the general case: dJ₁d⁻¹ = J_{s,s'}, and dT = T_{s,s'}. [V] all four (s, s').
- (d) *Q₈-regular.* Q₈ = ⟨J, K⟩ acting on β with J² = K² = −1, JK = −KJ, and permutation image the regular V₄. Exactly 4 placements are Q₈-invariant (both models used in the chains, [V]). In Morita form ([MQ] Lemma 9.1) they are {X ∈ M₂(F₃) : both rows in ℓ} for the 4 lines ℓ ⊂ F₃²; left multiplication preserves these.
- (e) *Obstructions, by hand.*
  - A diagonal g ≠ ±1 is in no Mon(P) (Lemma 1.5(c)).
  - If g ∈ Mon(P) permutes the coordinates by a double transposition, then g lies over V₄ ⊂ S₄ ≅ PGL₂(F₃). The preimage of V₄ in GL₂(F₃) is Q₈ ⊂ SL₂(F₃), whose elements other than ±1 have square −1. So g² = −1, and an involutive double transposition is in no Mon(P). □

**Proposition 4.10 (step two: doubled actions) [P; V: Part 3].** Let B = π ⊔ π* with π = {p, q}, and H = ρ_π(G_B) ⊂ Mon(π) (order 8). The doubled group {m ⊕ m : m ∈ H} admits an invariant placement on B** **iff H ⊂ ⟨J_π⟩** for a swap J_π of p ↔ q with J_π² = −1, i.e. iff H ∈ {1, ⟨−1⟩, ⟨J_π⟩}.
- *Proof.* The 8 elements m of Mon(π):
  - id and −1: the doubled element preserves all 8 placements.
  - The two swaps with m² = −1: the doubled element is J-type with s' = s (Prop 4.9(c)), and T_{s,s} in the order (p, q, p*, q*) is invariant.
  - diag(1,−1), diag(−1,1): the doubled element is diagonal ≠ ±1 (no placement).
  - The two swaps with m² = +1: the doubled element is an involutive double transposition (no placement, Prop 4.9(e)).
  - The subgroups of Mon(π) ≅ D₈ avoiding the four bad elements are 1, ⟨−1⟩ and the cyclic group ⟨J_π⟩ = {±1, ±J_π}. The 4 placements invariant under J_π are invariant under ⟨J_π⟩. □
- *Consequence.* Lemma 4.1 of [MQ] needs a hypothesis at step two as well: an element of G that stabilises a split pair and acts on it as an involutive swap or as diag(1, −1) makes Q_σ impossible equivariantly (§9, issue 1).

**Lemma 4.11 (local types propagate) [P; V: Part 7].** Call a block β with split {π₁, π₂} of type:
- **τ₀** if ρ_β(G_β) ⊂ {±1};
- **τ_J** if ρ_β(G_β) = ⟨J_β⟩ with J_β a J-type element (Prop 4.9(c)) that maps each split pair to itself;
- **τ_Q** if ρ_β(G_β) is Q₈-regular (Prop 4.9(d)) and the split is into J-pairs {x, Jx}, {Kx, JKx} (so Q₈ preserves the split).

Suppose every σ-block has type τ₀, τ_J or τ_Q, and use transposed refinement splits and transposed σ''-splits. Then:
- (i) G-invariant T¹ exist (4 placements per τ_J or τ_Q block, 8 per τ₀ block).
- (ii) Every step-one block B_π has ρ_π(G_{B_π}) ⊂ ⟨J_π⟩, so G-invariant T² exist (Prop 4.10):
  - τ₀: G_{B_π} ⊂ G_β acts by ±1;
  - τ_J: G_{B_π} = G_β = ⟨J⟩, acting on π by a swap with square −1;
  - τ_Q: G_{B_π} = {g : g(π) = π} = the stabiliser of the J-pair π, whose local image is ⟨J⟩ (K moves π to the other pair).
- (iii) Every σ''-block has type τ₀ or τ_J. For A = ϖ ⊔ ϖ** with ϖ = {p, q} (transposed refinement split of B_π; the other block {p*, q*} ⊔ {p*, q*}** is the same with p ↦ p*):
  - G_A = {g ∈ G_B : g'(ϖ) = ϖ} = G_B, since G_B preserves π = B ∩ X, and on the *-copy likewise.
  - Its local image on A in the order (p, q, p**, q**) is the doubled ρ_π(G_B) ⊂ doubled ⟨J_π⟩. With the transposed split {ϖ, ϖ**} both pairs are fixed. So A is of type τ_J (or τ₀).
- So from the second stage on, every block is of type τ₀ or τ_J, and (i)–(iii) apply again at every stage. □
- [V: Part 7] On the actual chains, every stage: J-chain n = 12 → 72, ℤ/12 chain A n = 36 → 144, Q₈ chain n = 24 → 96, Q₈×ℤ/3 chain n = 72 → 144. σ-blocks are τ_J (τ_Q at the Q₈ seeds). Step-one blocks are J-type (with the canonical split the J-pairs are swapped: "pairs swapped" in the log). Invariant placements exist everywhere. The σ''-blocks are τ_J again.
- *Why the transposed splits matter.* With canonical σ''-splits {y, y**}, J swaps the two pairs of A. From the next stage on, the step-one stabilisers are only {±1}, their G-orbits have |G|/2 elements, and b'' = |G| instead of |G|/2. So from the third step on the k-increment is |G| instead of |G|/2. For example, the ℤ/12 chains would give only k ∈ {3, 6, 9, 15} ∪ {k ≡ 0 mod 12} ∪ {k ≡ 3 mod 12, k ≥ 27}. That misses k ≡ 6, 18 mod 24 (gcd 6) and k ≡ 9, 21 mod 24 (gcd 3) from k = 18 and 21 on, and the J-chain would miss k ≡ 2 mod 4, k ≥ 6. (The Q₈ and Q₈×ℤ/3 chains would still reach k ≡ 0 mod 8 and k ≡ 0 mod 24.) With transposed refinement splits and transposed σ''-splits, the stabilisers of the next step-one blocks stay ⟨J⟩, as the τ_J computation in (iii) shows. (A canonical refinement split {p, p*}, {q, q*} would already give σ''-blocks with stabiliser {±1}.)
  - `mainq_equivariant.choose_splits` avoids this by re-splitting σ'' so that stabilisers fix both pairs, which is the transposed choice here.
  - [MQ] §4 "Conventions" describes the canonical reading "(w, w**, x, x**)" (§9, issue 2).

**Table 4.12 (the four chain families) [P; V: Part 7, and the chain logs of [MQ] §6].** At every stage the step-one stabilisers are ⟨J⟩ of order 4 (with −1 ∈ G; Lemma 4.11(ii), (iii)). So a G-orbit of step-one blocks has |G|/4 elements, b'' = 2·|G|/4 = |G|/2, and each later step adds 12b'' = 6|G| coordinates, i.e. |G|/2 to k.

| chain | G, \|G\| | seed (length) | σ₀, b₀, type | first step | b'' | later steps | k reached |
|---|---|---|---|---|---|---|---|
| J ([MQ] Thm 4.2) | ⟨J⟩ ≅ ℤ/4, 4 | Golay (12) | {(0,1\|2,3)}, 1, τ_J | 12 → 24 | 2 | +24 | all even k ≥ 2 |
| ℤ/12 A ([MQ] Thm 4.4) | ⟨g⟩, 12 | `z12seed_len36_3` (36) | σ₃, 3, τ_J | 36 → 72 | 6 | +72 | 6, 12, 18, … |
| ℤ/12 B | ⟨g⟩, 12 | same | σ₆, 6, τ_J | 36 → 108 | 6 | +72 | 9, 15, 21, … |
| Q₈ ([MQ] §5, Cor 8.2) | Q₈, 8 | `q8chain_len24` (24) | 2 orbit blocks, τ_Q | 24 → 48 | 4 | +48 | 4, 8, 12, … |
| Q₈×ℤ/3 ([MQ] Thm 10.1) | Q₈×⟨h⟩, 24 | `q8z3_seed72` (72) | 6 orbit blocks, τ_Q | 72 → 144 | 12 | +144 | 12, 24, 36, … |

**Remark 4.13 (the sign of the index) [P].** Flipping one coordinate i (d = diag with d_i = −1) replaces C by dC, G by dGd⁻¹, Index by −Index and T_h by −T_h (Lemma 1.3), and preserves every property in Lemma 4.7. So "Index = ±24" may be normalised to +24 without losing any symmetry property.

--------------------------------------------------------------------------------------------

## 5. Collapsed fixed codes ([MQ] Lemma 4.3, expanded)

**Setting 5.1.** G ⊂ Mon_σ(X) ∩ Aut(E) with G-invariant placement families, and h ∈ G of order 3 **without fixed coordinate**. For a code C and k ∈ Mon: T_k(C) := F(C^k) = Σ_{x∈C, kx=x} f(x), the twined count. T_{h²} = T_h, since C^{h²} = C^h.

**Lemma 5.2 (no fixed blocks) [P].** ⟨h⟩ has only orbits of size 3 on X̂, on σ, on σ', and on σ'' (for G-stable 𝓑).
- *Proof.* ĥ has no fixed coordinate (Lemma 4.7). An ĥ-stable 4-set would carry a permutation of order 1 or 3 of 4 points, which has a fixed point. □
- In particular the 4 points of a block lie in 4 different h-orbits: if h^j x ∈ β for x ∈ β and j ≢ 0, then h^jβ ∩ β ≠ ∅, so h^jβ = β.

**Lemma 5.3 (sign normalisation) [P; V: Part 6 (ℤ/12 seed: h = g⁴ has 24 sign changes)].** There is a diagonal d with h₀ := dhd⁻¹ a permutation (all signs +1). Moreover:
- d ∈ Mon_σ(X), and by Lemma 4.4 conjugation by d̂ carries the whole construction for (E, G, T) to the one for (dE, dGd⁻¹, d̂T);
- for every code C ⊂ F^{X̂}: F(d̂C) = ε·F(C) and T_{d̂ĥd̂⁻¹}(d̂C) = ε·T_ĥ(C), with the same ε = ∏_{x∈X̂} d̂_x = ∏_{i∈S(σ)} d_i.
- *Proof.* On a 3-cycle (i, πi, π²i) of h, h³ = 1 gives s_i s_{πi} s_{π²i} = 1.
  - Put d_i = 1, d_{πi} = s_i, d_{π²i} = s_i s_{πi}. Then (dhd⁻¹)(e_i) = d_{πi} s_i d_i e_{πi} = e_{πi}, and likewise at πi. At π²i: d_i s_{π²i} d_{π²i} = s_{π²i} s_i s_{πi} = 1.
  - Diagonal maps preserve blocks and pairs.
  - (d̂C)^{d̂ĥd̂⁻¹} = d̂(C^ĥ), and f(d̂x) = (∏d̂)f(x) (Lemma 1.3).
  - Each x ∈ X_σ contributes d_x⁴ = 1 to ∏d̂ (coordinates x, x*, x**, x*^{**}). □
- So T_h = 0 and the relation "T_h vs Index" are invariant, and **from now on h is a permutation**. Then ĥ is a permutation too (ext preserves "all signs +1").
- *Lean suggestion:* build the seeds so that h is the pure shift on coordinates X̄ × Fin 3 (below). Then no normalisation is needed.

**Definition 5.4 (collapse).** For a finite set Z with a fixed-point-free permutation η of order 3:
- Z̄ := Z/⟨η⟩, and c: (F^Z)^η → F^{Z̄}, c(v)_{z̄} := v_z;
- c is a linear bijection, and f(c v) = f(v) since φ³ = φ;
- for an η-invariant code C: F(c(C^η)) = T_η(C).

Collapsed structures, all well defined by Lemma 5.2 and ĥ(x*) = (hx)*, ĥ(y**) = (ĥy)**:
- X̄ = X/h, and σ̄ = {β̄ : β ∈ σ}, one block per h-orbit of blocks, β̄ = {x̄ : x ∈ β} with 4 elements; split pairs π̄; S(σ̄) = S(σ)/h.
- x̄* := (x*)‾ and ȳ** := (y**)‾. With these, X̂/ĥ is literally the coordinate set of Q_σ̄ on X̄, and (B_π)‾ = B_{π̄}.
- T̄¹_{β̄} := the image of T¹_β under x* ↦ x̄*. It is independent of the representative, since T¹_{hβ} = ĥT¹_β and (ĥt)_{(hx)*} = t_{x*}. Likewise T̄².
- For G-stable 𝓑 with equivariant splits: 𝓑̄ := 𝓑/h, and (σ'')‾ = (σ̄)'' (refinement of Q_σ̄ at 𝓑̄ with the collapsed splits and the same σ''-convention).
- D := c(E^h) ⊂ F^{X̄}, the *collapsed fixed code*. It is linear, not necessarily self-dual (its dual is the orbit-sum code, [MQ] §7).

**Theorem 5.5 (fixed codes collapse) [P; V: Part 6, as subspaces: ℤ/12 seed steps 36 → 72 and 72 → 144, Q₈×ℤ/3 seed 72 → 144].**  c(Q_σ(E; T¹, T²)^ĥ) = Q_σ̄(D; T̄¹, T̄²).
- *Proof.*
  1. V := E ⊕ T¹ ⊕ T² is ĥ-invariant, and V^ĥ = E^h ⊕ (T¹)^ĥ ⊕ (T²)^ĥ, since ĥ preserves the three coordinate sets X, X_σ*, (X_{σ'})**.
  2. On one h-orbit {β, hβ, h²β} (three distinct blocks, Lemma 5.2), (t₀, t₁, t₂) ∈ T¹_β ⊕ T¹_{hβ} ⊕ T¹_{h²β} is ĥ-fixed iff t₁ = ĥt₀, t₂ = ĥt₁, t₀ = ĥt₂. So the fixed part is {(t, ĥt, ĥ²t) : t ∈ T¹_β} (ĥ³ = 1), and its collapse is T̄¹_{β̄}. The same holds for T².
  3. Hence c(V^ĥ) = D ⊕ T̄¹ ⊕ T̄².
  4. H := H₂H₁ is bijective and commutes with ĥ (Lemma 4.3(b)), so Q^ĥ = H(V)^ĥ = H(V^ĥ).
  5. On (F^{X̂})^ĥ, c∘H = H̄∘c, where H̄ = H̄₂H̄₁ is built from the collapsed oriented pairs (x̄, x̄*) and (ȳ, ȳ**). Indeed, for fixed v, c(H₁v)_{x̄} = v_x + v_{x*} = c(v)_{x̄} + c(v)_{x̄*}, similarly at x̄*, and likewise for H₂.
  6. So c(Q^ĥ) = H̄(c(V^ĥ)) = H̄(D ⊕ T̄¹ ⊕ T̄²) = Q_σ̄(D; T̄¹, T̄²). □

**Corollary 5.6 (T_h = R_σ̄(D)) [P; V: Part 6, synthetic cases 8/8 including nonzero values −4, 2, 4].** T_h(Q_σ(E)) = F(c(Q^ĥ)) = F(Q_σ̄(D)) = R_σ̄(D), by Theorem 3.3(Q2) for the linear code D. If h was not normalised, multiply by ε (Lemma 5.3).

**Corollary 5.7 (T_h is constant along an equivariant chain) [P; V: Part 6, ℤ/12 two steps].** Let (E_j, σ_j) be a G-equivariant chain (§6), h ∈ G normalised as above, D₀ := c(E₀^h), σ̄₀ := (σ₀)‾. Then **T_h(E_j) = R_{σ̄₀}(D₀) for all j ≥ 1.**
- *Proof by induction.* Define D_{j+1} := Q_{σ̄_j}(D_j; T̄_j) and σ̄_{j+1} := (σ̄_j)'' (collapsed 𝓑_j and splits). Invariant (I_j): c(E_j^h) = D_j, (σ_j)‾ = σ̄_j, and R_{σ̄_j}(D_j) = R_{σ̄₀}(D₀). (I₀) holds by definition.
  - (I_j) ⇒ (I_{j+1}): Theorem 5.5 gives c(E_{j+1}^h) = Q_{σ̄_j}(D_j) = D_{j+1}; Def 5.4 gives (σ_{j+1})‾ = σ̄_{j+1}; Theorem 3.3(Q3) for D_j gives R_{σ̄_{j+1}}(D_{j+1}) = R_{σ̄_j}(D_j).
  - Then T_h(E_{j+1}) = F(D_{j+1}) = R_{σ̄_j}(D_j) = R_{σ̄₀}(D₀), by Theorem 3.3(Q2). □
- The collapsed chain (D_j, σ̄_j) is an ordinary, non-equivariant [I]-type chain on the length-|X₀|/3 code D₀. So T_h is decided on the seed by the finite value R_{σ̄₀}(D₀).

**Remark 5.8 (pitfall: λ-weights do not collapse) [P; V: Part 6].** For x ∈ E^h, in general w_σ(x) ≠ w_σ̄(c x): an h-orbit of three blocks on which x has weight 1 contributes λ(1)³ = −8, its collapse λ(1) = −2. So Σ_{x∈E^h} w_σ(x) ≠ R_σ̄(D) in general. Synthetic example: E = diag⟨(1,0,0,0,1,1)⟩ on three copies gives −16 vs R_σ̄(D) = T_h(Q_σ E) = −4.
- The proof above never collapses λ-weights. It collapses the code Q and applies Theorem 3.3 downstairs. A formalization should not try to prove a pointwise identity for w_σ.

--------------------------------------------------------------------------------------------

## 6. The equivariant engine

**Theorem 6.1 [P, from §§3–5; V: the chain logs of [MQ] §6 and Part 7].**

*Seed data:*
- E₀ ⊂ F^{X₀} self-dual, and a split block system σ₀ with b₀ blocks;
- a finite group G ⊂ Mon_{σ₀}(X₀) ∩ Aut(E₀) with −1 ∈ G, every σ₀-block of type τ_J or τ_Q (Lemma 4.11);
- r := R_{σ₀}(E₀).

*Recursion:*
- E_{j+1} := Q_{σ_j}(E_j; T¹_j, T²_j) with G-invariant placements (Lemma 4.11(i), (ii));
- σ_{j+1} := (σ_j)'' for 𝓑_j = one G-orbit of step-one blocks, with transposed refinement splits and transposed σ''-splits;
- G acts on X_{j+1} by iterated extension.

*Then for every j ≥ 1:*
- (a) E_j is self-dual of length |X₀| + 12(b₀ + … + b_{j−1}), with b_{i+1} = 2|𝓑_i| (Table 4.12);
- (b) Index(E_j) = F(E_j) = r;
- (c) G ↪ Aut(E_j), with all relations and signed cycle data of Lemma 4.7;
- (d) every σ_j-block is of type τ₀ or τ_J, so the recursion never stops;
- (e) if h ∈ G has order 3 and no fixed coordinate: T_h(E_j) = ε·R_{σ̄₀}(D₀) (Corollary 5.7), where D₀ and σ̄₀ are formed after the sign normalisation of Lemma 5.3, whose sign is ε (ε = 1 if h is already a permutation).

*Proof.* Induction on j:
- (a), (b) by Theorem 3.3 and Corollary 3.4;
- (c) by Corollary 4.5 and Lemma 4.7;
- (d) by Lemmas 4.8 and 4.11;
- (e) by Corollary 5.7. □

**Seed facts (finite checks, all verified in the scripts of [MQ] §6).**

| chain | finite facts | naive size of the largest check [V: Part 8] |
|---|---|---|
| J | J ∈ Aut(Golay), J² = −1, J fixed-point-free; (0,1\|2,3) of type τ_J; R = 24 | R_{σ₁}(Golay) = 24 is already `R_golay₁` in [Lean] (split {0,1},{2,3}); 3⁶ |
| ℤ/12 | g ∈ Aut(E₃₆), g¹² = 1, g⁶ = −1, all cycles of length 6; σ₃ or σ₆ g-stable of type τ_J; R_σ(E₃₆) = −24; R_σ̄(D₀) = 0 (D₀: length 12, dim 6) | R_{σ₃}: 2¹⁸ ≈ 2.6·10⁵ candidates (E₃₆ has full rank 18 on the 24 singletons; plain 3¹⁸ ≈ 3.9·10⁸); R_{σ₆}: 2¹²·3⁶ ≈ 3·10⁶ |
| Q₈ | J, K ∈ Aut(E₂₄), relations; σ of type τ_Q; R_σ = 24 | 2¹² = 4096 candidates (full rank on the 16 singletons) |
| Q₈×ℤ/3 | J, K, h ∈ Aut(E₇₂), relations, h fixed-point-free; σ of type τ_Q; R_σ(E₇₂) = 24; R_σ̄(D₀) = 0 (D₀: length 24, dim 12) | R_σ(E₇₂): 2³⁶ ≈ 6.9·10¹⁰ candidates (plain 3³⁶) |

A word x with w_σ(x) ≠ 0 is ±1 on every singleton. So if E has rank r on the singletons, at most 2^r·3^{dim E − r} words need evaluating: fix the ±1 pattern on an information set inside the singletons, then run through the rest.

--------------------------------------------------------------------------------------------

## 7. Finite checks versus induction; Lean plan and size

**Kinds of statements.**
- *Finite, by `decide`:*
  - the 8 placements, their self-duality and cardinality;
  - Lemmas 2.1, 2.2 for all placements and splits;
  - Props 4.9, 4.10 for the local types used (J-type for 4 sign pairs, the Q₈ model, the 8 doubled actions);
  - all seed facts of §6 except the large R-values.
- *Structural (no induction; sums, bijections, `funext` case analysis):*
  - Lemmas 3.1, 3.2 and Theorem 3.3;
  - Lemmas 4.3–4.8 and 4.11(iii) (stabiliser computation);
  - Lemmas 5.2, 5.3 and Theorem 5.5.
- *Induction on the chain step:* Corollaries 3.4 and 5.7 and Theorem 6.1. The inductive invariant must carry:
  - self-duality, R = r, the G-action with its relations;
  - the local types of all blocks, G-stability of σ_j;
  - for h: the collapsed pair (D_j, σ̄_j).
- *Not kernel-feasible as they stand:* R_σ of the ℤ/12 and Q₈×ℤ/3 seeds (§6 table). The first needs 2.6·10⁵ candidate evaluations. The Golay checks use 729 words and dominate the present ≈ 2 min build. So the ℤ/12 seed needs a verified bit-sliced evaluator, since `Nat` bit operations are GMP-accelerated in the kernel. The Q₈×ℤ/3 seed (6.9·10¹⁰) needs a mathematical reduction (e.g. [MQ] Cor 9.2, still ≈ 5.8·10⁶ good planes), a different seed, or `native_decide`, which the project standard excludes.

**Recommended Lean structure** (reusing [Lean] names).
1. `plc : Fin 8 → Finset (P → F)` and `localA_all`, `localB_all` (with a split parameter `Fin 3`) by `decide` or by transport from `localA`/`localB` (Lemma 2.2 remark).
2. `Dp (E) (τ : B → Fin 8)`, generalising `D`, with `CSG_Dp`, `card_Dp`, `sum_Dp`, `iso_Dp` (copy the proofs with `inT` replaced by `· ∈ plc (τ β)`). Then `D E = Dp E (fun _ => i₀)` with `plc i₀ = Tfin`.
3. General refinement: new singletons `S ⊕ ({x // x ∉ 𝓑} × (P × Fin 2))` and blocks `{x // x ∈ 𝓑} × Fin 2`, a regrouping equivalence generalising `r₂`, and `R_newStateGen`, proved like `R_newState` with `sum_Dp` and a per-block choice of `sgl`/`refdS`.
4. Signed permutations as `structure SPerm ι := (π : ι ≃ ι) (s : ι → ℤˣ)`, acting by a `LinearEquiv` on `ι → F`. Block-structured maps on `Blk S B` = (`SPerm S`, `B ≃ B`, `B → SPerm P` preserving the pair partition). `ext` to `Dbl S B`, `ext_mul`, `ext_neg_one`, `Φ_ext` (Lemma 4.3(b)), `Dp_ext` (Lemma 4.4), plus compatibility with `r₁`, `r₂`, `blockEquiv`.
5. Inherited data (Lemma 4.7): relations come from `ext_mul`; fixed-point-freeness and cycle lengths via "(ext g)^j fixes y ⟺ g^j fixes root(y)".
6. Collapse (Theorem 5.5) in model coordinates `Blk (S̄ × Fin 3) (B̄ × Fin 3)` with h the shift in `Fin 3` and placement indices constant along `Fin 3`. Show "fixed vectors ≃ vectors on `Blk S̄ B̄`" commutes with `Φ`, `Dp`, `r₁`, `r₂`. Conclude `twined (Qc …) = R (collapsed)`.
7. The engine (Theorem 6.1) as a `State` structure plus a step lemma, and four instantiations with the k-arithmetic of Table 4.12.

**Size estimate for this component** (items 1–7, excluding the seed certificates):

| item | lines |
|---|---|
| 1 placements and local identities | 80–150 |
| 2 `Dp` generalisation | 60–150 |
| 3 general refinement | 120–180 |
| 4 signed permutations, extension, transport, regrouping compatibility | 300–400 |
| 5 inherited data | 80–120 |
| 5′ local types and placement existence (Props 4.9–4.11) | 120–180 |
| 6 collapse | 200–300 |
| 7 engine and four chains | 250–400 |
| **total** | **≈ 1,200–1,900** |

- For comparison, [Lean] Existence.lean (805 lines) came in below its own estimate of 1,000–2,500.
- *Seed certificates in addition.*
  - J-chain: ≈ 50 lines, `decide` on Golay.
  - Q₈ seed: ≈ 150 lines plus a 2¹² enumeration.
  - ℤ/12 seed: ≈ 300–500 lines for a verified bit-sliced evaluator, plus a long kernel run.
  - Q₈×ℤ/3 seed: open (see above).
- The VOA side (orbifold existence, anomalies, [OI]) is not in Mathlib and would enter as hypotheses. So a Lean statement of the Main Question at the code level is: "for every k there are C and G ⊂ Aut(C) with the hypotheses of GJF Thm 5.6 / [OI] Theorem O". The classes k ≢ 0 mod 24 are within reach of this plan, provided the ℤ/12 and Q₈ seed checks are feasible. k ≡ 0 mod 24 hinges on the n = 72 seed certificate.

--------------------------------------------------------------------------------------------

## 8. Verification [V: `ternary60/theory/blueprint_equivariant.py`, log beside it; ≈ 35 s]

- **Part 1.** 130 planes in F₃⁴, 8 self-dual = 8 [4,2,3] = the Mon-orbit of T₀. |Mon(T)| = 48, ∩ diagonal = ±1, image S₄, element orders those of GL₂(F₃), self-normalising, 8 distinct stabilisers, two rulings of 4.
- **Part 2.** Lemma A 648/648 and Lemma B 1944/1944 (all placements, all splits, all u).
- **Part 3.** Placements preserved by each signed cycle type (Prop 4.9(b)); J-type: 4 each and T_{s,s'} invariant for all (s, s'); Q₈-regular: 4 (both models); doubled actions: 8, 0, 0, 8, 0, 4, 4, 0 (Prop 4.10); Mon(T) ∩ W_split of order 16 with SD₁₆ element orders; `Tfin` is invariant under J_{s,s'} only for (s, s') ∈ {(1,−1), (−1,1)}, so **not** under the J-chain's J (s = s' = −1).
- **Part 4.** On random block-structured g, h (m = 12, n = 36): ext(gh) = ext(g)ext(h), commutation with H₁ and H₂, and inherited cycle length and sign product, each 300/300; (−1)^ = −1.
- **Part 5.** Theorem 3.3 on 60 random cases with non-self-dual E (m ∈ {6, 8}), random placements, random splits and all 4 subsets 𝓑: (Q2) 60/60, (Q3) 60/60, (Q1) 12/12.
- **Part 6.**
  - Synthetic h-invariant codes: T_h(Q_σ E) = R_σ̄(D) 8/8, with values −4, 2, 4; the naive R-collapse differs (−16 vs −4).
  - ℤ/12 seed after sign normalisation, step 36 → 72: c(Q^ĥ) = H̄(D ⊕ T̄) as subspaces (D ⊂, 1 + 2 collapsed placements ⊂, all [4,2,3], dimensions add up); T_h = R_σ̄(D) = R_σ̄''(c(Q^ĥ)) = 0.
  - Step 72 → 144: the same subspace identity, the collapsed code of step 1 equals D₁ of step 2, |T_h| = 0.
  - Q₈×ℤ/3 seed, step 72 → 144: the subspace identity, R_σ̄(D) = 0, |T_h| = 0.
- **Part 7.** Local types at every stage of the four chains (Lemma 4.11, Table 4.12), invariant placements everywhere, generators in Aut(Q).
- **Part 8.** Certificate sizes of §6.

--------------------------------------------------------------------------------------------

## 9. Issues found

*Status (2026-09-27): the items below are tracked, with what has been fixed since, in `README.md` §5.*

None of these invalidates a result: all chain codes were built by `mainq_equivariant.quad_eq`, which handles each point correctly. They concern the written statements in [MQ], [I], the paper and [Lean].

1. **[MQ] Lemma 4.1(3) ("so the construction iterates") and paper Lemma `lem:eq` are incomplete.** Iterating needs G-invariant placements again at both steps of the next stage. This is a real condition:
   - by Prop 4.10, a stabiliser acting on a split pair by an involutive swap or by diag(1, −1) admits **no** invariant T² on the step-one block;
   - by Prop 4.9(b), most element types admit no invariant T¹;
   - [MQ]'s remark "When do invariant placements exist?" treats only step one (β*).
   - The fix is Lemma 4.11: with the local types τ₀/τ_J/τ_Q and transposed splits, placements exist at every stage. The paper's paragraph after `lem:eq` also proves only the J case; the Q₈-regular seed blocks need Prop 4.9(d).
2. **σ''-splits must be re-chosen (transposed), and [MQ] §4 "Conventions" describes the other choice.** [MQ] reads a refined block as the 4-tuple (w, w**, x, x**) with split {w, w**}, {x, x**}.
   - For the four chains that split has J swapping the two pairs. The next step-one blocks then have stabiliser {±1} instead of ⟨J⟩, b'' becomes |G| instead of |G|/2, and the k-increment doubles.
   - Taken literally, the convention would therefore **not** give [MQ] Thm 4.4's "k grows by 6". The ℤ/12 chains would then miss k ≡ 6, 18 and 9, 21 mod 24 from k = 18 and 21 on, i.e. part of gcd(k,24) ∈ {3, 6}. Likewise Thm 4.2's "lengths 12 + 12 + 24j" would fail, though gcd = 4 itself only needs k ≡ 0 mod 4.
   - The code is right: it re-splits (`choose_splits(G2, newblocks)`, "so that stabilisers fix both pairs"), which is the transposed choice, and Thm 4.2's "σ″ is again two J-stable blocks" is true as sets. The fix is to state the transposed σ''-split in [MQ] §4. The paper leaves splits free in its definition of Q_σ and says "with J-stable pairs" for the J-chain, which is the transposed choice; its ℤ/12 paragraph should say the same for the σ''-blocks.
3. **[I] Lemma 5.8 is stated for self-dual E but applied to the non-self-dual D in [MQ] Lemma 4.3.** Its proof, and [Lean] `indexG_Qc`/`R_newState`, never use self-duality for (Q2)/(Q3) (Theorem 3.3 here; [V: Part 5] on non-self-dual codes). This is a wording issue only; `paper/main-question.tex` already says "for any linear code".
4. **[Lean] covers Lemma 5.8 only in a special form** (Remark 3.5): fixed placement `Tfin`, canonical splits, one refined block. `Tfin` is not invariant under the J-chain's J on block (0,1,2,3) [V: Part 3]. So the Lean Thm 5.9 codes are not the J-chain codes, and "formally verified" for Thm 5.9 does not extend to the Main Question chains without items 1–7 of §7.
5. **Dangling reference.** `notes/orbifold-index.md` §4 cites `notes/lean-blueprint.md`, which does not exist in the repository.
6. (Not an error, a trap.) Remark 5.8: λ-weights do not collapse under h. [MQ] Lemma 4.3 is correct because it collapses the code, not the weight.
7. (Bookkeeping.) The new script `ternary60/theory/blueprint_equivariant.py` has no row in README's layout table yet (not added here: this file may not edit existing files).

Confirmed as stated in [MQ] §4: "8 conjugates = 8 placements" (Lemma 1.5(d)); Aut(tetracode) ≅ GL₂(F₃) (Lemma 1.5(c), now with a proof); inheritance of orders, relations and cycle lengths (Lemma 4.7, extended to sign products and Frame shapes); and Lemma 4.3's collapse identity (Theorem 5.5, verified as an identity of subspaces).
