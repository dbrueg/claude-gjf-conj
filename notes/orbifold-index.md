# The index of the orbifolds used for the Main Question, including the non-cyclic groups

Proof file, started 2026-09-27 and revised the same day after a three-lens review, which found no error but 7 gaps and 27 minor points; §5 lists the changes. It proves that the orbifolds of `notes/main-question.md` [MQ] have the claimed supersymmetric index: GJF Thm 5.6 (cyclic groups, [MQ] §4), [MQ] Cor 8.2 (Q₈) and [MQ] Thm 10.1 (Q₈ × ℤ/3).

Status labels as in the notes: [P] proved here, [V] exact computation (script cited), [T] cited theorem, [T*] cited statement whose super-VOA proof is only sketched in the literature.

Companions: `notes/blueprint/equivariant-quadrupling.md` [EQ] and `notes/blueprint/anomalies.md` [AN]. `notes/blueprint/orbifold-foundations.md` [OF] states every VOA input with sources (Li96, BK04, DZ05, DRY22, McR21, CM16) and proves the lattice-level steps in detail. Script: `ternary60/theory/mainq_orbifold_index.py` (log beside it).

--------------------------------------------------------------------------------------------

## 0. Result

**Theorem O.** Let C be a self-dual ternary code of length n = 12k with Index(C) = ±24, and let G ⊂ Aut(C) ⊂ 2ⁿ:Sₙ be one of the groups used for the Main Question:
- **(cyc)** ⟨g⟩ of order m = gcd(k, 24) ∈ {1, 2, 3, 4, 6, 12}, with GJF's conditions:
  - g^{m/2} = −1 if m is even;
  - if 3 | m, then h := g^{m/3} has no fixed coordinate (cycle shape 3^{n/3}) and T_h = 0.
- **(Q₈)** Q₈ = ⟨J, K⟩ with J² = K² = −1 and KJ = −JK (k ≡ 0 mod 8).
- **(Q₈×ℤ₃)** Q₈ × ⟨h⟩, with h of order 3 commuting with J and K, without fixed coordinate, and T_h = 0 (k ≡ 0 mod 24).

Here T_h := Σ_{x∈C, hx=x} f(x), with f(x) = Π φ(x_i) and φ = (0, −1, +1). It is defined up to a global sign ([MQ] Lemma 4.3).

The cases m ∈ {8, 24} cannot occur: (g^{m/8})⁴ = g^{m/2} = −1 forces 48 | Index(C) ([MQ] Thm 5.1).

Suppose the lift of G to V = V_{Λ(C)} (GJF Thm 3.1) is non-anomalous. Fix a trivialisation, and let W = V//G be the orbifold with the properties (ORB) of §1. Then, for every trivialisation,

  **Index(W) = ± Index(C)/|G| = ± 24/|G|.**

So the index is 24/m, 3 and 1 in the three cases.

Structure of the proof:
- §1: supersymmetry reduces every RR supertrace to the Ramond ground states (weight c/24). So Index(W) is the superdimension of the ground states of W_R, and a twisted sector can contribute only if it has states of weight c/24 (Cor 1.3).
- §2: the group theory.
- §3.1: for g of even order, V_{R,g} has lowest weight E_g = n/24 + n/(12m²) > c/24 (Lemma 3.3). So these sectors contribute nothing, with no projection formula or parity needed.
- §3.2: the untwisted sector gives Index(C)/|G|, because Z_RR(1, x) = 0 for x ≠ 1.
- §3.3: the sectors of order 3 (only when 3 | |G|) vanish by modular covariance, as in GJF.
- §4 collects the inputs; §5 lists the changes from the first version.

For Q₈ and for m ∈ {1, 2, 4} the proof uses no SL₂(ℤ)-transformation of twisted–twined traces. The cited inputs themselves (ORB, uniqueness of twisted modules) do rest on modular-invariance theorems.

--------------------------------------------------------------------------------------------

## 1. Setting, and the reduction to Ramond ground states

**Notation.**
- V = V_{Λ(C)}, c = n, σ = (−1)^F. τ is the N=1 supercurrent ([OF] Prop 2.6).
- G acts by even automorphisms fixing τ (hence ω), faithfully, with G ∩ ⟨σ⟩ = 1 ([OF] 5.0, Lemma 5.1).
- For g ∈ G, V_{R,g} := V(gσ) is the unique σ-stable irreducible gσ-twisted V-module, unique up to parity shift [T: DZ05 Thm 7.7, DRY22 Prop 3.4; [OF] Thm 4.1]. It is the *g-twisted Ramond sector*; V_R := V_{R,1}.
- For x ∈ C(g), an *x-intertwiner* on V_{R,g} is an invertible A with A Y(v,z) A⁻¹ = Y(xv, z).
  - One exists: x maps V_{R,g} to a σ-stable irreducible x(gσ)x⁻¹ = gσ-twisted module, which is ≅ V_{R,g} by uniqueness.
  - When V_{R,g} is of ℂ-type (Lemma 1.2), A is unique up to a scalar (Schur). So its parity p_g(x) ∈ ℤ/2 is well defined.
- Z_RR(g, A) := str_{V_{R,g}} A q^{L₀−c/24}.

**Lemma 1.1 (supertrace cancellation) [P; = [OF] Lemma 2.7].** On V_{R,g}, and on the Ramond sector W_R of W:
- the modes of τ are integral, and G₀² = κ(L₀ − c/24) with κ > 0;
  - κ = 1 for the normalisation of [OF] Prop 2.6;
  - κ = 3 for GJF's G = Σ_i (Γ_{+√3} + Γ_{−√3}), since G(z)G(w) ~ 2c(z−w)⁻³ + 6T(w)(z−w)⁻¹;
  - only κ ≠ 0 is used;
- every x-intertwiner A commutes with G₀, because x fixes τ.

Hence str A q^{L₀−c/24} = str_{(c/24)} A, the supertrace over the L₀ = c/24 eigenspace. In particular it is a constant, and it is 0 if there are no states of weight c/24.

*Proof.* If A is odd, every supertrace vanishes. If A is even, then on an eigenspace with L₀ ≠ c/24, G₀ is odd, invertible and commutes with A. So str A = str(G₀⁻¹AG₀) = −str A = 0. □

**(ORB) The orbifold [T*: [OF] Thm 5.4 and Hyp 5.5].** Given a non-anomalous G and a trivialisation, W = V//G is a holomorphic SVOA containing V^G with the same ω and τ. So it is N=1 ([OF] Prop 5.7). Its Ramond sector decomposes as W_R = ⊕_{[g]} W_{R,[g]}, over the conjugacy classes, where for a representative g:
- **(O2′)** W_{R,[g]} ⊂ V_{R,g} is a ℤ/2- and L₀-graded subspace;
- **(O2″)** if g has odd order, W_{R,[g]} = V_{R,g}^{C(g)} := {v : ρ_g(x)v = v for all x ∈ C(g)}, where ρ_g is a genuine representation of C(g) by x-intertwiners.

Sources:
- The formula W_R = ⊕ V_{R,g}^{C(g)} is asserted in GJF's proof of Thm 5.6, at the physics level ("the trivialisation is hidden in the notation"). GJF Thm 4.2 itself only builds the NS orbifold.
- For bosonic holomorphic VOAs the orbifold theory is a theorem: DNR25; Kirillov, Müger; McR21.
- The super version (a Lagrangian superalgebra from a trivialisation, and the Ramond decomposition) is folklore ([OF] Thm 5.4, item (2)). Regularity of V^G is a theorem: CM16 applied to V₀̄ ([OF] Thm 5.2).
- [OF] Hyp 5.5 states a stronger form (O1)–(O3). Only (O2′) for even-order g and (O2″) for g of odd order are used here; the conjugation compatibility (O3) and the class-sum formula are not.

**Remark (trivialisations).** A change of trivialisation can:
- multiply ρ_g by a character of C(g) (discrete torsion, or ψ ∈ Hom(G, U(1)) on V_R);
- shift the parity of a V_{R,g} (Arf-type stacking).

These changes multiply individual terms Z_RR(g, ρ_g(x)) by phases or signs. They do not act as one overall sign in general: for ℤ/2, stacking with Arf turns ½(Z₀₀+Z₀₁+Z₁₀+Z₁₁) into ½(Z₀₀−Z₀₁−Z₁₀−Z₁₁). Below, every term except (1, 1) vanishes for every normalisation. So the result holds for every trivialisation, up to the global parity of V_R.

**Lemma 1.2 (ℂ-type and evenness) [P, given T: [OF] Thm 5.3, Lemma 4.3; V: Part 2].** Let G be as in Theorem O.
- (i) Every V(g) and V_{R,g} (g ∈ G) is of ℂ-type (not Majorana).
- (ii) For g of odd order and x ∈ C(g), every x-intertwiner on V_{R,g} is even.

In particular the ρ_g(x) of (O2″) are even, and e_g := (1/|C(g)|) Σ_x ρ_g(x) is an even projector onto V_{R,g}^{C(g)}.

*Proof.*
- **(i)** The Majorana layer of the anomaly is the homomorphism G → ℤ/2 recording which V(g) are of Cl(1)-type (GJF §4). For g ∈ Aut(C) it is the character ε(g) = Π_i s_i ([OF] Lemma 4.3, from GJF Ex 4.4 and BK04: ⟨χ, (1−g)χ⟩ = 6·N₋(g), N₋(g) := #{i : s_i = −1}).
  - ε = 1 on all of G. [V: Part 2, every element of every group on every code.]
  - Directly: −1 has N₋ = n; J has one negative sign per 2-cycle, N₋ = n/2 = 6k; g of order 12 has one per 6-cycle, N₋ = 2k; odd-order elements have ε = 1 automatically.
  - V_R is ℂ-type ([OF] Prop 3.1(c)), and V_{R,g} ≅ V(g) ⊠ V_R.
- **(ii)** Put p(M, x) := parity of an x-intertwiner on a ℂ-type simple object M of Rep V. It is intrinsic: two x-intertwiners differ by an even scalar.
  - *Additivity.* If M ⊠ N ≅ P and A_M, A_N are x-intertwiners, then A_M ⊠ A_N, transported to P by any isomorphism φ, is an x-intertwiner on P: x acts on Rep V by monoidal functors, and the parity of φ cancels. So p(P, x) = p(M, x) + p(N, x).
  - V(g) ⊠ V(g′) ≅ V(gg′) in the G̃-crossed supercategory Rep V [T: McR21 Thms 4.15, 4.17; [OF] Thm 5.3].
  - p(V, x) = 0, since x is an even automorphism.
  - So a ↦ p(V(g^a), x) is a homomorphism ℤ/ord(g) → ℤ/2. It vanishes, since ord(g) is odd.
  - Then p(V_{R,g}, x) = p(V(g), x) + p(V_R, x) = p(V_R, x).
  - Finally p(V_R, x) = 0: an x-intertwiner maps the ground state e^{λ_w} to a multiple of e^{λ_{xw}} (§1.4). The parities are f(w) and f(xw) = ε(x)·f(w) ([OF] Prop 3.2(b); f(x·w) = (Π s)·f(w), EQ Lemma 1.3). And ε(x) = 1. □

**Corollary 1.3 (the reduction) [P, given ORB].**
- Index(W) := str_{W_R} q^{L₀−c/24} = sdim (W_R)_{c/24} = Σ_{[g]} sdim (W_{R,[g]})_{c/24} (Lemma 1.1 in W, with A = 1).
- If V_{R,g} has no states of weight c/24, then [g] contributes 0 (by (O2′) alone).
- If g has odd order, then by (O2″), Lemma 1.2 and Lemma 1.1:
  sdim (V_{R,g}^{C(g)})_{c/24} = (1/|C(g)|) Σ_{x∈C(g)} Z_RR(g, x), with Z_RR(g, x) := Z_RR(g, ρ_g(x)).
- If every class satisfied (O2″) and (O3), this would be the usual Index(W) = (1/|G|) Σ_{commuting (g,x)} Z_RR(g, x) ([OF] Prop 5.6; class-sum identity [V: Part 1]). That form is not needed. □

**(1.4) Ramond ground states of V ↔ maximal codewords [P, given T: Li96 Prop 5.4; = GJF Prop 2.4 "index = index", sign-exact in [OF] Prop 3.2].**
- V_R = V_{Λ+χ/2} with χ = √3·𝟙 characteristic. The parity of M(1) ⊗ e^λ is (−1)^{⟨χ,λ⟩}, unique up to one global sign ([OF] Prop 3.1).
- A Ramond momentum is ν = λ + χ/2 = (2y + 3·𝟙)/(2√3), with y ∈ ℤⁿ and y mod 3 ∈ C. So |ν|²/2 = Σ_i (2y_i + 3)²/24 ≥ n/24 = c/24.
  - Equality holds iff y_i ∈ {−1, −2} for every i. (y_i ≢ 0 mod 3 is not enough: y_i = 1 gives 25.)
  - Each maximal codeword has exactly one such lift. So the ground states are ℂe^{λ_w}, one for each maximal w ∈ C, with ν_w = ι(w)/(2√3), ι: F₃ → {0, 1, −1}. (The lift y reduces to −w; C = −C.)
- **Parity.** e^{λ_w} has parity (−1)^{Σy_i} = (−1)^{#{i: w_i = 1}} = f(w), with f(−w) = f(w) since n is even. So **Z_RR(1, 1) = Σ_w f(w) = Index(C)** exactly, with GJF's parity convention.
- **Twining.** x ∈ Aut(C) preserves Λ + χ/2, since (xχ − χ)/2 ∈ √3ℤⁿ ⊂ Λ, and xν_w = ν_{xw}.
  - Any x-intertwiner conjugates the Heisenberg zero modes by x, so it maps ℂe^{λ_w} onto ℂe^{λ_{xw}} [GJF Ex 4.4; [OF] Prop 3.3(i)].
  - So **Z_RR(1, x) only receives contributions from maximal codewords fixed by x.**

--------------------------------------------------------------------------------------------

## 2. Group theory [P; V: Part 1]

**Lemma 2.1.** In each G of Theorem O:
- (a) every pair of commuting elements generates a cyclic subgroup;
- (b) −1 is the unique involution of G, and it is a power of every element of even order;
- (c) the elements of odd order form a central subgroup ⟨h₃⟩ of order 3 (h₃ = g^{m/3}, resp. h), or just {1} if 3 ∤ |G|.

*Proof.*
- **Cyclic G.** (a) and (c) are clear. For (b): g^{m/2} = −1 by GJF's first condition, and g^{m/2} ∈ ⟨g^j⟩ for every g^j of even order.
- **Q₈.**
  - Every abelian subgroup is cyclic: the subgroups are 1, ⟨−1⟩, ⟨±J⟩, ⟨±K⟩, ⟨±JK⟩ and Q₈.
  - −1 is the unique involution and lies in every nontrivial subgroup.
- **Q₈ × ℤ₃.**
  - The abelian subgroups are A × B with A ⊂ Q₈ cyclic and B ⊂ ℤ₃. They are cyclic, since the orders are coprime.
  - An element (q, h^a) of even order has q ≠ 1, and (q, h^a)^{3·ord(q)/2} = (−1, 1) = −1.
  - h is central by hypothesis. □

Where each part is used:
- (b) is used in §3.1 and §3.2.
- (c) is used in §3.3: C(h₃) = G.
- (a) is used only through the modular covariance in §3.3: DZ05 Thm 7.7 makes the conformal-block space of a pair generating a cyclic group one-dimensional ([OF] Prop 4.8(b)).

--------------------------------------------------------------------------------------------

## 3. The terms

### 3.1 Elements of even order: no Ramond ground states [P, given T]

**Lemma 3.1 (lowest weight) [P, given T: FLM Thm 1.7.3, Lep85, DL96 (Heisenberg only); modular proof [OF] Prop 4.5].** Let g ∈ Aut(C) have no nonzero fixed vector on 𝔥 = ℂ ⊗ Λ(C), with eigenvalues e^{2πiθ_j}, θ_j ∈ (0, 1). Then the lowest L₀-eigenvalue of V_{R,g} is

  E_g := ¼ Σ_j θ_j(1 − θ_j) = (1/24) Σ_k d_k (k − 1/k)   (Frame shape Π_k k^{d_k}).

*Proof.*
- ω lies in the Heisenberg sub-VOA M(1) ⊂ V₀̄. σ acts trivially on M(1), and g acts on it through its linear action on 𝔥. So V_{R,g}, restricted to M(1), is a g-twisted M(1)-module, with L₀ = ω_{(1)}.
- Since g has no fixed vector, the g-twisted Heisenberg algebra has no zero modes. Every g-twisted M(1)-module with L₀ bounded below is then a direct sum of copies of the twisted Fock space S[g] [T: FLM Thm 1.7.3, a Stone–von Neumann-type complete reducibility].
- The lowest L₀-eigenvalue of S[g] is the twisted vacuum energy ¼ Σ θ_j(1−θ_j) [T: Lep85, DL96; FLM's 1/16 per dimension for θ = ½]. These sources treat even lattices, but only the bosonic M(1) enters here.
- [OF] Prop 4.5 gives a second proof that needs no explicit constant: S-transform Z_NS(1, ĝ) = 1/η_g and read off the leading exponent. It also proves that the two formulas for E_g agree. □
- *Remark (not needed).* σ = e^{2πi(χ/2)(0)} is inner. With (g⁻¹ − 1)a = χ/2, e^{2πia(0)} conjugates ĝ to ĝσ, so V_{R,g} ≅ V(ĝ) as graded spaces ([OF] Lemma 4.2). For odd lattices the structure V(ĝ) = S[g] ⊗ T_g, with dim T_g = |det(1−g)|^{1/2} in the Majorana-free case, is [BK04] ([OF] Prop 4.4).

**Lemma 3.2 (fixed-point-free coordinate permutations) [P; V: Part 2].** For G as in Theorem O, every g ∈ G ∖ {±1} has a fixed-point-free underlying permutation π_g. Hence tr_{ℝⁿ} g = 0 for g ∈ G ∖ {±1}.

*Proof.* Write g = x·y, with x the 2-part and y the 3-part (commuting powers of g). By Lemma 2.1, either x = ±1 or x has order 4 with x² = −1, and y ∈ ⟨h₃⟩.
- x of order 4: if π_x i = i, then xe_i = s e_i with s = ±1, so x²e_i = e_i ≠ −e_i. So π_x is fixed-point-free.
- y ≠ 1: π_{±y} = π_y = π_{h₃}^{±1} is fixed-point-free by hypothesis (shape 3^{n/3}).
- x of order 4 and y ≠ 1: π_x and π_y commute. If π_xπ_y i = i, put j := π_x i = π_y⁻¹ i. Then i = π_x j = π_xπ_y⁻¹ i = π_y⁻¹π_x i = π_y⁻² i, so π_y i = i, a contradiction.
- A signed permutation matrix with fixed-point-free π has zero diagonal, so its trace is 0. □
- For ⟨g⟩ of order 12 this says that every cycle of g has length 6 and, as g⁶ = −1, sign product −1. This is the cycle structure GJF use in their proof of Thm 5.6.

**Lemma 3.3 (vacuum energy of an element of even order) [P; V: Part 2].** Let g ∈ G have even order m. Then:
- g has no nonzero fixed vector on ℝⁿ;
- the eigenvalues of g are e^{2πis/m} with s odd, each with multiplicity 2n/m;
- **E_g = n/24 + n/(12m²) > n/24 = c/24.**

*Proof.*
- g^{m/2} is the unique involution in ⟨g⟩, so g^{m/2} = −1 (Lemma 2.1(b)).
- By Lemma 3.2 the character of ⟨g⟩ on ℝⁿ is χ(g^j) = n for j ≡ 0, −n for j ≡ m/2, and 0 otherwise (mod m).
- So the multiplicity of e^{2πis/m} is (1/m) Σ_j χ(g^j) e^{−2πisj/m} = (n/m)(1 − (−1)^s): it is 2n/m for odd s and 0 for even s. In particular 1 is not an eigenvalue.
- Put m = 2p. Then Σ_{s odd, s<m} (s/m)(1 − s/m) = (m·p² − p(4p²−1)/3)/m² = (2p² + 1)/(12p).
- So the mean of θ(1−θ) over the p odd phases is (2p² + 1)/(12p²) = 1/6 + 1/(3m²), and E_g = (n/4)(1/6 + 1/(3m²)) = n/24 + n/(12m²). □
- Values: m = 2: n/16; m = 4: 3n/64; m = 6: 19n/432; m = 12: 73n/1728. In units of n/4: 216, 162, 152, 146 out of 864, against 144 for c/24.
- Lemma 3.2 also gives the joint balance of eigenvalues that a case-by-case table would need. For example, for g = xh₃ of order 12 it forces the ω-eigenspace of h₃ to carry the eigenvalues ±i of x equally often.
- [V: Part 2] E_g = n/24 + n/(12m²) exactly, and the phase multiset equals {odd s/m, each 2n/m times}, for every element of even order of the group on each of these codes:
  - the J-chain (n = 48);
  - the ℤ/12-chains (n = 72, 108, 144; all of ⟨g⟩ is checked, which contains the groups ⟨g²⟩ and ⟨g⁴⟩ used at n = 72 and 108);
  - the Q₈-chain (n = 96);
  - the Q₈ × ℤ₃ seed and chain (n = 72, 144, 288).
  Other chain lengths are covered by the lemma itself.

**Corollary 3.4 [P, given T: [OF] Cor 4.6].** For g ∈ G of even order, V_{R,g} has no states of weight c/24. So:
- [g] contributes 0 to Index(W) (Cor 1.3, using only (O2′));
- Z_RR(g, A) = 0 for every x-intertwiner A, x ∈ C(g) (Lemma 1.1). This is used in §3.3.

### 3.2 The untwisted sector [P, given T: GJF Thm 3.1, BK04 Prop 4.1; cf. [OF] Prop 3.3]

By Cor 1.3 the contribution of [1] is (1/|G|) Σ_{x∈G} Z_RR(1, x), where ρ_1(x) is an x-intertwiner on V_R.
- **x = 1.** Z_RR(1, 1) = Index(C) (§1.4).
- **x of even order.**
  - A maximal codeword w with xw = w is also fixed by x^{ord(x)/2} = −1 (Lemma 2.1(b)). But −w ≠ w, since w has no zero entry.
  - So no ground-state line is mapped to itself, and Z_RR(1, x) = 0 (§1.4), for every normalisation of ρ_1(x).
- **x of order 3** (x ∈ ⟨h₃⟩ ∖ 1).
  - *The lift fixes V_{Λ^x} pointwise.* GJF's lift x̂ lies in Λ̂[2].Aut(C) and acts by e^λ ↦ ±e^{xλ} (±1-valued cocycle; [BK04] Prop 4.1, GJF §3). For λ ∈ Λ^x this gives x̂e^λ = u(λ)e^λ with u(λ) = ±1, and x̂³ = 1 forces u(λ) = 1.
  - *No uniqueness of the lift is used.* The order-3 lifts in Λ̂[2]·x̂ are the t·x̂ with t + xt + x²t = 0; there are 4^{n/3} of them. They are all Λ̂[2]-conjugate (Schur–Zassenhaus), but not unique. Lifts in ℂ*:Aut(C) outside Λ̂[2].Aut(C) can have different twining counts. Theorem O is about GJF's lift.
  - *One common eigenvalue.* Let A = ρ_1(x), with A³ = 1.
    - Any two x-fixed ground-state momenta differ by an x-fixed vector of Λ, so they lie in one coset of Λ^x.
    - For α ∈ Λ^x, the leading term of Y_R(e^α, z)e^λ is a nonzero multiple of e^{λ+α} ([OF] Prop 3.1).
    - A Y_R(e^α, z) A⁻¹ = Y_R(x̂e^α, z) = Y_R(e^α, z).
    - So A has one common eigenvalue ζ on all x-fixed ground states, with ζ³ = 1. The trivialisation fixes ζ; it is not forced to be 1.
  - Hence **Z_RR(1, x) = ζ·Σ_{y∈C, xy=y} f(y)** with the signed x. Non-maximal words have f = 0.
    - After a diagonal sign change making x a permutation, the sum is ±T_x ([MQ] Lemma 4.3).
    - T_{x²} = ±T_x, since x and x² have the same fixed vectors.
    - So Z_RR(1, h₃^{±1}) = ±ζ^{±1}T_h. It vanishes iff T_h = 0, i.e. iff C has as many even as odd h-fixed maximal codewords (GJF's condition).
  - [OF] Prop 3.3(iii) gives a second proof, via an h-fixed characteristic vector.
- **Conclusion.** The [1]-contribution is Index(C)/|G|, up to the global parity sign.

### 3.3 Twisted sectors of order 3 [P, given T: DZ05 Thms 4.12, 7.7 ([OF] Prop 4.8); GJF Thm 5.6, case m = 3]

This occurs only when 3 | |G|. Let g ∈ ⟨h₃⟩ ∖ 1. Then C(g) = G (Lemma 2.1(c)), and the contribution of [g] is (1/|G|) Σ_{x∈G} Z_RR(g, x) (Cor 1.3, Lemma 1.2).

- **Modular covariance** [T: DZ05 Thms 4.12, 7.7; [OF] Prop 4.8].
  - Let g, x commute and generate a cyclic group (Lemma 2.1(a)), and let γ = (a b; c d) ∈ SL₂(ℤ). Then Z_RR(g, x)(γτ) = c_γ·Z_RR(g^a x^c, g^b x^d)(τ) for some c_γ ∈ ℂ (possibly 0).
  - The RR (periodic–periodic) spin structure is SL₂(ℤ)-invariant, so the labels transform by the plain rule.
  - DZ05 needs C₂-cofiniteness and rationality for ⟨g, x, σ⟩. These are supplied by [OF] Prop 2.4 and Thm 5.2 (CM16 on V₀̄).
  - Only "Z_RR(γ-image) ≡ 0 ⇒ Z_RR(g, x) ≡ 0" is used, so the constant c_γ and the normalisation of ρ_g(x) never matter.
- **x of even order.** S = (0 −1; 1 0) carries (g, x) to (x, g⁻¹), and Z_RR(x, g⁻¹) = 0 by Cor 3.4. So Z_RR(g, x) = 0.
- **x = g^b ∈ ⟨g⟩.**
  - SL₂(ℤ) → SL₂(ℤ/3) is onto, and SL₂(ℤ/3) is transitive on (ℤ/3)² ∖ 0 [V: Part 1].
  - So some γ carries (g, g^b) to (1, g^d), with d ≠ 0.
  - Z_RR(1, g^d) = 0 by §3.2, hence Z_RR(g, g^b) = 0.
- So every Z_RR(g, x) vanishes, and [g] contributes 0. This is GJF's m = 3 argument, extended to the even-order x ∈ C(g).

### 3.4 Conclusion

Index(W) = (the [1]-contribution) + 0 = ±Index(C)/|G|. □

**Which inputs each case uses** [V: Part 3 classifies every pair].
- **Q₈ and m ∈ {1, 2, 4}.**
  - Every class except [1] has even order. So only (O2′) and (O2″) for [1] are used, and there ρ_1(x) is an explicit x-intertwiner.
  - No SL₂(ℤ)-transformation of twisted–twined traces is used.
  - The cited inputs (ORB, uniqueness of twisted modules) rest on modular-invariance theorems. For the twisted modules one can cite [BK04] instead.
- **m ∈ {3, 6, 12} and Q₈ × ℤ₃.** §3.3 uses the modular covariance [DZ05], as GJF do.

--------------------------------------------------------------------------------------------

## 4. Inputs, and what each case needs

| input | status | source | used in |
|---|---|---|---|
| (ORB) W = V//G exists, holomorphic, N=1; W_R = ⊕ W_{R,[g]} with (O2′), (O2″) | [T*] | GJF Thm 4.2 (super case sketched) and proof of Thm 5.6 (Ramond formula); bosonic: DNR25, Kirillov, Müger, McR21; regularity: CM16 on V₀̄ ([OF] Thm 5.2, 5.4, Hyp 5.5) | Cor 1.3 |
| V_{R,g} unique up to parity shift | [T] | DZ05 Thm 7.7, DRY22 Prop 3.4 ([OF] Thm 4.1); lattices: BK04 | §1 |
| Majorana layer ε(g) = Π s_i; ℂ-type sectors | [P, given T] | GJF Ex 4.4, BK04 ([OF] Lemma 4.3, Prop 4.4) | Lemma 1.2 |
| G̃-crossed structure: V(g) ⊠ V(g′) ≅ V(gg′), x acts monoidally | [T] | McR21 Thms 4.15, 4.17 ([OF] Thm 5.3) | Lemma 1.2 |
| N=1 on V_{R,g}: integral modes, G₀² = κ(L₀ − c/24) | [P, given T] | Li96 twisted Jacobi identity ([OF] Prop 2.6) | Lemma 1.1 |
| V_R = V_{Λ+χ/2}, parity (−1)^{⟨χ,λ⟩} | [P, given T] | Li96 Prop 5.4 ([OF] Prop 3.1) | §1.4 |
| ground states ↔ maximal codewords; Z_RR(1,1) = Index(C) exactly | [P] | GJF Prop 2.4 ([OF] Prop 3.2) | §1.4, §3.2 |
| GJF's lift lies in Λ̂[2].Aut(C) and acts by ±e^{gλ} | [T] | GJF Thm 3.1, BK04 Prop 4.1 | §3.2 |
| twisted Heisenberg modules without zero modes; vacuum energy | [T] | FLM Thm 1.7.3, Lep85, DL96 (bosonic M(1) only); modular proof [OF] Prop 4.5 | Lemma 3.1 |
| modular covariance of RR twisted–twined supertraces (cyclic ⟨g, x⟩) | [T] | DZ05 Thms 4.12, 7.7; vE13 ([OF] Prop 4.8) | §3.3 (not for Q₈, m ∈ {1, 2, 4}) |
| group theory; Lemmas 3.2, 3.3 | [P; V] | Parts 1–2 | §2, §3.1 |
| ε = 1 (N₋ even) on all of G | [P; V] | Part 2 | Lemma 1.2 |
| T_h = 0 on the chain codes | [P; V] | [MQ] Lemma 4.3, §4, §10 | §3.2 |

References: GJF = Gaiotto–Johnson-Freyd, *Holomorphic SCFTs with small index*; FLM = Frenkel–Lepowsky–Meurman 1988; Lep85 = Lepowsky, PNAS 1985; DL96 = Dong–Lepowsky 1996; Li96 = H. Li, *Local systems of twisted vertex operators* (1996); BK04 = Bakalov–Kac, *Twisted modules over lattice vertex algebras* (2004); DZ05 = Dong–Zhao, *Modularity in orbifold theory for vertex operator superalgebras* (2005); vE13 = van Ekeren 2013; DRY22 = Dong–Ren–Yang 2022; McR21 = McRae 2021; CM16 = Carnahan–Miyamoto; DNR25 = Dong–Ng–Ren. Full entries are in [OF].

--------------------------------------------------------------------------------------------

## 5. Changes from the first version (review of 2026-09-27)

- **Reduction to ground states (Cor 1.3).** Even-order classes now need only (O2′): no projection formula, parity, class-sum identity or conjugation compatibility. The class-sum form of the index formula is kept only as a remark.
- **§3.2, order-3 twining.**
  - The claim "the order-3 lift is unique" was false. There are 4^{n/3} order-3 lifts in Λ̂[2]·ĥ, all conjugate, and the proof uses GJF's lift.
  - The claim "acts on a fixed ground state by 1" was unjustified. The action is by one common cube root of unity ζ, so Z_RR(1, h) = ±ζT_h, which still vanishes iff T_h = 0.
- **Evenness of ρ_g(x) is proved** (Lemma 1.2), not dismissed.
- **The eigenvalue table is replaced by E_g = n/24 + n/(12m²)** (Lemmas 3.2–3.3). The proof also supplies the balance of joint eigenvalues that the table assumed but did not prove. Lemma 3.1 is proved via M(1), independent of the lift and of odd-lattice theory.
- **Smaller corrections.**
  - The equality condition in (1.4) is now y_i ∈ {−1, −2}, and the parity convention is made explicit.
  - G₀² = κ(L₀ − c/24).
  - ρ_g is renamed E_g, to avoid the clash with ρ_g(x).
  - m ∈ {8, 24} is excluded.
  - "Fixed-point-free on coordinates" and "on ℝⁿ" are now distinguished.
  - The trivialisation remark is corrected.
  - Citations: the Ramond decomposition is attributed to GJF's proof of Thm 5.6, the super orbifold theorem is marked [T*], BK04 is cited for odd lattices, and the dangling reference is replaced by [OF].
