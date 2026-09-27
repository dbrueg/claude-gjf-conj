# The index of the orbifolds used for the Main Question, including the non-cyclic groups

Proof file, started 2026-09-27. It proves that the orbifolds of `notes/main-question.md` have the claimed supersymmetric index: GJF Thm 5.6 (cyclic groups, §4), Cor 8.2 (Q₈), and Thm 10.1 (Q₈ × ℤ/3). Status labels as in the notes: [P] proved here, [V] exact computation (script cited), [T] cited theorem.

Script: `ternary60/theory/mainq_orbifold_index.py` (log beside it).

--------------------------------------------------------------------------------------------

## 0. Result

**Theorem O.** Let C be a self-dual ternary code of length n = 12k with Index(C) = ±24. Let G ⊂ Aut(C) ⊂ 2ⁿ:Sₙ be one of the groups used for the Main Question:
- ⟨g⟩ with m = ord g = gcd(k, 24), satisfying GJF's conditions (Thm 5.6);
- Q₈ = ⟨J, K⟩ with J² = K² = −1 (k ≡ 0 mod 8);
- Q₈ × ⟨h⟩ with h of order 3, fixed-point-free on coordinates, T_h = 0 (k ≡ 0 mod 24).

Suppose G acts non-anomalously on V = V_{Λ(C)} (GJF's lift, Thm 3.1), and fix a trivialisation. Then the orbifold W = V//G is a holomorphic N=1 SVOA of central charge 12k with

  **Index(W) = ± Index(C)/|G| = ± 24/|G|.**

So the index is 24/m, 3 and 1 in the three cases.

Structure of the proof:
- §1 gives the index formula as a sum over commuting pairs.
- §2 gives the group theory: every commuting pair generates a cyclic subgroup, and every element of even order has −1 as a power.
- §3 shows that each twisted–twined term vanishes. Most terms vanish directly, because the twisted Ramond sector of a fixed-point-free element has lowest weight > c/24. The rest are the terms inside the order-3 subgroup, handled as in GJF.
- §4 collects the inputs.

For Q₈ (§3.5) the proof uses no modular transformation at all.

--------------------------------------------------------------------------------------------

## 1. The index formula [T: GJF §5 (proof of Thm 5.6); P]

Notation.
- V is a holomorphic SVOA with an N=1 supercurrent τ (odd, weight 3/2); c = n. G acts by even automorphisms fixing τ.
- For g ∈ G, V_{R,g} is the unique irreducible g(−1)^F-twisted V-module: the "g-twisted Ramond sector" [T: uniqueness for holomorphic V, Dong–Li–Mason, van Ekeren].
- A trivialisation of the anomaly gives, for commuting g, h, an action ρ_g(h) of the centraliser C(g) on V_{R,g}, and parities on the V_{R,g}.

**(1.1) RR index of a twisted sector.** Z_RR(g, h) := str_{V_{R,g}} ρ_g(h) q^{L₀ − c/24}.
- τ is g-invariant and (−1)^F-odd, so on V_{R,g} its modes G_r have r ∈ ℤ, and G₀² = L₀ − c/24 (N=1 algebra, Ramond sector).
- ρ_g(h) commutes with G₀, since h fixes τ. (If ρ_g(h) is odd its supertrace vanishes anyway.)
- On every L₀-eigenspace with L₀ ≠ c/24, G₀ is an odd invertible operator commuting with ρ_g(h). So the supertrace of ρ_g(h) there is 0.
- Hence Z_RR(g, h) is the constant str ρ_g(h) over the L₀ = c/24 eigenspace of V_{R,g}. **In particular Z_RR(g, h) = 0 whenever the lowest L₀-eigenvalue of V_{R,g} exceeds c/24.** [P]

**(1.2) Index of the orbifold.** The Ramond sector of W is W_R = ⊕_{[g]} V_{R,g}^{C(g)} (sum over conjugacy classes, invariants under ρ_g) [T: GJF §4–5]. Its RR index is
- Index(W) = str_{W_R} q^{L₀ − c/24} = Σ_{[g]} (1/|C(g)|) Σ_{h ∈ C(g)} Z_RR(g, h).
- Conjugation by G identifies V_{R,g} with V_{R,xgx⁻¹} compatibly with the ρ's, so Z_RR(g, h) = Z_RR(xgx⁻¹, xhx⁻¹).
- There are |G|/|C(g)| elements in the class of g. So Index(W) = (1/|G|) Σ_{commuting (g,h)} Z_RR(g, h) [P; V: class-sum identity checked in Part 1].

**(1.3) The untwisted terms.** Z_RR(1, 1) = str_{V_R} q^{L₀−c/24} = ±Index(C) [T: GJF Prop "index = index"].
- The Ramond sector is V_R = V_{Λ(C)+χ/2}, χ = √3(1,…,1).
- λ = (2y + 3·𝟙)/(2√3) with y mod 3 ∈ C has |λ|² = |2y+3𝟙|²/12 ≥ n/12, with equality iff every y_i ≡ 1, 2 mod 3. So the ground states (weight c/24 = n/24) are e^λ, one for each maximal codeword y mod 3, with parity the codeword's parity.
- Z_RR(1, h) = str of ρ(h) on these ground states. ρ(h) maps e^λ to a multiple of e^{hλ}. **So Z_RR(1, h) only receives contributions from maximal codewords fixed by h** [P, given T: GJF Thm 3.1].

The index is defined up to sign: the parity of V_R, and the choice of trivialisation (a fermionic trivialisation choice changes the RR partition functions by Arf signs), change Index(W) by an overall sign at most. Only vanishing matters for the twisted terms below.

--------------------------------------------------------------------------------------------

## 2. Group theory [P; V: Part 1]

**Lemma 2.1.** In each G of Theorem O:
- (a) every pair of commuting elements generates a cyclic subgroup;
- (b) every element of even order has a power equal to −1, the unique involution of G;
- (c) the elements of odd order form the subgroup ⟨h₃⟩ of order 3 (h₃ = g^{m/3}, resp. h), or just {1} if 3 ∤ |G|.

*Proof.*
- Cyclic G: (a) and (c) are clear. For (b): g^{m/2} = −1 by GJF's condition (1), and every element g^j of even order has g^{m/2} ∈ ⟨g^j⟩.
- Q₈: every abelian subgroup is cyclic (the subgroups are 1, ⟨−1⟩, ⟨±i⟩, ⟨±j⟩, ⟨±k⟩, Q₈). −1 is the unique involution and lies in every nontrivial subgroup.
- Q₈ × ℤ₃: the abelian subgroups are A × B with A ⊂ Q₈ cyclic and B ⊂ ℤ₃, hence cyclic, since the orders are coprime. An element (q, h^a) of even order has q ≠ 1, and its power (q, h^a)^{3·ord(q)/2} = (−1, 1) = −1. □

--------------------------------------------------------------------------------------------

## 3. The twisted terms vanish

### 3.1 Fixed-point-free elements [P, given T: lattice twisted modules]

**Lemma 3.1.** Let g ∈ Aut(C) act on ℝⁿ = Λ(C) ⊗ ℝ without nonzero fixed vector, with eigenvalues e^{2πiθ_j}, θ_j ∈ (0, 1). Then the lowest L₀-eigenvalue of V_{R,g} is

  ρ_g = ¼ Σ_j θ_j(1 − θ_j).

*Proof.*
- (−1)^F = e^{2πi (χ/2)(0)} is inner. Since 1 − g is invertible over ℚ, choose a ∈ ℚ ⊗ Λ with (g⁻¹ − 1)a = χ/2. Then e^{2πi a(0)} conjugates g to g(−1)^F, so V_{R,g} ≅ V_g as graded spaces (the conformal vector is fixed).
- For fixed-point-free g, the g-twisted module of the lattice (S)VOA is V_g = S[g] ⊗ T_g [T: Lepowsky 1985, Dong–Lepowsky, Bakalov–Kac]. S[g] is the Fock space of the twisted Heisenberg algebra (modes α(m), m ∈ θ_j + ℤ on the e^{2πiθ_j}-eigenline), and T_g is finite-dimensional of a single weight.
- The lowest weight is the twisted vacuum energy ¼ Σ_j θ_j(1−θ_j). This equals (1/24) Σ_k d_k(k − 1/k) for Frame shape Π k^{d_k}; e.g. n/16 for −1 and 3n/64 for J. □

**Corollary 3.2.** If ρ_g > c/24 = n/24, i.e. the mean of θ_j(1−θ_j) exceeds 1/6, then Z_RR(g, h) = 0 for every h ∈ C(g) (by (1.1)).

**Lemma 3.3 (the elements of even order) [P; V: Part 2].** Every element g ∈ G of even order is fixed-point-free on ℝⁿ and has ρ_g > n/24.

*Proof.* By Lemma 2.1(b) some power of g is −1. If gv = v then (−1)v = v, so v = 0. For the weight, list the eigenvalue types.
- **ℝⁿ as a G-module.** −1 acts as −1. An element x of order 4 with x² = −1 has eigenvalues ±i. The order-3 element h₃ (fixed-point-free on coordinates, cycle shape 3^{n/3}) permutes the coordinates in 3-cycles. In each case below, ℝⁿ is a sum of copies of a rep where h₃ acts through the regular representation of ℤ₃, commuting with the 2-part:
  - Q₈ × ℤ₃: ℝⁿ ≅ k·(H ⊗ ℝ[ℤ₃]), since h permutes the Q₈-orbits in triples (Morita form, notes §9).
  - ⟨g⟩ of order 12: a 6-cycle with sign product −1 splits the same way.
- **Phases θ (mod 1) of g = x·h₃^a** (x the 2-part, a the 3-part):

  | g | θ | mean θ(1−θ) | vs 1/6 = 144/864 |
  |---|---|---|---|
  | −1 | ½ | 1/4 = 216/864 | > |
  | order 4 (x² = −1) | ¼, ¾ | 3/16 = 162/864 | > |
  | −h₃^{±1} (order 6) | ½, ⅙, ⅚ | 19/108 = 152/864 | > |
  | x h₃^{±1}, x of order 4 (order 12) | 1/12, 3/12, 5/12, 7/12, 9/12, 11/12 | 146/864 | > (just) |

  The same table covers ⟨g⟩ of order 12 (g, g⁵, g⁷, g¹¹ of order 12; g², g¹⁰ of order 6; g³, g⁹ of order 4; g⁶ = −1).
- [V: Part 2] ρ_g − n/24 > 0 is checked exactly (from the actual signed cycle structure) for every element of even order of the groups on the actual codes: the J-chain (n = 48), the ℤ/12-chains (n = 72, 108, 144), the Q₈-chain (n = 96), and the Q₈ × ℤ₃ seed and chain (n = 72, 144, 288). □

So **Z_RR(g, h) = 0 whenever g has even order** (Cor 3.2).

### 3.2 Untwisted terms with h ≠ 1 [P, given T: GJF Prop "index = index", Thm 3.1]
- **h of even order.** A maximal codeword c fixed by h (as a signed permutation, h·c = c) is fixed by −1 (Lemma 2.1(b)). But −c ≠ c since c has no zero entry. So h fixes no maximal codeword, and Z_RR(1, h) = 0 by (1.3).
- **h of odd order, h ≠ 1.** Then h ∈ ⟨h₃⟩ has order 3.
  - The lift of h is unique: an element of order 3 in Λ̂[2].Aut(C) has a unique lift of order 3, since Λ̂[2] is a 2-group.
  - It acts on a fixed ground state e^λ by a cube root of unity that is also a sign, i.e. by 1.
  - So Z_RR(1, h) = Σ_{maximal c, hc = c} (−1)^{parity(c)} = ±T_h. Here T_h = Σ_{x ∈ C^h} f(x), f(x) = Π φ(x_i), after the diagonal sign change making h a permutation (notes §4).
  - T_{h²} = T_h, since h and h² have the same fixed vectors.
  - The hypothesis T_h = 0 gives Z_RR(1, h^{±1}) = 0.

### 3.3 Twisted terms (g, h) with g of odd order ≠ 1 and h of even order [P, given T: modular covariance of RR twisted–twined supertraces]
- By Lemma 2.1(a), ⟨g, h⟩ is cyclic of even order.
- The modular S-transformation maps Z_RR(g, h) to Z_RR(h, g⁻¹) up to a nonzero constant [T: Dong–Li–Mason 2000 and van Ekeren 2013 for super (Ramond) twisted modules; this is the modular covariance GJF use]. Covariance holds up to phase for any choice of lifts.
- Z_RR(h, g⁻¹) = 0 by §3.1 (h has even order). So Z_RR(g, h) = 0.

### 3.4 Terms inside the subgroup of order 3 [T: GJF Thm 5.6, case m = 3]
- The 8 pairs (h^a, h^b) ≠ (1,1) with h = h₃: those with a = 0 vanish by §3.2.
- Those with a ≠ 0 are carried to a pair (1, h^d) by an element of SL₂(ℤ) (the SL₂(ℤ)-orbit of (a, b) ∈ (ℤ/3)² ∖ 0 contains (0, 1)), up to a nonzero constant [T: modular covariance]. So they vanish as well.
- This is exactly GJF's m = 3 argument.

### 3.5 Conclusion
All terms other than (1,1) vanish. So Index(W) = (1/|G|)·Z_RR(1,1) = ±Index(C)/|G|. □

**Q₈ needs no modular transformation.** Every element of Q₈ ∖ {1} has even order. So every pair (g, h) ≠ (1,1) is either (1, h) with h of even order (§3.2) or (g, h) with g of even order (§3.1). The proof of Cor 8.2 then uses only (1.1)–(1.3), Lemma 3.1 and GJF Prop "index = index".

The same holds for the cyclic cases m ∈ {2, 4} of GJF Thm 5.6. For m ∈ {3, 6, 12} and for Q₈ × ℤ₃, the order-3 terms of §3.3–3.4 use modular covariance, as in GJF.

--------------------------------------------------------------------------------------------

## 4. Inputs, and what each case needs

| input | status | used for |
|---|---|---|
| orbifold W = ⊕ V_{R,g}^{C(g)} exists, N=1, holomorphic, for a trivialised anomaly | [T] GJF Thm 4.2 (regularity of V^G: Carnahan–Miyamoto for solvable G, super case via the even part, see `notes/lean-blueprint.md`) | (1.2) |
| unique g-twisted Ramond module; N=1 modes on it | [T] DLM, van Ekeren; standard | (1.1), (1.2) |
| Ramond ground states of V_{Λ(C)} ↔ maximal codewords | [T] GJF Prop "index = index" (proof recalled in (1.3)) | (1.3), §3.2 |
| lift of Aut(C), unique for odd order | [T] GJF Thm 3.1 | §3.2 |
| twisted modules of lattice (S)VOAs for fixed-point-free g; vacuum energy | [T] Lepowsky, Dong–Lepowsky, Bakalov–Kac | Lemma 3.1 |
| modular covariance of RR twisted–twined supertraces, up to phase | [T] DLM 2000, van Ekeren 2013 | §3.3–3.4 (not for Q₈, m = 2, 4) |
| group theory, class sums, eigenvalue table | [P; V] | §1.2, §2, Lemma 3.3 |
| T_h = 0 on the chain codes | [P; V] notes §4 (Lemma 4.3), §10 | §3.2 |
