# Blueprint: the anomaly side of the Main Question

Proof file, 2026-09-27. Purpose: give Lean-ready statements and detailed proofs of every 't Hooft-anomaly computation used in the answer to GJF's Main Question, and isolate exactly what is cited. It covers:
- **(a)** GJF Ex 4.4 as used for cyclic groups: the Majorana-layer criterion ⟨χ,(1−g)χ⟩ ∈ 4ℤ, the Frame-shape formula α/(2m) ≡ m·ρ_g for fixed-point-free g, and the order-3 case with the "standard lift" (§1–§2);
- **(b)** for G = Q₈ × ℤ/3: the anomaly vanishes iff its restrictions to Q₈ and ℤ/3 vanish, with a full proof (Sylow detection for extended supercohomology, §3);
- **(c)** the Q₈ anomaly theorem of [MQ §8.4–8.5], reduced to a minimal chain of inputs, each with its status (§4).

The orbifold-index side (twisted sectors vanish, index 24/|G|) is in [OI]. The code-level machinery (chains, fixed codes) is in `notes/blueprint/equivariant-quadrupling.md`.

Sources: [MQ] = `notes/main-question.md`; [OI] = `notes/orbifold-index.md`; [I] = `notes/ternary-code-index.md`; [GJF] = Gaiotto–Johnson-Freyd, arXiv:1811.00589 (TeX in `literature/gjf-1811.00589.tex`; labels `thm.symmetries lift` = Thm 3.1, `thm.anomaly` = Thm 4.2, `eg.anomaly of a lattice automorphism` = Ex 4.4, `prop.index=index`, `thm.answers` = Thm 5.6). Status labels: [P] proved in this file, [T] cited (exact reference given), [V] exact or numerical computation (script cited), [H] heuristic.

Script: `ternary60/theory/blueprint_anomaly.py` (stdlib Python, ≈ 2 s), log `blueprint_anomaly.log` beside it: 53 checks, all pass. Parts 0–6 are cited below as [V: Part n].

--------------------------------------------------------------------------------------------

## 0. Summary for the formalizer

| # | statement | status | kind of proof |
|---|---|---|---|
| 1.4 | \|rSH³(ℤ/m)\| = 2m (m even), m (m odd); \|rSH³(Q₈)\| = 32 | [P given (A5), T: group cohomology; V: Part 4] | exact sequences + finite cohomology |
| 1.5 | e_m: rSH³(ℤ/m) → U(1) is injective; q² rule | [P given (A7); V: Part 0] | theta/eta transformation |
| 2.2 | ⟨χ,(1−g)χ⟩ = 6·N₋(g); Majorana layer of g = N₋(g) mod 2, a homomorphism on 2ⁿ:Sₙ | [P given (A6); V: Part 1] | algebra |
| 2.3, 2.3′ | cycle structure forced by GJF's conditions; the Majorana layer vanishes for every group used | [P; V: Part 1] | cycle combinatorics |
| 2.4 | all lifts of a fixed-point-free g are conjugate | [P given (A8)] | divisibility of U(1) |
| 2.6 | fixed-point-free g: α/m′ ≡ L·ρ_g (GJF's Frame-shape formula) | [P given (A7), (A8); V: Parts 2–3] | eta transformation |
| 2.7 | an odd-order lift in Λ̂[2].O(Λ) is standard | [P given (A8)] | one line |
| 2.8 | odd m, standard lift: α/m ≡ 2m·ρ_g; h of shape 3^{n/3}: α = 2k ∈ ℤ/3 | [P given (A7), (A8); V: Part 3] | theta + eta transformation |
| 2.9 | every element used: α = 2k ∈ ℤ/m′, zero iff m \| k | [P; V: Part 2] | rational arithmetic |
| 3.2 | α ∈ S̃H³(G) vanishes iff all its Sylow restrictions vanish | [P given (A2), (A5), T: transfer] | diagram chase |
| 3.3 | Q₈ × ℤ/3: α = 0 iff α\|Q₈ = 0 and α\|ℤ/3 = 0 | [P; V: Part 4] | from 3.2 |
| 3.5 | the anomaly of Q₈ × ℤ/3 in [MQ Thm 10.1] vanishes for 24 \| k | [P given 4.1, 2.8, 3.3] | assembly |
| 4.3 | cyclic kernel of rSH³(Q₈) is {0, κ} | [P given 1.4, 1.5, 4.2; V: Part 4] | counting, no eta invariants |
| 4.5 | (−1)-twisted ground states: T ≅ ⊗_O(ρ₂ ⊕ 2·1), t_x = 2^{3k} | [P given (A10); V: Part 5] | Spin(4), finite |
| 4.6 | three eta identities | [P; V: Part 6] | eta transformation, Euler |
| 4.7 | non-anomalous Q₈ with 4 \| k forces 8 \| k | [P given (A1), (A9)–(A11), 4.5, 4.6; V: Part 6] | character S-invariance |
| 4.1 | GJF's Q₈-action is non-anomalous iff 8 \| k | [P given the above] | assembly |

**Cited inputs, in one place** (§1.2): (A1) GJF Thm 4.2 and regularity; (A2) restriction; (A3) conjugation; (A4) additivity; (A5) the layer exact sequences; (A6) Majorana layer = parity on the Ramond sector; (A7) the multiplier principle for cyclic groups; (A8) lifts of lattice automorphisms; (A9) S-invariance of holomorphic SVOA characters; (A10) lattice twisted modules; (A11) the structure of the orbifold. Plus standard group cohomology (§3.1, §4.2) and GJF Thm 3.1.

**Issues found:** see §6. None breaks a result; the main points are
- an imprecise "unique lift" claim in [OI §3.2];
- a gap in the by-hand remark of [MQ §8.4 step 1], closed here in a simpler way (Prop 4.3), which also removes the eta-invariant input;
- two typos in GJF's proofs;
- a citation gap in GJF's m = 3 step (Möller's thesis treats even lattices), closed here by Prop 2.8.

--------------------------------------------------------------------------------------------

## 1. Setting and the anomaly interface

### 1.1 Definitions

**Definition 1.1 (setting).**
- V is a holomorphic SVOA (C₂-cofinite, rational, with V itself its only irreducible NS module), of central charge c, with parity P = (−1)^F.
- V_R is its Ramond sector: the unique irreducible P-twisted module, defined up to a possibly odd isomorphism.
- A G-action is an injective homomorphism G → Aut(V) into even automorphisms.
- For an odd unimodular lattice Λ, V_R = V_{Λ+χ/2} with χ a characteristic vector, and the parity of M_{λ+χ/2} is (−1)^{⟨χ,λ⟩} [GJF §2, before `prop.index=index`].

**Definition 1.2 (the code VOAs).** C ⊂ F₃ⁿ is self-dual, n = 12k.
- Λ = Λ(C) = {x̃/√3 : x̃ ∈ ℤⁿ, x̃ mod 3 ∈ C}; it is odd unimodular.
- The frame is F = V_{√3ℤ}^{⊗n} ⊂ V = V_Λ.
- χ = √3·𝟙 is characteristic: ⟨χ, x̃/√3⟩ = Σx̃_i and λ² = Σx̃_i²/3. Since Σx̃_i² ≡ 0 (mod 3) and 3 is odd, Σx̃_i²/3 ≡ Σx̃_i² ≡ Σx̃_i (mod 2).
- Mon(n) = 2ⁿ:Sₙ. For g = (p, s) we set (g·x)_{p(i)} = s_i x_i, and N₋(g) := #{i : s_i = −1}.
- **GJF's lift** [T: GJF Thm 3.1] is a homomorphism s: Aut(C) → Λ̂[2].Aut(C) ⊂ Aut(V) whose restriction to F is the standard signed-permutation action: a sign change swaps Γ_{+√3} ↔ Γ_{−√3}.
- It is *unique*: restriction to F is injective on Λ̂[2].Aut(C), because Hom(Λ, ±1) → Hom(√3ℤⁿ, ±1) is an isomorphism (odd index). This is the argument of GJF's proof [P].
- Consequently, for C ⊕ C′ the lift is s_C ⊗ s_{C′} exactly: both restrict to the standard action on F_C ⊗ F_{C′}.

**Definition 1.3 (anomaly groups).** For a finite group G:
- S̃H³(G) is reduced extended supercohomology of BG in degree 3, and rSH³(G) is restricted supercohomology [GJF Def. in §4].
- The natural maps are
  - maj: S̃H³(G) → H¹(G;ℤ/2) (Majorana layer),
  - gw: rSH³(G) → H²(G;ℤ/2) (Gu–Wen layer),
  - ι₁: H³(G;U(1)) → rSH³(G) and ι₂: rSH³(G) → S̃H³(G).
- m′ := |rSH³(ℤ/m)| and L := m (m even), 2m (m odd).

### 1.2 The cited inputs (the "anomaly interface")

In a Lean formalization each of these is an axiom (or a structure field). Everything else in this file is proved from them.

- **(A1) Existence and meaning** [T: GJF Thm 4.2 (`thm.anomaly`), proof modelled on Kirillov, CMP 229 (2002); hypothesis "V^G regular" holds for G solvable by Carnahan–Miyamoto, arXiv:1603.05645, with the super case via the even part as remarked after GJF Thm 4.2].
  - A G-action has an anomaly α(V, G) ∈ S̃H³(G).
  - An orbifold V//G (a holomorphic SVOA) exists iff α = 0. The orbifolds form a torsor under S̃H̃²(G).
  - All groups used here are solvable.
- **(A2) Restriction and transport** [T: in GJF's construction the super fusion category of H-twisted sectors is the H-graded part of that of G].
  - α(V, H) = res^G_H α(V, G) for H ⊂ G.
  - α(V, ρ∘φ) = φ*α(V, ρ) for an isomorphism φ.
- **(A3) Conjugation** [T: transport of structure]: α(V, tρt⁻¹) = α(V, ρ) for t ∈ Aut(V).
- **(A4) Additivity** [T: anomalies form a group under stacking, GJF17 = Gaiotto–Johnson-Freyd, arXiv:1712.07950, §5]: α(V ⊗ V′, ρ ⊗ ρ′) = α(V, ρ) + α(V′, ρ′).
- **(A5) Layers** [T: GJF §4, the two long exact sequences following the definition of rSH and SH, and the sentence "for • = 3, we have inclusions H³ ↪ rSH³ ↪ SH³"; Wang–Gu arXiv:1703.10937; GJF17 §5.4]. The following sequences are exact and natural in G:
  - H³(G;U(1)) →ι₁ rSH³(G) →gw H²(G;ℤ/2) → H⁴(G;U(1)), with ι₁ injective;
  - rSH³(G) →ι₂ S̃H³(G) →maj H¹(G;ℤ/2), with ι₂ injective.
- **(A6) Majorana layer from the Ramond sector** [T: GJF §4, paragraph "There is another description of the Majorana and Gu–Wen layers …", justified there through the bosonic shadow, BGK16 = Bhardwaj–Gaiotto–Kapustin arXiv:1605.01640].
  - maj(α)(g) = 0 iff an (any) operator on V_R implementing g is even.
  - For free fermions Fer(ρ), ρ: G → O(d), the zero modes of V_R form Cl(d), and g acts through a Pin(d)-lift of ρ(g). That lift is even iff det ρ(g) = 1, so **maj = w₁(ρ) = det ρ** [P given (A6)].
- **(A7) Multiplier principle (MP) for cyclic groups** [T: GJF §4, paragraph before Ex 4.4. It is stated there without proof ("by studying the 2π/m-rotation of two free fermions, one finds …"), with "compare [GPRV13, §3]". Bosonic analogue: the "type" of a twisted sector, van Ekeren–Möller–Scheithauer, arXiv:1507.08142].
  - Let ⟨g⟩ ≅ ℤ/m act with maj(α) = 0.
  - Then Z^{1,g}/Z^{1,1}, where Z^{1,g} = tr_V g q^{L₀−c/24}, is an eigenfunction of S T^L S⁻¹.
  - Its eigenvalue e_m(α) ∈ U(1) depends only on α ∈ rSH³(ℤ/m), and e_m is a homomorphism.
- **(A8) Lifts of lattice automorphisms** [T: Lepowsky, PNAS 82 (1985) 8295; FLM Ch. 9–10; Dong–Nagatomo, Contemp. Math. 248 (1999), arXiv:math/9808088; surveyed in Möller's thesis §5.3, as GJF say. The super (odd-lattice) case is identical]. For Λ integral and g ∈ O(Λ):
  - (i) the automorphisms of V_Λ that preserve M(1) (the Heisenberg subVOA) and induce g on 𝔥 = Λ ⊗ ℂ form a torsor under the torus T_Λ = {e^{2πi v(0)}} ≅ Hom(Λ, U(1));
  - (ii) each acts as ĝ(u ⊗ e^λ) = η(λ)·gu ⊗ e^{gλ} on V_Λ = ⊕_λ M(1) ⊗ e^λ, with η: Λ → U(1);
  - (iii) Λ̂[2].O(Λ) consists of those with η(λ) ∈ {±1};
  - (iv) the lift ĝ acts on each V_Λ-module V_{Λ+ν} by mapping M(1) ⊗ e^{λ+ν} to M(1) ⊗ e^{g(λ+ν)} (this is how GJF compute on V_R).
- (A9), (A10), (A11) are only used in §4 and are stated there.

### 1.3 Consequences for the anomaly groups

**Lemma 1.4 (orders) [P given (A5); T: H^{2j}(G;ℤ) ≅ ℤ/|G| and H^{odd>0}(G;ℤ) = 0 for G cyclic or Q₈ (periodic cohomology: Cartan–Eilenberg Ch. XII §7, Brown VI.9, item numbers not checked); V: Part 4 for H^{≤2}(−;F₂)].**
- (a) m odd: rSH³(ℤ/m) = S̃H³(ℤ/m) = ι₁H³(ℤ/m;U(1)) ≅ ℤ/m.
- (b) m even: |rSH³(ℤ/m)| = 2m.
- (c) |rSH³(Q₈)| = 32, and gw: rSH³(Q₈) → H²(Q₈;ℤ/2) ≅ (ℤ/2)² is onto.

*Proof.*
- For finite G, H³(G;U(1)) ≅ H⁴(G;ℤ) and H⁴(G;U(1)) ≅ H⁵(G;ℤ) (Bockstein of 0 → ℤ → ℝ → U(1) → 0, since H^{>0}(G;ℝ) = 0).
- For G cyclic or Q₈ these are ℤ/|G| and 0. So by (A5) the sequence 0 → ℤ/|G| → rSH³(G) → H²(G;ℤ/2) → 0 is exact.
- H²(ℤ/m;ℤ/2) is ℤ/2 for m even and 0 for m odd. H²(Q₈;ℤ/2) ≅ (ℤ/2)² [V: Part 4].
- For m odd also H¹(ℤ/m;ℤ/2) = 0, so ι₂ is onto. □

**Lemma 1.5 (calibration of MP; the q² rule) [P given (A6), (A7); V: Part 0].** Let ν_{m,q} be the anomaly of ℤ/m acting on Fer(2) = V_ℤ by rotating the two Majoranas through 2πq/m, i.e. by ζ^{pq} on charge p, with ζ = e^{2πi/m}. Put ν_m := ν_{m,1}.
- (a) e_m(ν_{m,q}) = exp(2πi q²/m′).
- (b) e_m is injective, and rSH³(ℤ/m) = ⟨ν_m⟩ ≅ ℤ/m′.
- (c) **q² rule:** ν_{m,q} = q²·ν_m.
- (d) Writing α = a·ν_m, we have e_m(α) = e^{2πia/m′}, and α = 0 iff e_m(α) = 1.

*Proof.*
- Rotations lie in SO(2), so maj = 0 by (A6) and (A7) applies.
- The two characters are Z^{1,1} = Σ_p q^{p²/2}/η and Z^{1,g} = Σ_p ζ^{pq} q^{p²/2}/η.
- Poisson summation gives (Σ_p ζ^{pq}q^{p²/2})|S = (−iτ)^{1/2} Σ_p q^{(p+q/m)²/2}. Hence (Z^{1,g}/Z^{1,1})|S = Σ_p q^{(p+q/m)²/2} / Σ_p q^{p²/2}.
- T^L multiplies q^{(p+q/m)²/2} by e^{2πi(Lp²/2 + Lpq/m + Lq²/2m²)}.
  - m even (L = m): mp²/2 ∈ ℤ and pq ∈ ℤ, so the factor is e^{2πiq²/2m}.
  - m odd (L = 2m): the factor is e^{2πiq²/m}.
  - The denominator is T^L-invariant.
- This proves (a).
- (b) By (a), e_m(ν_m) has order m′ = |rSH³(ℤ/m)| (Lemma 1.4). Since e_m is a homomorphism, ⟨ν_m⟩ has at least m′ elements, so it is everything and e_m is injective.
- (c) follows from (a) and injectivity, and (d) is (b). □

--------------------------------------------------------------------------------------------

## 2. Cyclic groups on V_{Λ(C)}: GJF Ex 4.4 as used

**Definition 2.1 (signed cycles, Frame shapes, ρ_g).**
- A signed cycle of g = (p, s) is a cycle of p of length ℓ together with its sign product σ.
- On ℝⁿ it contributes the eigenvalues e^{2πiθ} with θ = (j + [σ = −1]/2)/ℓ, j = 0, …, ℓ−1.
- It contributes the Frame-shape factor ℓ¹ if σ = 1 and ℓ⁻¹(2ℓ)¹ if σ = −1, since 1 + x^ℓ = (1 − x^{2ℓ})/(1 − x^ℓ). In general det(1 − g x) = Π_k (1 − x^k)^{d_k}.
- ρ_g := ¼ Σ_j θ_j(1 − θ_j) = (1/24) Σ_k d_k (k − 1/k). For one unsigned ℓ-cycle, ¼Σ_j (j/ℓ)(1 − j/ℓ) = (ℓ² − 1)/(24ℓ).
- g is fixed-point-free on ℝⁿ iff no θ_j = 0, i.e. iff every signed cycle has σ = −1. Then Σ_k d_k = 0.
- Every k with d_k ≠ 0 divides ord(g): ℓ | ord g, and if σ = −1 then g^ℓ = −1 on that cycle, so 2ℓ | ord g.

**Lemma 2.2 (Majorana layer) [P given (A6), (A8)(iv); V: Part 1].** For g ∈ Aut(C) with lift ĝ = s(g):
- (a) ⟨χ, (1−g)χ⟩ = 6·N₋(g).
- (b) ĝ maps M_{λ+χ/2} ⊂ V_R to M_{μ+χ/2} with μ = gλ + (gχ − χ)/2 ∈ Λ, and multiplies the parity (−1)^{⟨χ,λ⟩} by (−1)^{N₋(g)}.
- (c) Hence the Majorana layer of ⟨g⟩ is maj(g) = N₋(g) mod 2, i.e. maj(g) = 0 ⟺ Π_i s_i = 1 ⟺ ⟨χ,(1−g)χ⟩ ∈ 4ℤ (GJF's criterion).
- (d) g ↦ Π_i s_i is a homomorphism Mon(n) → {±1}. So for every G ⊂ Aut(C), maj(α_G) is the restriction of this character (by (A2)), and it vanishes iff it vanishes on generators.

*Proof.*
- (a) ⟨χ,χ⟩ = 3n and (gχ)_{p(i)} = √3 s_i, so ⟨χ,gχ⟩ = 3Σs_i = 3(n − 2N₋).
- (b) gχ is characteristic (g is an isometry), so ⟨gχ − χ, λ⟩ ≡ λ² − λ² = 0 (mod 2) and (gχ − χ)/2 ∈ Λ* = Λ. By (A8)(iv), ĝ maps M_{λ+χ/2} to M_{g(λ+χ/2)} = M_{μ+χ/2}.
- Since ⟨χ, gλ⟩ ≡ (gλ)² = λ² ≡ ⟨χ,λ⟩, we get ⟨χ,μ⟩ = ⟨χ,gλ⟩ + ½⟨χ, gχ − χ⟩ ≡ ⟨χ,λ⟩ − 3N₋(g) (mod 2).
- In coordinates: μ = x̃′/√3 with x̃′_{p(i)} = s_i x̃_i + (3/2)(s_i − 1) ∈ ℤ, so Σx̃′ ≡ Σx̃ + N₋ (mod 2) [V: Part 1, random λ on every code].
- (c) By (A6), maj(g) is the parity of ĝ on V_R.
- (d) For gh = (p_g p_h, i ↦ s_h(i) s_g(p_h(i))) the sign product is multiplicative. □

**Lemma 2.3 (cycle structure) [P].** Let g ∈ Mon(n) and j ≥ 1.
- (a) g^j = −1 iff every signed cycle of g has length ℓ | j with j/ℓ odd and σ = −1. (On a signed ℓ-cycle, g^j is diagonal iff ℓ | j, and then it equals σ^{j/ℓ}.)
- (b) Suppose g satisfies GJF's conditions: m = ord g ∈ {2, 4, 6, 12}, g^{m/2} = −1, and if 3 | m then g^{m/3} has cycle shape 3^{n/3}. Then every cycle has length exactly m/2 and σ = −1:
  - m = 2: g = −1 itself, so ℓ = 1.
  - m = 4: ℓ ∈ {1, 2} with 2/ℓ odd, so ℓ = 2.
  - m = 6: ℓ ∈ {1, 3}. But ℓ = 1 would make g² trivial on that coordinate, contradicting shape 3^{n/3}.
  - m = 12: ℓ ∈ {2, 6}. But ℓ = 2 would make g⁴ = σ² = 1 on that 2-cycle.
  - So the Frame shape is (m/2)^{−2n/m} m^{2n/m}.
- (c) An element h of order 3 with cycle shape 3^{n/3} has σ = +1 on every cycle (h³ = σ there), hence an even number of −1's per cycle, and Frame shape 3^{n/3}.

**Corollary 2.3′ (Majorana layer vanishes for all groups used) [P; V: Part 1].**
- g = −1: N₋ = 12k.
- g² = −1 (J, K, JK, the J-chain J): one sign −1 per 2-cycle, so N₋ = n/2 = 6k.
- GJF-type g of order m ∈ {2, 4, 6, 12}: N₋ ≡ #cycles = 24k/m (mod 2), and 24/m is even.
- h as in 2.3(c): N₋ is even.
- By 2.2(d) the layer vanishes on every group generated by these: ⟨g⟩ for the ℤ/12-chains, Q₈ = ⟨J, K⟩, Q₈ × ⟨h⟩.
- [V: Part 1] checked on every element of the groups on the J-chain (n = 48), the ℤ/12 seed and chains (n = 36, 72, 108), the tetracode sums D48 and D96, and the Q₈×ℤ₃ seed and chain (n = 72, 144, 288).

**Lemma 2.4 (all lifts of a fixed-point-free g are conjugate) [P given (A8)(i)].** Let g ∈ O(Λ) with 1 − g invertible on 𝔥. Then any two lifts are conjugate by an element of T_Λ.
- Consequently every lift has the order of GJF's lift s(g), namely ord g. Its anomaly is α_{⟨s(g)⟩} by (A3), and GJF's extra hypothesis "the lift has order m" is automatic.

*Proof.*
- Write ĝ′ = ĝ t₀ with t₀ ∈ T_Λ = Hom(Λ, U(1)).
- For t ∈ T_Λ, ĝ⁻¹tĝ acts on e^λ by t(gλ). So t ĝ t⁻¹ = ĝ·(t∘(g − 1)).
- g − 1: Λ → Λ is injective with finite cokernel, and U(1) is divisible, hence an injective ℤ-module. So t ↦ t∘(g − 1) is onto T_Λ, and we may choose t with t∘(g−1) = t₀. □

**Lemma 2.5 (character of a lift) [P given (A8)(ii)].** For a lift ĝ of finite order with phase function η:
- Z^{1,ĝ}(τ) = Θ_{Λ^g, η}(τ)/η_g(τ), where Θ_{Λ^g,η} = Σ_{λ∈Λ^g} η(λ) q^{λ²/2} and η_g(τ) = Π_k η(kτ)^{d_k}.
- In particular Z^{1,ĝ} = 1/η_g if g is fixed-point-free.

*Proof.*
- ĝ maps M(1) ⊗ e^λ to M(1) ⊗ e^{gλ}, so only λ ∈ Λ^g contribute, each with factor η(λ)q^{λ²/2}.
- tr_{M(1)} g q^{L₀} = Π_{r≥1} det(1 − g q^r)⁻¹ = Π_r Π_k (1 − q^{kr})^{−d_k}.
- With q^{−c/24} and c = n = Σ_k k d_k this is 1/η_g. □

**Proposition 2.6 (Frame-shape formula; GJF Ex 4.4) [P given (A7), Lemmas 1.5, 2.2, 2.4, 2.5; V: Part 3 (eta quotients), Part 2].** Let g ∈ Aut(C) have order m, be fixed-point-free on ℝⁿ, and have N₋(g) even. Identify rSH³(⟨s(g)⟩) ≅ ℤ/m′ via ν_m (s(g) ↦ rotation by 2π/m). Then
- **α/m′ ≡ L·ρ_g (mod 1)**, i.e. α/(2m) ≡ m·ρ_g for m even and α/m ≡ 2m·ρ_g for m odd.

*Proof.*
- The Majorana layer vanishes (Lemma 2.2), so (A7) applies. By Lemma 2.4 any lift may be used.
- Z^{1,1} = Θ_Λ/ηⁿ is invariant under S (Λ unimodular: both Θ_Λ and ηⁿ pick up (−iτ)^{n/2}) and under T^L. Indeed λ²/2 ∈ ½ℤ, L is even, and η(τ+L)ⁿ = e^{2πi·Ln/24}ηⁿ with Ln/24 = Lk/2 ∈ ℤ.
- So e_m(α) is the eigenvalue of S T^L S⁻¹ on 1/η_g (Lemma 2.5).
- Since η(−k/τ) = (−iτ/k)^{1/2} η(τ/k) and Σ_k d_k = 0, we get (1/η_g)|S = Π_k k^{d_k/2} · Π_k η(τ/k)^{−d_k}.
- Each k divides m, which divides L. So T^L multiplies η(τ/k)^{−d_k} by e^{−2πi d_k (L/k)/24}.
- The eigenvalue is exp(−2πi(L/24)Σ_k d_k/k) = exp(2πi L ρ_g)·exp(−2πi Ln/24) = e^{2πiLρ_g}.
- Conclude with Lemma 1.5(d). □
- Note: GJF write the eigenvalue as exp((2πi/24)Σ_k d_k (m/k)(k²−1)). This agrees for m even. For m odd the operator is S T^{2m} S⁻¹ and m must be replaced by 2m (Issue G1).

**Lemma 2.7 (standard lifts) [P given (A8)].** Let g ∈ O(Λ) have odd order m and let ĝ be a lift with ĝ^m = 1. Then η(λ) = 1 for all λ ∈ Λ^g (ĝ is *standard* in the sense of [Lep85]) if either
- (i) ĝ ∈ Λ̂[2].O(Λ), i.e. η is ±1-valued; or
- (ii) ĝ commutes with some lift θ̂ ∈ Λ̂[2].O(Λ) of −1 (GJF's formulation in the proof of Thm 5.6).

In particular GJF's lift s(h) of an order-3 h ∈ Aut(C) is standard, and so is every order-3 element of Λ̂[2].Aut(C) lifting h.

*Proof.*
- For λ ∈ Λ^g, ĝ^m e^λ = η(λ)^m e^λ, so η(λ)^m = 1.
- (i) η(λ) = ±1 and m is odd, so η(λ) = 1.
- (ii) On Λ^g, η is a character: apply ĝ to e^λ_{(−1−⟨λ,μ⟩)} e^μ = ε(λ,μ)e^{λ+μ} and use ε(gλ, gμ) = ε(λ, μ) for λ, μ ∈ Λ^g. Commuting with θ̂ gives η(−λ) = η(λ), while the character property gives η(−λ) = η(λ)⁻¹. So η(λ)² = 1, and with η(λ)^m = 1 (m odd) we get η(λ) = 1. □

**Proposition 2.8 (odd order, standard lift) [P given (A7), Lemmas 1.5, 2.5, 2.7; V: Part 3].** Let Λ be unimodular of rank n = 12k (odd or even), g ∈ O(Λ) of odd order m, and ĝ a standard lift of order m with vanishing Majorana layer.
- Then **α/m ≡ 2m·ρ_g (mod 1)**, with ρ_g = (1/24)Σ_k d_k(k − 1/k) from the Frame shape. The fixed lattice does not contribute.
- For h ∈ Aut(C) of order 3 with cycle shape 3^{n/3} and GJF's lift: ρ_h = n/27 = 4k/9, so **α = 2k ∈ ℤ/3**, and α = 0 iff 3 | k.

*Proof.*
- Z^{1,ĝ} = Θ_{Λ^g}/η_g by Lemma 2.5 with η ≡ 1. Let r = rank Λ^g = Σ_k d_k.
- By Poisson summation [T: e.g. Serre, *Cours d'arithmétique* VII.6], Θ_{Λ^g}(−1/τ) = (−iτ)^{r/2} vol(Λ^g)⁻¹ Θ_{(Λ^g)*}(τ). And (1/η_g)(−1/τ) = (−iτ)^{−r/2} Π_k k^{d_k/2} / Π_k η(τ/k)^{d_k}.
- So Z^{1,ĝ}|S = const · Θ_{(Λ^g)*}(τ) / Π_k η(τ/k)^{d_k}.
- (Λ^g)* = π_g(Λ), the orthogonal projection to 𝔥^g [P]. Λ^g = Λ ∩ 𝔥^g is primitive, so every functional on Λ^g extends to Λ = Λ*, and ⟨λ, ·⟩|_{Λ^g} = ⟨π_gλ, ·⟩|_{Λ^g}.
- For λ ∈ Λ, π_gλ = (1/m)Σ_j g^jλ, so m|π_gλ|² = Σ_{j=0}^{m−1} ⟨λ, g^jλ⟩ ∈ ℤ. Hence T^{2m} multiplies each q^{|μ|²/2}, μ ∈ π_g(Λ), by e^{2πi m|μ|²} = 1.
- The eta part gives e^{2πi·2mρ_g} exactly as in Prop 2.6. The powers of (−iτ) cancel between theta and eta, and Z^{1,1} is invariant under S and T^{2m}.
- So e_m(α) = e^{2πi·2mρ_g}, and Lemma 1.5(d) applies.
- For h: a 3-cycle with σ = 1 has det(1 − hx) = 1 − x³, so the Frame shape is 3^{n/3} and ρ_h = (n/3)(3 − 1/3)/24 = n/27. Then 2mρ_h = 6n/27 = 8k/3, and α ≡ 8k ≡ 2k (mod 3). The Majorana layer vanishes by 2.3(c), and s(h) is standard by Lemma 2.7. □
- [V: Part 3]
  - Exactly: 3|π_hλ|² ∈ ℤ on Λ(C), via the quadratic form Σ_O(Σ_{i∈O} d_i x_i)² ≡ 0 on a basis and on pairwise sums.
  - Numerically: F_h := Θ_{Λ^h}/η(3τ)^{n/3} satisfies F_h(τ/(1−6τ)) = e^{2πi·8k/3} F_h(τ) (error < 10⁻¹⁴). This was checked for:
    - the Golay code with a fixed-point-free order-3 automorphism found by a seeded random search (k = 1, T_h = 0, eigenvalue e^{4πi/3}, anomalous);
    - GJF's k = 3 example (shift by 12);
    - the ℤ/12 seed with h = g⁴ (k = 3);
    - the ℤ/12-chain code of length 72 (k = 6);
    - the Q₈×ℤ₃ seed (k = 6).
  - In the last four cases the eigenvalue is 1.
  - Z^{1,1} drops out, since it is invariant under S T⁶ S.

**Corollary 2.9 (the cyclic anomalies used) [P; V: Part 2].** In every case α = 2k·ν_m in ℤ/m′, so the cyclic anomaly vanishes iff m | k. This is GJF's clause "m divides k" in Thm 5.6.

| element type | phases θ | ρ_g (n = 12k) | m′ | α |
|---|---|---|---|---|
| −1 | ½ | n/16 = 3k/4 | 4 | 2k |
| x with x² = −1 (J, K, JK, the J-chain J) | ¼, ¾ | 3n/64 = 9k/16 | 8 | 2k |
| order 6, g³ = −1, signed 3-cycles | 1/6, 1/2, 5/6 | 19n/432 = 19k/36 | 12 | 2k |
| order 12, g⁶ = −1, signed 6-cycles (the ℤ/12 generator; x·h in Q₈×ℤ₃) | (2j+1)/12 | 73n/1728 = 73k/144 | 24 | 2k |
| h, order 3, shape 3^{n/3}, standard lift | 0, ⅓, ⅔ | n/27 = 4k/9 | 3 | 2k |

- *Uniform proof for the even types.* All cycles have length ℓ = m/2 and σ = −1, so ρ_g = (n/24)(1 + 1/(2ℓ²)) = k/2 + k/m². Then α/(2m) ≡ mk/2 + k/m, i.e. α ≡ m²k + 2k ≡ 2k (mod 2m), since m²k = m·(mk) and mk is even.
- For Q₈ ⊂ Aut(C): res_{⟨x⟩}α = 2k·ν₄ ∈ ℤ/8 for x ∈ {±J, ±K, ±JK}, and res_{⟨−1⟩}α = 2k·ν₂ ∈ ℤ/4.
- Consistency with free fermions: Reg|_{⟨i⟩} has two planes rotated by π/2 and one by π, so α(Fer(Reg)|_{⟨i⟩}) = 1 + 1 + 4 = 6 by the q² rule. Then 3k·6 ≡ 2k (mod 8), and 3k·α(Fer(Reg)|_{⟨−1⟩}) = 3k·2 ≡ 2k (mod 4). This matches [MQ Thm 8.1].
- [V: Part 2]
  - Every element of every group on the actual codes is of one of these types, with α = 2k.
  - For g of order 12: α_g mod 8 = α_{g³} and α_g mod 3 = α_{g⁴}. Restriction ℤ/24 → ℤ/8, ℤ/3 is reduction in the ν-normalisation, since ν₁₂ restricted to ⟨g³⟩ is Fer(2) rotated by 2π/4.
  - The closed forms were checked for k = 1..48.

**Remark 2.10 (what GJF cite, exactly, and what replaces it).**
- "Standard formulas give Z^{1,g} = 1/η_g" (GJF Ex 4.4): this is Lemma 2.5 [P given (A8)].
- The eigenvalue formula (GJF Ex 4.4): Prop 2.6, with the m-odd typo corrected.
- The multiplier principle (GJF §4, before Ex 4.4) is **the one genuinely cited step for cyclic groups**: (A7). Its calibration (Lemma 1.5) and the group orders (Lemma 1.4) are proved here.
- m = 3 (GJF Thm 5.6, proof): "The lift we are using is standard in the sense that it commutes with a choice of lift of −1, and so the Frame shape formula from Example 4.4 applies [Möl16, Chapter 5]". Ex 4.4 also says: "There is always a 'standard' lift [Lep85], for which these phases are trivial. In this case the 't Hooft anomaly is again determined by the Frame shape …; compare [Möl16, Chapter 5]."
  - [Möl16] = S. Möller, *A cyclic orbifold theory for holomorphic vertex operator algebras and applications*, PhD thesis, TU Darmstadt 2016, arXiv:1611.09843. Its lattice chapter concerns **even** lattices, i.e. bosonic lattice VOAs; item numbers were not checked, since the thesis is not in the repository.
  - Λ(C) is odd, so the citation does not literally apply. Lemma 2.7 and Prop 2.8 replace it: a direct proof for any unimodular lattice and odd m, using only (A7) and (A8).

--------------------------------------------------------------------------------------------

## 3. Coprime products: Q₈ × ℤ/3

**Lemma 3.1 (ordinary group cohomology) [T: Brown, *Cohomology of Groups*, III.9–III.10 (cor∘res = [G:H]; H^{q>0}(G;M) is killed by |G|; restriction to a Sylow p-subgroup is injective on the p-primary part), item numbers not checked; V: Part 4].** Let G be finite, M a trivial G-module, q ≥ 1.
- (a) For a Sylow p-subgroup P, res^G_P is injective on H^q(G;M)_{(p)}. It is injective on all of H^q(G;ℤ/2) when p = 2, since [G:P] is odd and acts as 1 on an F₂-vector space.
- (b) β ∈ H^q(G;M) vanishes iff res^G_P β = 0 for every Sylow P.
- (c) For G = Q₈ × ℤ/3:
  - res: H^q(G;ℤ/2) → H^q(Q₈;ℤ/2) and res: H^q(G;ℤ/3) → H^q(ℤ/3;ℤ/3) are isomorphisms;
  - the inverses are the inflations along the projections;
  - H³(G;U(1)) ≅ H³(Q₈;U(1)) ⊕ H³(ℤ/3;U(1)) via the two restrictions (injective by (b), onto via the inflations).

*Proof.*
- (a) cor∘res = [G:P] is invertible on p-primary parts.
- (b) H^q(G;M) is torsion of exponent dividing |G|, so β = Σ_p β_{(p)}. The element res_P(β_{(p′)}) with p′ ≠ p is killed by a power of p′ and by |P|, so it is 0. Hence res_P β = res_P β_{(p)}, and (a) gives β_{(p)} = 0.
- (c) res is injective by (a) and surjective because res∘infl = (pr∘incl)* = id. In the last statement the map is injective by (b), and surjective because res_{Q₈}∘infl_{ℤ/3} and res_{ℤ/3}∘infl_{Q₈} factor through the trivial group.
- [V: Part 4] Over F₂: dim H¹ = dim H² = 2 for both Q₈ and Q₈×ℤ/3, and the inflated classes x², y² stay independent. Over F₃: dim H¹ = dim H² = 1 for Q₈×ℤ/3 with the inflated Bockstein class nonzero, and dim H¹ = dim H² = 0 for Q₈. □

**Proposition 3.2 (Sylow detection for anomalies) [P given (A2), (A5), Lemma 3.1].** Let G be finite and α ∈ S̃H³(G). Then α = 0 iff res^G_P α = 0 for every Sylow subgroup P.

*Proof.* Suppose all Sylow restrictions vanish. Let P₂ be a Sylow 2-subgroup.
1. *Majorana layer.* By naturality, res_{P₂} maj(α) = maj(res_{P₂}α) = 0. By Lemma 3.1(a) for ℤ/2, maj(α) = 0.
   - By exactness (A5), α = ι₂(α′) for a unique α′ ∈ rSH³(G) (ι₂ is injective).
   - For every P, ι₂ res_P α′ = res_P α = 0, so res_P α′ = 0 (ι₂ is injective for P).
2. *Gu–Wen layer.* res_{P₂} gw(α′) = gw(res_{P₂}α′) = 0, so gw(α′) = 0. Then α′ = ι₁(β) for a unique β ∈ H³(G;U(1)), and as before res_P β = 0 for every P (ι₁ is injective).
3. *Ordinary layer.* β = 0 by Lemma 3.1(b), so α = 0. □
- Only naturality of maj, gw, ι₁, ι₂, their injectivity in degree 3, and exactness at S̃H³ and rSH³ are used. No Künneth formula and no spin bordism.

**Corollary 3.3 (G = Q₈ × ℤ/3) [P; V: Part 4].**
- The Sylow subgroups are Q₈ × 1 and 1 × ℤ/3, each unique since normal. So **α = 0 iff α|_{Q₈} = 0 and α|_{ℤ/3} = 0.**
- More precisely, (res_{Q₈}, res_{ℤ/3}): S̃H³(Q₈ × ℤ/3) → S̃H³(Q₈) ⊕ S̃H³(ℤ/3) is an isomorphism.
  - It is injective by 3.2.
  - It is surjective: infl_{Q₈} ⊕ infl_{ℤ/3} is a right inverse, because res_{Q₈}∘infl_{ℤ/3} factors through the trivial group, whose reduced S̃H³ is 0.
  - So there are no "mixed terms". This is the coprimality statement used in [MQ §8, §10].

**Remark 3.4 (spin-bordism form).**
- [T, reference to be checked: GJF17 §5.4] S̃H is the (−2)-connective cover τ_{≥−2} I_{ℂ^×}MSpin of the Pontryagin dual of spin bordism.
- Since Ω₃^Spin(pt) = 0, and π_{≤−4} enters only in degrees ≥ 4, we get S̃H³(G) ≅ Hom(Ω̃₃^Spin(BG), U(1)) [P given T].
- Corollary 3.3 then says Ω̃₃^Spin(B(Q₈ × ℤ/3)) ≅ Ω̃₃^Spin(BQ₈) ⊕ Ω̃₃^Spin(Bℤ/3). Alternative proof: B(Q₈×ℤ/3) → BQ₈ is a ℤ₍₂₎-homology equivalence, and → Bℤ/3 a ℤ₍₃₎-homology equivalence; compare the Atiyah–Hirzebruch spectral sequences after localisation.
- Not needed above.

**Corollary 3.5 (the anomaly of [MQ Thm 10.1] vanishes) [P given Thm 4.1, Prop 2.8, Cor 3.3].**
- Setting: C self-dual of length n = 12k, and G = Q₈ × ⟨h⟩ ⊂ Aut(C) as in [MQ Thm 10.1]: J² = K² = −1, KJ = −JK, h of order 3 with cycle shape 3^{n/3} commuting with J and K, acting by GJF's lift.
- Claim: if 24 | k, then α_G = 0.
- *Proof.* α_G|_{Q₈} = α_{Q₈} = 0 by Thm 4.1 (8 | k), and α_G|_{⟨h⟩} = 2k·ν₃ = 0 by Prop 2.8 (3 | k). Conclude by Cor 3.3. □
- [V: Part 2] On `q8z3_chain_len288` (k = 24) and `q8z3_chain_len144` (k = 12) every cyclic subgroup is non-anomalous. At k = 12, α_G|_{Q₈} = κ ≠ 0 (Thm 4.1) is invisible cyclically; this is why [MQ Thm 10.1] uses only k ≡ 0 mod 24.

--------------------------------------------------------------------------------------------

## 4. The Q₈ anomaly, consolidated ([MQ §8.4–8.5])

**Theorem 4.1 [P given Table 4.8; this is MQ Thm 8.1 in the form the Main Question uses].** Let C be self-dual of length n = 12k and Q₈ = ⟨J, K⟩ ⊂ Aut(C) with J² = K² = −1 and **KJ = −JK**, acting on V = V_{Λ(C)} by GJF's lift. Then the Q₈-action is non-anomalous **iff 8 | k**. More precisely:
- α_C ∈ rSH³(Q₈);
- if 4 ∤ k, then res_{⟨J⟩} α_C = 2k·ν₄ ≠ 0;
- if 4 | k, then α_C = (k/4 mod 2)·κ, where κ is the unique nonzero element of rSH³(Q₈) with all cyclic restrictions zero (Prop 4.3).

(The relation KJ = −JK must be part of the hypothesis: J² = K² = −1 alone does not force ⟨J, K⟩ ≅ Q₈.)

**Lemma 4.2 (cohomology of Q₈) [T: Cartan–Eilenberg Ch. XII §7 (periodic resolution of generalized quaternion groups); Adem–Milgram, *Cohomology of Finite Groups*, Ch. IV (H*(Q₈;F₂)); Brown VI.9 (periodic cohomology, free actions on spheres); item numbers not checked; V: Part 4 for (a), (b)].**
- (a) H¹(Q₈;ℤ/2) = ⟨x, y⟩ with x = w₁(χ_i) and y = w₁(χ_j), so x + y = w₁(χ_k). Here χ_u is the character with kernel ⟨u⟩.
  - H²(Q₈;ℤ/2) = {0, x², y², xy}, with x² + xy + y² = 0.
- (b) For u ∈ {i, j, k}, the restriction H²(Q₈;ℤ/2) → H²(⟨u⟩;ℤ/2) ≅ ℤ/2 is zero. Reason: H*(ℤ/4;F₂) = Λ[u₁] ⊗ F₂[v₂] with u₁² = 0.
- (c) H³(Q₈;U(1)) ≅ H⁴(Q₈;ℤ) ≅ ℤ/8, generated by e = c₂(ρ₂), the second Chern class of the 2-dim irrep ρ₂: Q₈ ⊂ SU(2). Also H^{odd}(Q₈;ℤ) = 0.
  - res to each ⟨u⟩ ≅ ℤ/4 is onto H⁴(ℤ/4;ℤ) ≅ ℤ/4: it sends c₂(ρ₂) to c₂(ζ ⊕ ζ⁻¹) = −c₁(ζ)², the Euler class of ⟨u⟩ ⊂ SU(2) acting freely on S³, a generator.
  - So ker(res_{⟨u⟩}) = {0, 4e}.
- (d) Every automorphism σ of Q₈ fixes H⁴(Q₈;ℤ) pointwise, since ρ₂∘σ ≅ ρ₂ (the unique 2-dim irrep).
  - Taking σ: i ↦ j ↦ k ↦ i and using (A2), the restrictions of any β ∈ H³(Q₈;U(1)) to ⟨i⟩, ⟨j⟩, ⟨k⟩ are *equal* elements of ℤ/4 under the identifications u ↦ 1.

**Proposition 4.3 (the cyclic kernel, without eta invariants) [P given (A2), (A5), (A6), Lemmas 1.4, 1.5, 4.2; V: Part 4].** Let R = (res_{⟨i⟩}, res_{⟨j⟩}, res_{⟨k⟩}): rSH³(Q₈) → (ℤ/8)³, each factor in its ν₄-normalisation, and K := ker R. Then **K = {0, κ}** with κ := ι₁(4e) ≠ 0.

*Proof.*
1. |rSH³(Q₈)| = 32 (Lemma 1.4(c)).
2. *Bosonic classes.* For each u, ι₁H³(⟨u⟩;U(1)) ⊂ rSH³(⟨u⟩) ≅ ℤ/8 is the subgroup of order 4, namely 2ℤ/8 (ι₁ is injective and \|H³(ℤ/4;U(1))\| = 4). res_{⟨u⟩}(ι₁e) = ι₁(res_{⟨u⟩}e) generates it (Lemma 4.2(c)), and is the same element for u = i, j, k (Lemma 4.2(d)). So R(ι₁e) = (2a, 2a, 2a) for one odd a.
3. *Free-fermion classes.* Let b_χ := α(Fer(2χ)), where Q₈ acts on two Majoranas through χ ∈ {χ_i, χ_j, χ_k}, i.e. by rotation through π where χ = −1.
   - Since 2χ lands in SO(2), maj(b_χ) = w₁(2χ) = 0 (A6), so b_χ ∈ rSH³(Q₈).
   - On ⟨u⟩ with χ(u) = 1 the action is trivial, so the restriction is 0.
   - If χ(u) = −1, u rotates through 2π·2/4, and the restriction is 2²ν₄ = 4ν₄ (Lemma 1.5(c)).
   - So R(b_{χ_i}) = (0, 4, 4), R(b_{χ_j}) = (4, 0, 4), R(b_{χ_k}) = (4, 4, 0).
4. For odd a, the subgroup of (ℤ/8)³ generated by (2a,2a,2a), (0,4,4), (4,0,4) has order 16. [V: Part 4, all four a; by hand in (2ℤ/8)³ ≅ (ℤ/4)³: ⟨(1,1,1)⟩ has order 4; (0,2,2) is not in it; and (2,0,2) is not of the form (t, t+2s, t+2s).] So |im R| ≥ 16 and |K| ≤ 32/16 = 2.
5. κ = ι₁(4e) is nonzero, since ι₁ is injective and 4e ≠ 0. Also R(κ) = 4R(ι₁e) = (8a, 8a, 8a) = 0. So K = {0, κ}. □
- This proves "step 1" of [MQ §8.4] without eta invariants, without the free-fermion count of 32 values, and without Gu–Wen layers.
- Cross-checks with [MQ §8]: κ = 4·A(H) = A(Fer(4H)), since A(H) = ±ι₁(e) by [MQ Thm 8.1 Step 3]; κ takes the value ½ on S³/Q₈ [V: `mainq_q8_nonanomaly.py` Part 1]; im R has order exactly 16.

**Lemma 4.4 (layers and cyclic restrictions of α_C) [P given Cor 2.3′, Cor 2.9].**
- maj(α_C) = 0 (N₋(J) = N₋(K) = 6k is even).
- res_{⟨x⟩}α_C = 2k·ν₄ for x ∈ {±J, ±K, ±JK}. This uses (JK)² = J(KJ)K = −J²K² = −1, so JK is also of type x² = −1.
- res_{⟨−1⟩}α_C = 2k·ν₂.
- Hence α_C ≠ 0 if 4 ∤ k, and α_C ∈ K = {0, κ} if 4 | k.

**Lemma 4.5 (the (−1)-twisted sector) [P given (A10), GJF Thm 3.1; V: Part 5 and `mainq_q8_twisted.py` Part 1].** Let θ̂ = s(−1).
- (a) [(A10); MQ Lemma 8.3] The unique irreducible θ̂-twisted V-module is V(−1) = S[θ] ⊗ T.
  - S[θ] is the Fock space of the modes α(r), r ∈ ½ + ℤ.
  - T is the spinor module of Cl(n) = ⟨γ₁, …, γ_n⟩, of dimension 2^{n/2} and ordinary type since n is even, with all of T at weight n/16.
  - V(−1) is irreducible already for the frame F.
  - ch V(−1) = E(τ) := 2^{n/2} q^{n/48} Π_{j odd}(1 − q^{j/2})^{−n}.
- (b) [P, Schur] For g ∈ Q₈, every operator on V(−1) implementing s(g) (so in particular implementing g on F) is a scalar multiple of Fock(g) ⊗ φ_g. Here φ_g ∈ Pin(n) satisfies φ_g γ_i φ_g⁻¹ = s_i γ_{p(i)}.
- (c) [P] There is a genuine linearisation ρ̃: Q₈ → GL(T), ρ̃(g) ∈ ℂ^× φ_g, with T ≅ ⊗_O (ρ₂ ⊕ 2·1) over the 3k orbits O. Hence
  - **t_x := Tr_T ρ̃(x) = 2^{3k}** for x ∈ {±J, ±K, ±JK};
  - Tr_T ρ̃(−1) = 0;
  - all genuine linearisations are ψ ⊗ ρ̃ with ψ ∈ Hom(Q₈, ±1).
  
  *Proof of (c).*
  - Cl(n) = ⊗̂_O Cl(4)_O. On an orbit, Q₈ acts on ℝ⁴_O by signed permutations of determinant 1 (double transpositions with two minus signs).
  - In Morita coordinates [MQ Lemma 9.1] this is left multiplication on ℍ, i.e. SU(2)_L ⊂ SO(4) = (SU(2)_L × SU(2)_R)/±1 (or SU(2)_R, if the monomial coordinate change reverses orientation).
  - SU(2)_L lifts isomorphically to SU(2)_L × 1 ⊂ Spin(4). The half-spin modules are S⁺ = ℂ² for SU(2)_L and S⁻ = ℂ² for SU(2)_R, so q ↦ (q, 1) gives S₄|_{Q₈} ≅ ρ₂ ⊕ 2·1.
  - Even Clifford elements act factorwise on T = ⊗_O S₄(O), with no Koszul signs. So the tensor product of these lifts is a genuine representation ρ̃.
  - Traces: χ_{ρ₂}(x) = 0 for x of order 4 and χ_{ρ₂}(−1) = −2. So t_x = Π_O(0 + 2) = 2^{3k} and Tr ρ̃(−1) = Π_O(−2 + 2) = 0.
  - Two genuine representations that agree pointwise up to scalars differ by a homomorphism Q₈ → ℂ^×, which is ±1-valued. □
  
  [V: Part 5] On one orbit (J, K from `mainq_morita.q8_gens(1)`):
  - the Pin lifts are computed in Cl(4);
  - there are exactly four linearisations, each ρ₂ ⊕ 2ψ, with ψ running over the four characters;
  - ρ̃(−1) = ±Γ, the chirality.
- (d) [(A10)] For x of order 4, V(x) = S[x] ⊗ T_x.
  - T_x is the spinor module of Cl(n/2): one zero mode per signed 2-cycle. It has dimension 2^{n/4}, superdimension 0, and ordinary type since n/2 is even.
  - The weights lie in h_x + ¼ℤ with h_x = 3n/64.
  - ch V(x) = g(τ) := 2^{n/4} q^{n/192} Π_{j odd}(1 − q^{j/4})^{−n/2}.
- The Fock trace of x on S[θ] is F(τ) := q^{n/48} Π_{r odd}(1 + q^r)^{−n/2}.

**Lemma 4.6 (eta identities; MQ Lemma 8.5.1) [P given η(−1/τ) = √(−iτ)η(τ), η(τ+1) = e^{2πi/24}η(τ), and Euler's identity Π(1 − (−q)^m) = Π(1−q^{2m})³/(Π(1−q^m)Π(1−q^{4m})); V: Part 6 and `mainq_q8_orbifold_character.py`].** Let e := ηⁿ(τ)/ηⁿ(2τ) = Z(1,−1) and f := η(2τ)^{n/2}/η(4τ)^{n/2} = Z(1,x) (Lemma 2.5). Then:
- (i) e|S = E;
- (ii) f|S = g;
- (iii) f|ST²S = N·F with **N = (√2·e^{2πi/48})^{n/2} = 2^{3k} e^{2πik/8}**.

*Proof.*
- (i) and (ii): direct substitution. For example, f(−1/τ) = 2^{n/4}(η(τ/2)/η(τ/4))^{n/2} = g(τ).
- (iii): f|ST²S(τ) = f(τ′) with τ′ = τ/(1 − 2τ).
  - 2τ′ = γ₁(2τ) with γ₁ = (−1 0; 1 −1), and 4τ′ = γ₂(τ − ½) with γ₂ = (−2 −1; 1 0).
  - Both eta multipliers equal e^{−πi/6} (Dedekind sums, [V]), so they cancel. The square roots give √(−i(2τ−1))/√(−i(τ−½)) = √2.
  - Euler gives η(τ − ½) = e^{−2πi/48} η(2τ)³/(η(τ)η(4τ)).
  - Hence η(2τ′)/η(4τ′) = √2 e^{2πi/48} η(τ)η(4τ)/η(2τ)². Finally (η(τ)η(4τ)/η(2τ)²)^{n/2} = q^{n/48}Π_{r odd}(1+q^r)^{−n/2} = F. □

**Proposition 4.7 (non-anomalous and 4 | k forces 8 | k; MQ Prop 8.5.2) [P given (A1), (A9)–(A11), Lemmas 2.5, 4.5, 4.6; V: Part 6].** If 4 | k and the Q₈-action on V_{Λ(C)} is non-anomalous, then 8 | k.

Additional cited inputs (used only here):
- **(A9)** [T: Dong–Zhao, CMP 260 (2005) 227; van Ekeren, CMP 322 (2013) 333; item numbers not checked]. The NS character of a C₂-cofinite holomorphic SVOA W satisfies ch W|S = λ·ch W for a constant λ.
  - [P] λ = 1: S fixes τ = i, and ch W(i) = Σ_h dim W_h e^{−2π(h − c/24)} > 0.
- **(A10)** [T: Lepowsky 1985; FLM Ch. 9; Dong–Lepowsky, JPAA 110 (1996); Bakalov–Kac, arXiv:math/0402315]. Twisted modules of lattice (S)VOAs: existence, uniqueness (for holomorphic V), and the explicit form used in Lemma 4.5(a),(d).
  - Also the twisted-module axiom: e^{2πiL₀}P on a g-twisted module implements g^{±1} (the monodromy).
- **(A11)** [T: GJF Thm 4.2 and its proof (Kirillov 2002; Dijkgraaf–Vafa–Verlinde–Verlinde, CMP 123 (1989) 485)]. A trivialisation of α gives W = V//G = ⊕_{[g]} V(g)^{C(g)}, where V(g) is the unique irreducible g-twisted module. After regauging parities, C(g) acts on V(g) by a genuine representation ρ_g through even operators implementing C(g) (ρ_g(h)Y(v,z)ρ_g(h)⁻¹ = Y(hv,z)), with ρ₁ the given action.
  - The remaining choices of trivialisation are H¹(Q₈;ℤ/2), since H²(Q₈;U(1)) = 0. They flip the parity of V(g) for g with ψ′(g) = 1; this never affects V(−1), because −1 is a commutator.

*Proof.* Suppose α_C = 0 and let W = V//Q₈ (A1). The classes of Q₈ are {1}, {−1}, {±J}, {±K}, {±JK}, with C(±1) = Q₈ and C(x) = ⟨x⟩.
1. *Untwisted sector.* It contributes (1/8)Σ_{h∈Q₈} Z(1,h) = (1/8)(Z(1,1) + e + 6f), by Lemma 2.5 (all h ≠ 1 are fixed-point-free).
2. *(−1)-sector.*
   - By Lemma 4.5(b) and genuineness, ρ_{−1}(h) = ψ(h)·(Fock(h) ⊗ ρ̃(h)) for a character ψ.
   - Traces: E for h = 1; (Fock trace)·Tr ρ̃(−1) = 0 for h = −1; ψ(x)·2^{3k}·F for h = ±x, using ψ(−x) = ψ(x) and t_{−x} = t_x (same computation).
   - Contribution: E/8 + (1/4)T_ψ F, with **T_ψ := 2^{3k}(ψ(J) + ψ(K) + ψ(JK))**.
3. *x-sectors.*
   - V(x) is irreducible with End = ℂ, and e^{2πiL₀}P implements x^{±1} (A10). So by Schur ρ_x(x) = ε·e^{2πiL₀}P for a scalar ε.
   - *W_x := V(x)^{⟨x⟩} ≠ 0.* On the weight space of weight h_x + j/4, which is (Fock level j/4) ⊗ T_x:
     - the odd powers ρ_x(x^{±1}) have trace ∝ sdim T_x = 0;
     - ρ_x(x²) = ε²e^{4πiL₀} is the scalar ε²e^{4πih_x}(−1)^j there;
     - so the projector (1/4)Σ_j ρ_x(x^j) has trace (1/4)(1 + ε²e^{4πih_x}(−1)^j)·dim.
     - This is nonzero for j = 0 or for j = 1, and both levels are nonzero (the modes lie in ±¼ + ℤ).
   - W is an SVOA, so e^{2πiL₀} = ±P on W_x (the sign is the parity convention for this sector). On W_x, ρ_x(x) = 1, hence ε = ±1.
   - Then ρ_x(x²) = e^{4πiL₀}, whose trace (with q^{L₀−n/24}) is e^{4πi·n/24}·g(τ+2) = g(τ+2), since n/24 = k/2.
   - The sector contributes (1/4)(g(τ) + g(τ+2)).
   - (This avoids the notes' use of ε⁴ = 1, which needs 4h_x ∈ ℤ; see Issue N4.)
4. *Character.* ch W = Z(1,1)/8 + e/8 + (6/8)f + E/8 + (1/4)T_ψF + (3/4)(g + g(τ+2)).
5. *S-invariance.*
   - By (A9), ch W|S = ch W. Z(1,1) is S-invariant (Λ is unimodular), e ↔ E and f ↔ g (Lemma 4.6(i),(ii); S² = 1).
   - By (iii), g|T²S = N·F, and F|S = g|T²/N.
   - So ch W|S − ch W = **¼(3N − T_ψ)(F − g(τ+2)/N)**.
   - F − g(τ+2)/N ≠ 0: the leading exponents n/48 and n/192 differ.
   - Hence T_ψ = 3N, i.e. ψ(J) + ψ(K) + ψ(JK) = 3e^{2πik/8}. The left side is 3 (ψ = 1) or −1 (ψ ≠ 1), so its modulus forces ψ = 1 and e^{2πik/8} = 1, i.e. 8 | k. □
- [V: Part 6]
  - Z(1,1) = Θ_{ℤⁿ}/ηⁿ is S-invariant to 10⁻¹⁴ (tetracode sums have Λ ≅ ℤⁿ).
  - For k = 4, 8 and all four ψ, ch W(−1/τ) − ch W(τ) equals ¼(3N − T_ψ)(F − g(τ+2)/N) to rounding.
  - It vanishes only for (k = 8, ψ = 1); otherwise it is ≥ 750× the rounding level.
  - f(τ/(1−2τ)) = N·F(τ) at n = 12 to 10⁻¹⁵.

**Proof of Theorem 4.1.**
- (i) maj(α_C) = 0 (Lemma 4.4).
- (ii) 4 ∤ k: res_{⟨J⟩}α_C = 2kν₄ ≠ 0, so the action is anomalous.
- (iii) k ≡ 4 mod 8: α_C ∈ {0, κ} (Lemma 4.4, Prop 4.3), and α_C = 0 would give 8 | k by Prop 4.7. So α_C = κ.
- (iv) 8 | k:
  - Let D be the tetracode sum of length 48 (k_D = 4) with Q₈ in Morita form, D = F₃² ⊗ ⊕_b ⟨e_{2b}⟩.
  - Q₈ acts diagonally on C ⊕ D (the relations persist). GJF's lift for C ⊕ D is s_C ⊗ s_D (Def. 1.2), so α_{C⊕D} = α_C + α_D by (A4).
  - k + 4 ≡ 4 and k_D = 4 ≡ 4 (mod 8), so (iii) gives α_{C⊕D} = κ = α_D. Hence α_C = 0. □
- [V: Part 1–2] D48 and D96 are self-dual and Q₈-invariant, with Majorana layer 0 and all cyclic anomalies 0.

**Table 4.8 (inputs of Theorem 4.1 and Corollary 3.5, with status).**

| input | used in | status | reference |
|---|---|---|---|
| GJF's lift s; unique given its frame action; s_{C⊕D} = s_C ⊗ s_D | everywhere; 4.1(iv) | [T] + [P] | GJF Thm 3.1 and its proof |
| (A1) anomaly in S̃H³; orbifold iff α = 0; V^G regular | 4.7 | [T] | GJF Thm 4.2; Kirillov 2002; Carnahan–Miyamoto 2016 |
| (A2) restriction, transport | 2.2, 3.2, 4.2(d), 4.3 | [T] | GJF §4 (construction) |
| (A3) conjugation invariance | 2.4 | [T] | transport of structure |
| (A4) additivity under ⊗ | 4.1(iv) | [T] | GJF17 §5 |
| (A5) layer exact sequences, injectivity in degree 3 | 1.4, 3.2, 4.3 | [T] | GJF §4; Wang–Gu 2017; GJF17 §5.4 |
| (A6) Majorana layer = parity on V_R; = w₁ for free fermions | 2.2, 4.3 | [T] (+ [P] for w₁) | GJF §4 (via BGK16) |
| (A7) multiplier principle for cyclic groups | 1.5, 2.6, 2.8, 4.3 step 3 | [T] **stated without proof in GJF** | GJF §4 before Ex 4.4; GPRV13 §3; bosonic: vEMS 2020 |
| (A8) lifts of lattice automorphisms | 2.2, 2.4, 2.5, 2.7 | [T] | Lep85; FLM; Dong–Nagatomo 1999 |
| (A9) S-invariance of holomorphic SVOA NS characters | 4.7 | [T] + [P] (λ = 1) | Dong–Zhao 2005; van Ekeren 2013 |
| (A10) lattice twisted modules, twisted-module monodromy | 4.5, 4.7 | [T] | Lep85; FLM Ch. 9; Dong–Lepowsky 1996; Bakalov–Kac 2004 |
| (A11) W = ⊕ V(g)^{C(g)}, genuine even C(g)-actions after regauging | 4.7 | [T] | GJF Thm 4.2 proof; Kirillov 2002; DVVV 1989 |
| group cohomology of ℤ/m, Q₈, Q₈ × ℤ/3 | 1.4, 3.1, 4.2 | [T; V: Part 4] | Brown III, VI.9; Cartan–Eilenberg XII.7; Adem–Milgram IV |
| Poisson summation, η transformations, Euler identity | 1.5, 2.6, 2.8, 4.6 | [T] classical | e.g. Serre, *Cours d'arithmétique* VII |
| Majorana layer and cyclic anomalies of all elements used | 2.3′, 2.9, 4.4 | [P; V: Parts 1–2] | this file |
| cyclic kernel {0, κ} | 4.3 | [P; V: Part 4] | this file |
| Spin(4) traces t_x = 2^{3k} | 4.5 | [P; V: Part 5] | this file |
| eta identities (i)–(iii) | 4.6 | [P; V: Part 6] | this file; MQ Lemma 8.5.1 |
| Q₈-invariant tetracode sum D48 | 4.1(iv) | [P; V: Parts 1–2] | MQ Lemma 9.1 |

**Remark 4.9 (what the Main Question does *not* need).**
- The coprime-gauging lemma ([MQ §8.2 Lemma E]) and Step 1 of [MQ Thm 8.1].
- The eta invariants of S³/Q₈ ([MQ Thm 8.1 Step 4]). They were used in [MQ §8.4 step 1] "only to count classes", which Prop 4.3 replaces.
- The invariant μ of [MQ §8.3]. Prop 4.7 is the logical input and μ is a consistency check.
- The formula α_C = 3k·a ([MQ §8.4 step 5]). It is needed only for "a has order 8", not for Thm 4.1.

--------------------------------------------------------------------------------------------

## 5. Formalization notes and size estimate (anomaly side)

**Strategy.** Declare the VOA-level facts as an interface (a Lean `structure` or `axiom`s) and prove everything else. The interface has roughly 15–20 fields:
- an opaque anomaly map `anom : (G-action on a holomorphic SVOA) → S̃H³ G`, with (A1)–(A4);
- `S̃H³` as an abstract functor with layer maps satisfying (A5);
- (A6) for Ramond parity;
- (A7) as the statement "the S T^L S⁻¹-eigenvalue is a homomorphic invariant";
- (A8), (A9)–(A11) phrased as equalities of explicit q-series (characters) and Schur-type uniqueness.
Existing files calibrate the scale: `Existence.lean` (805 lines) and `Divisibility.lean` (662 lines).

| block | content | estimate (lines) | notes |
|---|---|---|---|
| signed permutations | Mon(n), N₋, sign character, signed cycles, Lemma 2.3 | 300–500 | Mathlib `Equiv.Perm.cycleType` helps; signed cycles need their own API |
| Frame shapes, ρ_g | cycle-type → ρ_g ∈ ℚ, Cor 2.9 table, α ≡ 2k | 150–300 | rational arithmetic, `norm_num`/`decide` |
| eta/theta analysis | η S and T laws, Poisson for lattice thetas, Euler identity, Lemma 1.5(a), Prop 2.6, 2.8, Lemma 4.6 | 600–1200 if Mathlib's η S-transformation is available; +1500–3000 otherwise | Mathlib has `jacobiTheta` with its S-law; multi-variable Poisson for Θ_{Λ^g} may need work |
| lattice lifts | Lemmas 2.4, 2.5, 2.7 from (A8) | 200–400 | 2.4 needs divisibility of U(1) (injective ℤ-module) |
| supercohomology interface | (A5) as a structure; Lemma 1.4, Prop 3.2, Cor 3.3, Prop 4.3 | 400–800 | pure diagram chases and finite abelian groups |
| group cohomology inputs | H^{≤2}(Q₈;F₂), H^{≤2}(ℤ/4;F₂), Q₈×ℤ/3 restrictions; cor∘res = index; H⁴(Q₈;ℤ) = ℤ/8 and restrictions | 300–600 with certificates + axioms for H⁴ and transfer; 1500–3000 to prove transfer and the periodic resolution | Mathlib's `groupCohomology` covers low degrees; transfer on cohomology is not in Mathlib (to my knowledge) |
| Clifford / Spin(4) | Lemma 4.5(c): explicit 4×4 matrices over ℚ(i), Kronecker products, trace multiplicativity | 250–500 | `Matrix.trace_kronecker` exists |
| character argument | Prop 4.7 given (A9)–(A11): q-series bookkeeping, leading-exponent comparison | 400–800 | holomorphic functions on ℍ with q-expansions |
| assembly | Thm 4.1, Cor 3.5, cyclic theorem for the chains | 200–400 | |

- **Total, VOA inputs axiomatized: ≈ 2,800–5,500 lines** (≈ 15–20 axioms). Add ≈ 3,000–6,000 if the η/θ transformation laws and group-cohomology transfer must be built first. [H: order-of-magnitude, calibrated only against the two existing files.]
- **Without the axioms** (lattice SVOAs and their twisted modules, Zhu/DLM/van Ekeren modular invariance, Carnahan–Miyamoto regularity, Kirillov–Müger orbifold theory, super fusion categories and extended supercohomology as a cohomology theory) the anomaly side is far beyond current Mathlib. It would plausibly take 10⁵ lines or more and years of work [H].
- **Lean pitfalls anticipated.**
  - The hypothesis must include KJ = −JK (Theorem 4.1).
  - The ν-normalisations of rSH³(⟨u⟩) ≅ ℤ/8 must be transported along the chosen generator, or Lemma 4.2(d) becomes false by a unit.
  - Keep "fixed-point-free on ℝⁿ" (σ = −1 on every cycle) separate from "no fixed coordinate" (order-3 h has fixed vectors but no fixed coordinates).

--------------------------------------------------------------------------------------------

## 6. Issues found

*Status (2026-09-27): the items below are tracked, with what has been fixed since, in `README.md` §5.*

None of these invalidates a result of [MQ], [OI] or GJF. Items O1 and N1–N6 concern the existing notes; G1–G3 concern GJF's paper.

- **O1 ([OI] §3.2, imprecise; harmless).** "The lift of h is unique: an element of order 3 in Λ̂[2].Aut(C) has a unique lift of order 3, since Λ̂[2] is a 2-group."
  - This is false as stated. In Λ̂[2].⟨h⟩ ≅ 2ⁿ.3 the order-3 lifts of h generate Sylow 3-subgroups, so they are unique only **up to conjugation by Λ̂[2]**.
  - Example: for h a product of n/3 disjoint 3-cycles, t·h has order 3 iff t_a t_b t_c = 1 on each cycle, giving 4^{n/3} lifts.
  - It is harmless for three reasons:
    - GJF's lift s(h) is one specific, canonical element (Def. 1.2);
    - every order-3 lift in Λ̂[2].Aut(C) is standard (Lemma 2.7), and they are conjugate, so they have the same anomaly;
    - whatever normalisation the orbifold induces on V_R is a scalar multiple of the sign-valued one (Schur). That scalar multiplies Z_RR(1,h) = ±T_h, so vanishing for T_h = 0 is unaffected.
  - The sentence "acts on a fixed ground state by a cube root of unity that is also a sign, i.e. by 1" presupposes the sign-valued normalisation.
- **N1 ([MQ] §8.4 step 1, gap in the by-hand remark).** "A class with nonzero Gu–Wen layer is b_χ + h, …"
  - This needs two unstated facts:
    - the Gu–Wen layers of b_{χ_i}, b_{χ_j}, b_{χ_k} are the three nonzero classes of H²(Q₈;ℤ/2). This is true: w₂(2χ) = w₁(χ)², and x², y², xy are distinct and nonzero (Lemma 4.2(a), [V: Part 4]);
    - "h restricts to the same element on all three ℤ₄'s" needs Aut(Q₈)-invariance of H⁴(Q₈;ℤ) (Lemma 4.2(d)).
  - Prop 4.3 gives a shorter proof that needs neither Gu–Wen layers nor eta invariants. With it, the input "[T] the anomaly of free fermions on S³/Q₈ is given by eta invariants … used only to count classes" can be dropped from §8.4.
- **N2 ([MQ] §8.4 Inputs and step 3, dependency list).** Step 3 uses μ = −1 (§8.3) together with "non-anomalous ⇒ μ = 1" (Prop 8.5.2). But Prop 8.5.2 already proves "non-anomalous and 4 | k ⇒ 8 | k" directly. So μ is a consistency check, not a logical input, and §8.4 step 3 can cite Prop 8.5.2 alone (as Thm 4.1(iii) does here).
- **N3 ([MQ] §8, notation).** κ denotes two different classes:
  - in Thm 8.1 Step 3, the level-1 SU(2)_L anomaly (pulled back: A(H));
  - in §8.4, A(Fer(4H)) = 4a of order 2.
  They are related by κ_{§8.4} = 4·ρ_H*κ_{Step 3}. Renaming one would avoid confusion.
- **N4 ([MQ] Prop 8.5.2 step 3, two unstated steps; conclusion correct).**
  - "ε⁴ = 1 because ρ_x(x)⁴ = 1 and the weights lie in h_x + ¼ℤ" silently uses 4h_x = 9k/4 ∈ ℤ (true for 4 | k).
  - "ε = ±1 because W is an SVOA" needs W_x ≠ 0, which is not argued.
  - Prop 4.7 step 3 supplies W_x ≠ 0 and avoids ε⁴ = 1.
- **N5 ([MQ] §8 preamble, citation to check).** The identification "extended supercohomology is a connective cover of the Pontryagin dual of spin bordism" is attributed to [JF §2.4] (*The moonshine anomaly*). GJF attribute extended supercohomology to Wang–Gu and GJF17 §5.4. [JF §2.4] could not be checked here. The precise statement needed is Remark 3.4, and no proof in this file depends on it.
- **N6 ([OI] §4 table, dangling reference).** It refers to `notes/lean-blueprint.md`, which does not exist in the repository (it may be planned).
- **G1 (GJF Ex 4.4, typo).** For m odd the operator is S T^{2m} S⁻¹, and its eigenvalue on Z^{1,g}/Z^{1,1} is exp((2πi/24)Σ_k d_k (2m/k)(k²−1)), not the displayed exp((2πi/24)Σ_k d_k (m/k)(k²−1)).
  - "α '=' Σ d_k (m/k)(k²−1) mod 24" holds only in the normalised sense of Prop 2.6 (α/m′ ≡ Lρ_g).
  - GJF's conclusion for m = 3 is right (Prop 2.8).
- **G2 (GJF Thm 5.6 proof, typo).** Each block contributes 6 × (number of sign changes in the block) to ⟨χ,(1−g)χ⟩ (Lemma 2.2(a)), not "3(m/2) − 2×odd". For example, g = −1 gives 6 per block, not 1. The conclusion ⟨χ,(1−g)χ⟩ ∈ 4ℤ is right: the total is 6N₋, and N₋ is a sum of 24k/m odd numbers with 24k/m even.
- **G3 (GJF Thm 5.6 proof, citation gap; closed here).** The m = 3 step cites [Möl16, Ch. 5], whose lattice results concern even lattices; Λ(C) is odd. Lemma 2.7 and Prop 2.8 prove what is needed for any unimodular lattice and odd m, given (A7).
  - GJF's criterion "commutes with a lift of −1" does imply standardness (Lemma 2.7(ii)).
  - The simpler criterion "order-3 element of Λ̂[2].Aut(C)" suffices (Lemma 2.7(i)).
