# Ternary-code SCFTs: 24 | Index for every self-dual ternary code (counterexample hunt, closed)

Working notes, 2026-09-25/26, on GJF Conjecture 1.4. TMF background is in `notes/tmf-context.md`.
Companion folder: `ternary60/` (Rust, std only; `cargo build --release`; `theory/` holds
stdlib-Python invariant-theory scripts). Status labels: [P] proved here, [V] exact
computation, [T] cited theorem, [C] conjecture, [H] heuristic.

GJF = D. Gaiotto, T. Johnson-Freyd, *Holomorphic SCFTs with small index*, Canad. J. Math. 74(2) (2022)
573–601, arXiv:1811.00589 (only v1 exists). Theorem numbers below follow arXiv v1.

--------------------------------------------------------------------------------------------

## 0. The result

**Setup [T: GJF §§1–2].**
- C ⊂ F₃ⁿ is a self-dual ternary code. Such codes exist only for 4 | n.
- Λ(C) = preimage of C in (1/√3)Zⁿ is odd unimodular. V_{Λ(C)} ⊃ V_{√3Z}^{⊗n} is a holomorphic N=1 SVOA (a "3-framed" VOA) with G = 3^{−1/2}Σᵢ(Γ_{+√3,i} + Γ_{−√3,i}) and c = n. The cocycles are chosen so that the Gᵢ pairwise anticommute; the 3^{−1/2} and the cocycles are left implicit in GJF.
- Its RR partition function is the Witten index (GJF Prop 2.4, Rem 2.5):

      Index(C) = CWE_C(0, 1, −1) = #{even maximal codewords} − #{odd maximal codewords},

  where a maximal codeword has no zero entry and its parity is the number of 1s mod 2.
- Index(C) = 0 unless 12 | n.
- **Sign.** Negating one coordinate negates Index. This is the Ramond-parity ambiguity of GJF Rem 5.3. So Index is an invariant of the monomial class only up to sign. Every divisibility and mod-48 statement below is sign-invariant.

**TMF prediction [C: GJF Conj 5.4–5.5 (Stolz–Teichner); image theorem T: Hopkins ICM 2002, Prop 4.6].** For n = 12k the theory has degree d = 24k and Φ = Index·Δᵏ. mΔᵏ lies in the image of π_{24k}TMF → MF_{12k} iff 24/gcd(24,k) | m (`notes/tmf-context.md`). At n = 60 (k = 5) this is **24 | Index**.

**What was known [T: GJF Thm 1.3, Conj 1.4].**
- 24 | Index when 24 | n (even neighbours Λ^± plus Borcherds [Bor95, Thm 12.1]).
- 12 | Index when 12 | n (from Index(C⊕C) = Index(C)²).
- GJF conjectured 24 | Index in all lengths. The open case was n ≡ 12 mod 24 (36, 60, 84, …), where the missing piece is exactly 8 | Index.
- GJF say they do not know an elementary proof even of the 24 | n case.

**Theorem [P; V].** For every self-dual ternary code C, **24 | Index(C)**. This is the divisibility half of GJF Conj 1.4. There are two proofs.
- **Proof I (§1, Kneser neighbours; Fourier analysis on F₃ⁿ only):** 8 | Index. The 3-part then comes from GJF Thm 1.3.
- **Proof II (§2, signed 2-design; one fact about modular forms, M₂(SL₂(Z)) = 0):** both 8 | Index and 3 | Index. This is independent of GJF Thm 1.3 and of Borcherds, and re-proves Thm 1.3 without the even-neighbour/Borcherds argument.
- **The existence half of Conj 1.4 (a code of index ±24 in every length 12k) is proved for all k ≥ 1** (Theorem 5.9, §5.1(f‴), 2026-09-26). The codes are explicit: Golay plus tetracodes, glued by *partial* Hadamard quadrupling, which adds 12b to the length and preserves a block-weighted index R_σ. Verified on explicit codes at n = 24, …, 84. Web literature check found no prior solution; not yet checked by a second reader. (Earlier: k = 2^j by doubling, Theorem 5.7.)

**Consequences.**
- Every 3-framed SCFT V_{Λ(C)} (c = n = 12k, N=1 structure from the code) satisfies the TMF-predicted divisibility 24/gcd(24,k) | Index, so ob = 0 in Cok_{24k}.
- Not covered: orbifolds of V_{Λ(C)} by symmetries acting non-trivially on the frame (Aut(C) ⊄ C*, GJF Thm 5.6). These are not 3-framed.
- **The search for a counterexample to the TMF prediction among self-dual ternary codes is closed negatively:** no self-dual ternary code of any length violates it.

Literature checked as of 2026-09-25 (§4): no earlier proof of GJF Conj 1.4, and neither the neighbour identity (★) nor the signed 2-design (◆) appears in print.

--------------------------------------------------------------------------------------------

## 1. Proof I: the neighbour identity, 8 | Index

Write ω = e^{2πi/3}. Let φ: F₃ → Z be φ(0) = 0, φ(1) = −1, φ(2) = +1, and set f(x) := ∏ᵢ φ(xᵢ).
- f(x) = (−1)^{n₁(x)} for x of full weight, and f(x) = 0 otherwise; in particular f(0) = 0.
- For a linear code D put F(D) := Σ_{x∈D} f(x). Then Index(C) = F(C).

If 3 ∤ n, a self-dual code has no full-weight words, since all its words are isotropic and a full-weight x has x·x = n. Then every index is 0 and there is nothing to prove. **Assume 12 | n from here on.**

**Step 1 (f is a Fourier eigenfunction).** Let f̂(u) := Σ_x f(x) ω^{u·x}.
- φ̂(0) = 0, φ̂(1) = ω² − ω = −i√3, φ̂(2) = ω − ω² = i√3. So φ̂ = i√3·φ.
- Hence f̂ = (i√3)ⁿ f = 3^{n/2} f, using 4 | n. For n ≡ 2 mod 4 the sign would flip [V].

**Step 2 (Poisson).** For a linear code D ⊂ F₃ⁿ, Σ_{x∈D^⊥} f(x) = |D|^{−1} Σ_{u∈D} f̂(u) = 3^{n/2}|D|^{−1} F(D). The sign convention of ω^{u·x} does not matter, since D = −D.
- If dim D = n/2 − 1, this reads F(D^⊥) = 3F(D).

**Step 3 (neighbours).** Let C ≠ C′ be self-dual with D := C ∩ C′ of dimension n/2 − 1. These are Kneser 3-neighbours.
- D^⊥ ⊇ C + C′, and dim(C + C′) = n/2 + n/2 − (n/2 − 1) = n/2 + 1 = dim D^⊥, so D^⊥ = C + C′.
- Take c₀ ∈ C∖D and c₀′ ∈ C′∖D. Then c₀·c₀′ ≠ 0: otherwise c₀′ ⊥ D + ⟨c₀⟩ = C, so c₀′ ∈ C^⊥ = C, a contradiction.
- The four cosets d + a c₀ + b c₀′ with a, b ≠ 0 consist of vectors x with x·x = 2ab(c₀·c₀′) ≠ 0.
- Full-weight vectors are isotropic (x·x = n ≡ 0), so the four anisotropic cosets carry none.
- Therefore F(D^⊥) = F(D) + (F(C) − F(D)) + (F(C′) − F(D)), and with Step 2:

      **Index(C) + Index(C′) = 4·F(D).**                                    (★)

**Step 4 (F(D) is even).** f(0) = 0, x ↦ −x is a fixed-point-free involution on D∖{0}, and f(−x) = (−1)ⁿf(x) = f(x). So F(D) ∈ 2Z, and (★) gives Index(C′) ≡ −Index(C) mod 8.

**Step 5 (connectivity and base point).**
- The 3-neighbour graph on self-dual codes of length n is connected. Given C₁ ≠ C₂, pick x ∈ C₂∖C₁ and put C′ := (C₁ ∩ x^⊥) + ⟨x⟩.
  - Since x ∉ C₁ = C₁^⊥, C₁ ∩ x^⊥ has dimension n/2 − 1.
  - x is isotropic and orthogonal to C₁ ∩ x^⊥, so C′ is self-dual and a neighbour of C₁.
  - Since C₁ ∩ C₂ ⊂ C₂ ⊂ x^⊥ and x ∈ C₂, the modular law gives C′ ∩ C₂ = (C₁ ∩ C₂) + ⟨x⟩.
  - So after n/2 − dim(C₁ ∩ C₂) steps we reach C₂. Connectivity is classical; cf. Chakraborty–Chiari–Miezaki–Oura, arXiv:2411.04647, Thm 3.6.
- T = (tetracode)^{⊕n/4} has no full-weight word: the tetracode's nonzero words all have weight 3 < 4, and a full-weight word of a direct sum needs full weight in every block. So Index(T) = 0.
- Hence 8 | Index(C) for all C. □

--------------------------------------------------------------------------------------------

## 2. Proof II: the signed 2-design, 8 | Index and 3 | Index

Found by a subagent of this session (theory pass); independently re-derived and re-checked here [V].

Notation.
- F = the maximal codewords, viewed as ε ∈ {±1}ⁿ by lifting 1 ↦ +1 and 2 ↦ −1.
- s(ε) = (−1)^{#1s} = (−1)^{#(−1)s}; the two agree because n is even.
- Index = Σ_{ε∈F} s(ε).
- Scalar products ε·ε′ are taken in Zⁿ. Reduced mod 3 they are the F₃ inner product, so ε·ε′ ≡ 0 mod 3 for ε, ε′ ∈ F.

**Step 1 (signed 2-design) [P, using the standard transformation law of harmonic theta series; checked by two referees].**

      Σ_{ε∈F} s(ε) εᵢ εⱼ = Index·δᵢⱼ,   equivalently   Σ_{ε∈F} s(ε)(ε·μ)² = Index·|μ|²  for all μ ∈ Rⁿ.   (◆)

*Argument.*
- Let Λ = Λ(C), χ = √3(1,…,1), shadow S = Λ + χ/2, and s(v) = (−1)^{⟨λ,χ⟩} for v = λ + χ/2.
- For a harmonic polynomial H of degree 2, let Φ_H(τ) = Σ_{v∈S} s(v)H(v)q^{v²/2} be the harmonic RR theta. Then

      Φ_H(τ+1) = e(n/24)·Φ_H(τ),      Φ_H(−1/τ) = (τ/i)^{n/2}·τ²·Φ_H(τ).

  - **T:** for v ∈ S, v²/2 ≡ χ²/8 ≡ n/8 mod 1, and n/8 − n/24 = k.
  - **S:** Poisson summation with Hecke's identity for harmonic H of degree 2. Θ_RR is an S-eigenvector of the Weil representation of disc(Λ_ev) ≅ (Z/2)² with eigenvalue (τ/i)^{n/2}.
  - These are the multipliers of ηⁿ times τ², whatever the value of Index, including 0.
  - The harmonic factor is τ², not (τ/i)^{n/2+2}; the two differ by −1 [V: referee check `s_transform.py`, not in the repo].
- Every v ∈ S has the form y/(2√3) with all yᵢ odd, so v² ≥ n/12.
  - Equality holds iff y ∈ {±1}ⁿ and y mod 3 ∈ C. So the norm-n/12 shell of S is in bijection with F, with s(v) = (−1)^{#1s} (GJF Prop 2.4).
- Hence f = Φ_H/ηⁿ satisfies f(τ+1) = f(τ) and f(−1/τ) = τ²f(τ), and is holomorphic at ∞. So f ∈ M₂(SL₂(Z)) = 0.
- The q^{n/24} coefficient gives Σ_F s(ε)·H(ε/(2√3)) = Σ_F s(ε)((ε·μ)² − |μ|²)/12 = 0 for H(x) = (x·μ)² − |μ|²|x|²/n. Since H is even and s(−ε) = s(ε), the sign of the lift is irrelevant. This is (◆).

*Checks.*
- [V: `ternary60 design`] (◆) holds exactly for all pairs i < j on random codes at n = 12, 24, 36, 48, 60, and on P(29) and XQR(59).
- [V: `theory/qseries_check.py`, log `theory/qseries_check.log`] the q-series identity for the Golay code, through q^{1/2+4}: Σ_{v∈S} s(v)(v·μ)²q^{v²/2} = (Index·|μ|²/12)·E₂·ηⁿ.
  - For code lattices the coset series factorise over coordinates. So this identity is equivalent to its leading coefficient (◆), and it is not independent evidence for the modular step.
- [V: `theory/jacobi_invariants.py`, log `theory/jacobi_invariants.log`] for n ≤ 72, (◆) already follows from invariance of the two-point Jacobi polynomial under the Gleason group. This was checked by rank computations mod two large primes.

**Step 2 (8 | Index).**
- For distinct a, b, c, [ε_a = ε_b = ε_c] = (1 + ε_aε_b + ε_bε_c + ε_aε_c)/4. With (◆) this gives Σ_{ε∈F, ε_a=ε_b=ε_c} s(ε) = Index/4.
- On that set, ε ↦ −ε is a fixed-point-free involution preserving s. So Index/4 is even. □
- 8 is sharp, since Index = 24 occurs. The method stops here: the signed set is not a 4-design (M₄(SL₂(Z)) ≠ 0), and 4-point sums differ from Index/8 [V: referee].

**Step 3 (3 | Index).**
- If F = ∅ then Index = 0. Otherwise pick ε₀ ∈ F and put x = ε₀ + 3y with y ∈ Zⁿ.
- Then ε·x ≡ ε·ε₀ ≡ 0 mod 3 for all ε ∈ F, so 9 | Σ_F s(ε)(ε·x)² = Index·|x|² by (◆).
- |x|² = n + 6ε₀·y + 9|y|² ≡ 3k + 6ε₀·y mod 9. For y ∈ {0, e₁, −e₁} this takes the values 3k, 3k+6 and 3k+3 mod 9. Exactly one of them is 0 mod 9, so some y has v₃(|x|²) = 1.
- Hence 3 | Index. □

**Lattice form [P, same proof].** The argument never uses the code, only Λ.

*Hypotheses.*
- **(H1)** L ⊂ Rⁿ is positive-definite, odd and unimodular, of rank n = 12k.
- **(H2)** χ ∈ L is characteristic, S = L + χ/2, and s(λ + χ/2) = (−1)^{⟨λ,χ⟩}.
- **(H3)** min{v² : v ∈ S} ≥ n/12.

Put Index(L) := Σ_{v∈S, v²=k} s(v). Then Θ_RR = Index(L)·ηⁿ (a consequence of (H3), not a replacement for it), and **24 | Index(L)**.

*Proof.*
- As in Step 1, Σ_{v∈S, v²=k} s(v)(v·μ₁)(v·μ₂) = Index·(μ₁·μ₂)/12 for all μᵢ ∈ Rⁿ.
- s(−v) = s(v) because χ² ≡ n ≡ 0 mod 4, and −v ≠ v. So the left side is 2B with B := Σ_{±pairs} s(v)(v·μ₁)(v·μ₂).
- For μᵢ ∈ L_ev, S ⊂ L_ev*, so B ∈ Z. Hence 24 | Index·(μ₁·μ₂).
- If d divides every such μ₁·μ₂, then d^{−1}L_ev ⊂ L_ev*, so dⁿ ≤ [L_ev* : L_ev] = 4 and d = 1. So 24 | Index. □
- Replacing χ by χ + 2μ multiplies s by (−1)^{μ²}, so Index(L) is defined up to sign.

*Remarks.*
- (H3) holds automatically for k = 1, 2, and for every Λ(C). It is a real restriction from k = 3 on; for example D12⁺ ⊕ E8³ has shadow minimum 1 < 3.
- (H3) says exactly that the Ramond sector of V_L has no states below c/24. So 24 | RR index holds for every holomorphic lattice SVOA with that property, N=1 or not. For N=1 lattice SVOAs, unitarity forces (H3).
- Consistency: Z¹² gives 0, D12⁺ = Λ(Golay) gives ±24, O₂₄ = Λ(P(11)) gives ±48 [V: referee].

--------------------------------------------------------------------------------------------

## 3. Remarks

**(a) Orbifold form [P for the identity; H for the VOA reading].**
- Let u := c₀′ and T_u(C) := Σ_{c∈C} f(c)ω^{u·c}.
- Poisson gives T_u(C) = F(−u+C) = F(u+C), since f is even.
- Splitting C into cosets of D gives T_u(C) = F(D) − F(c₀+D) = (3F(D) − Index(C))/2 = F(u+D). With (★):

      Index(C′) = (Index(C) + 8·T_u(C)) / 3.

- [H] This has the shape of the Z/3-orbifold formula (1/3)Σ_{a,b} Z(gᵃ,gᵇ), with all eight nontrivial twisted–twined RR indices equal to T_u [V: verification subagent, exact at n ≤ 12; not in the repo]. The 3-neighbours correspond bijectively to the order-3 subgroups ⟨g_u⟩ ⊂ C* ≅ F₃ⁿ/C (GJF Thm 3.1): lines of C* ↔ hyperplanes D ⊂ C ↔ neighbours C′, with (3^{n/2}−1)/2 of each.
- The expected statement V_{Λ(C′)} ≅ V_{Λ(C)}/⟨g_u⟩ needs the inner-automorphism orbifold theorem for lattice SVOAs (Dong–Mason; Möller–Scheithauer) and a fixed Ramond-parity choice. It is not used in the proofs.

**(b) What an odd-order orbifold does to the class [H; the counterexample is V].**
- An odd-order orbifold does **not** preserve the 2-primary TMF class. The Golay code (|Index| = 24) has 364 neighbours: 220 of index 0, 132 with the same index as Golay and 12 with the opposite sign [V: `ternary60 allnbrs`, log `runs/allnbrs.log`].
- What (★) shows is that the 2-primary obstruction ob_(2) ∈ Cok_(2) gets multiplied by the 2-adic unit 3^{−1}.
  - The untwisted term (1/3)Z(1,1) is 3^{−1}[V], because BG is stably 2-locally a point for |G| odd.
  - The eight twisted terms form one SL₂(Z)-orbit, and 8 = |F₃²∖0| kills Cok_(2) ⊂ Z/8.
- For non-anomalous Z/p with p ≥ 5, p·Index(V/Z_p) = Index(V) + (p²−1)t, and 24 | p² − 1. For Z/2, 2·Index(W) = Index(V) + 3t.
- This matches the prime-by-prime picture in `notes/tmf-context.md`. Level-3 structure (code neighbours, Z/3-orbifolds) controls the prime 2; level-2 structure (GJF's even neighbours Λ^±, bosonisation) controls the prime 3.
- Proof II sidesteps the dictionary: modularity of the RR sector alone gives both primes.

**(c) Nothing finer holds.**
- F(D) ≡ 2 mod 4 occurs [V]; for example Golay has a neighbour of index 0 with F(D) = 6.
- Index mod 48 takes the values 0 and 24 with roughly equal frequency at n = 36 (200,099 : 199,901) [V].
- So 24 is the exact common divisor.

**(d) Averaged form.** Summing (★) over the neighbours of C gives Σ_{C′∼C} Index(C′) = ((3^{n/2−1} − 3)/2)·Index(C). For Golay this is 24·120 = 2880. All 265,720 neighbours of a random length-24 code also satisfy (★) [V: `allnbrs`].
- This is compatible with Nebe's Kneser–Hecke eigenvalues (arXiv:math/0509474, Thms 8–9). Those give only the averaged form, not the pairwise congruence and not the index.

**(e) Invariant theory of the complete weight enumerator is not enough [V: `theory/invariants.py`, log `theory/invariants.log`].**
- Take integral G-invariant polynomials with coefficient 1 on xⁿ plus the orbit congruences a genuine CWE satisfies.
- On that set, Index only takes values in 6Z (n = 12, 24, 48, 60) or 2Z (n = 36, 72).
- Proof II uses the finer two-point (Jacobi) structure, and Proof I uses the neighbour graph.

--------------------------------------------------------------------------------------------

## 4. Computations and literature [V: ternary60/]

**Index algorithm.**
- Normalise a full-weight word to 1 by sign changes; this multiplies Index by ±1. Then Index = ±Σ_{A: 1_A∈C} (−1)^{|A|/3}.
- Enumerate the {0,1}-codewords by a Gray code over an information set: 2^{n/2−1} steps with bitsliced F₃ arithmetic, about 0.15 s per length-60 code on 8 cores.
- Cross-checked against brute force over all 3^{n/2} codewords for n ≤ 24, including random monomial images (`selftest`).

| check | result |
|---|---|
| Golay = P(5) = XQR(11) | \|Index\| = 24 (GJF Ex 1.5) |
| P(11), XQR(23) (n=24, extremal) | \|Index\| = 48 |
| P(17) (n=36) | \|Index\| = 744 = 24·31 |
| P(23), XQR(47) (n=48) | \|Index\| = 96 |
| P(29) (n=60, extremal) | \|Index\| = 21696 = 24·904; 41184 maximal words |
| XQR(59) (n=60, extremal) | \|Index\| = 41184 = 24·1716; 41184 maximal words |
| random self-dual (uniform Kneser walk), n=12/24/36/48 | 400 each, all 24 \| Index |
| n = 36, batch | 400,000 codes, all 24 \| Index; mod 48: 200,099 × 0, 199,901 × 24 |
| n = 60, random | 2,200 codes, all 24 \| Index; \|Index\| = 24 occurs |
| n = 60, walks of 1–8 steps from Golay⁵, P(11)⊕Golay³, P(17)⊕P(11), P(23)⊕Golay, XQR(47)⊕Golay, Golay⁴⊕tetra³ | about 1,200 codes, all 24 \| Index |
| n = 72, random | 60 codes, all 24 \| Index |
| (★) with GJF sign, n = 12, 24, 36, 48 (`nbr`) | exact on every sampled pair; F(D) even; min v₂(F(D)) = 1 |
| (◆), triple count, Step 3 identity (`design`), n = 12…60 | exact on every code tested, incl. P(29), XQR(59) |

Independent checks by verification subagents, with their own code (not in the repo):
- about 7,000 neighbour pairs at n = 8…60;
- all 338 codes of length 24 (Harada–Munemasa database). Every index is a multiple of 24, and 35 codes have |Index| = 24; GJF Ex 1.6 says 30, a discrepancy that is unresolved;
- the Nebe–Villar extremal code NV(29), |Index| = 27024 = 24·1126;
- all 275 near-extremal length-60 codes on Harada's site.

`codes/index24_len60.txt` is a length-60 code of index 24 (random walk, seed 7, #24). It is a second, independently found example; the first is Elkies' code in GJF Ex 5.7(5), which already settled k = 5.

**Literature (checked 2026-09-25).**
- arXiv:1811.00589 still states Conj 1.4 as open in both versions (arXiv v1 and the CJM 2022 paper).
- Citing records searched: INSPIRE (54), Semantic Scholar (38) and OpenAlex (43), with 22 full texts grepped, including Kawabata–Yahagi 2303.11613, 2308.12592, 2409.12527. None contains a proof, a counterexample, (★) or (◆).
- Related but weaker: Nebe (averaged Hecke eigenvalue), and Araya–Harada (A_{12m} ≡ 0 mod 8 for near-extremal codes, unsigned).
- Journal-only coding-theory papers were not full-text searched.

--------------------------------------------------------------------------------------------

## 5. What remains

1. The existence half of GJF Conj 1.4: **proved for all k** (Theorem 5.9, §5.1(f‴)). Remaining: a full citation search (the 2026-09-26 web check found nothing, see §5.1(f‴)) and an independent reading of Lemma 5.8, and optionally a sign-exact (ℤ[ω] or brute-force) check at n ≥ 36.
2. [C] A TMF-level statement behind Remark (b): for a non-anomalous Z/3 acting on a holomorphic N=1 SVOA V, ob_(2)(V/Z₃) = 3^{−1}·ob_(2)(V) in Cok_(2). Its shadow on the Δᵏ-coefficient is 3·Index(V/Z₃) = Index(V) + 8T_u. The naive [V/Z₃] ≡ [V] in π_*TMF_(2) is false; see Remark (b).
3. Proof II for families, or for the refined (Jacobi-form) index of the N=2 structure that V_{Λ(C)} also carries (GJF §2).
4. Before any public claim: consider contacting Johnson-Freyd, since both proofs close a published open case.

### 5.1 The existence half: obstructions, constructions, data (2026-09-25)

Scripts: `ternary60/theory/existence_*.py`, each with a `.log` next to it. They share `existence_common.py` and call the Rust `index`. **Sign caveat:** Rust's `index` normalises a full-weight word to all-ones, so its sign is not meaningful. Sign-exact checks use brute force (`brute_index`, n ≤ 24) or exact ℤ[ω] arithmetic.

GJF (§1, before Ex 1.5; Ex 5.7) found their k ≤ 5 examples by random search over codes with a prescribed automorphism. GJF's Question 0.1 asks for a systematic construction. No family is known to extend.

Notation: T_u(C) = Σ_{c∈C} f(c)ω^{u·c} = F(u+C) (Remark 3(a)). G_C(y,v) = Σ_{x∈y+C} f(x)ω^{v·x} is the sum twisted by y and twined by v. For a direct sum it factorises: G_{⊕C_j} = ∏ G_{C_j}.

**(a) Lemma 5.2 [P] (Z/3-neighbours of direct sums).** Let E, B be self-dual, and let C′ be the neighbour of E⊕B along u = (u_E, u_B) with u_E ∉ E and u_B ∉ B. Then **72 | Index(C′)**.
- *Proof.* The orbifold formula gives 3·Index(C′) = I_E I_B + 8·T_{u_E}(E)·T_{u_B}(B).
- Applied to E and its neighbour E′ along u_E, the same formula gives T_{u_E}(E) = (3I(E′) − I(E))/8.
- By the Theorem, I(E) = 24i and I(E′) = 24i′, so T_{u_E}(E) = 3(3i′ − i). Likewise T_{u_B}(B) = 3(3j′ − j).
- Hence Index(C′) = 72(3ij + 3i′j′ − ij′ − i′j). If a summand has length ≢ 0 mod 12, then T = 0 and the index is 0. □
- [V: `existence_walks.py` part L] 300 mixed neighbours of Golay⊕Golay, Golay⊕code2 and code2⊕code2. The formula holds up to sign in every case, and 72 | I in every case.

**(b) Lemma 5.3 [P] (gluing divisibility; generalises (a)).** Let C be self-dual and [n] = S₁ ⊔ S₂. Put C_i = C ∩ F₃^{S_i}, so the projection of C to S₁ is C₁^⊥. Let F₁(q) be the signed full-weight count of the coset q + C₁, for q ∈ C₁^⊥/C₁. If C₂ ≠ 0 and d := gcd_q F₁(q), then **24d | Index(C)**.
- *Proof, 2-part.* Fix distinct a, b, c ∈ S₂. By (◆), Σ_{ε∈F, ε_a=ε_b=ε_c} s(ε) = Index/4.
  - Split ε = (ε₁, ε₂) along the glue C = ∪_q (q+C₁) × (φq+C₂). This gives Index/4 = Σ_{(q,η)} F₁(q)f(η), where η runs over the full-weight words of φq + C₂ with η_a = η_b = η_c.
  - The map (q, η) ↦ (−q, −η) is a fixed-point-free involution that preserves F₁(q)f(η), since the sign is (−1)^{|S₁|+|S₂|} = 1. So Index/4 ∈ 2dℤ.
- *Proof, 3-part.* Take μ supported on S₂ lifting some 0 ≠ c₂ ∈ C₂.
  - Every full-weight ε satisfies ε·μ ≡ ε₂·c₂ ≡ 0 mod 3, because ε₂ ∈ C₂^⊥. So Index·|μ|² = Σ_q F₁(q)·Σ_η f(η)(η·μ)² ∈ 9dℤ.
  - As in Proof II Step 3, choose μ with v₃(|μ|²) = 1. □
- **Corollaries.**
  - Lemma (a): take S₁ = the coordinates of E. Then C′ ∩ F₃^{S₁} = E ∩ u_E^⊥, and its coset counts are F(E₀), (I_E − F(E₀))/2, (I_{E′} − F(E₀))/2 and 0, all in 3ℤ.
  - Every index-24 code has, across every split with C₂ ≠ 0, a piece coset count that is odd and one that is prime to 3.
  - Any code with a weight-3 word has index 0: adding that word pairs up the full-weight words with opposite signs. So index-24 codes have d_min ≥ 6.

**(c) Gadget substitution is dead [P].** Replace coordinate i of a self-dual W by a *gadget*: a self-orthogonal R ⊂ F₃^k with R^⊥/R = ⟨e⟩, k odd. The result is self-dual with Index = ±∏ aᵢ · Index(W), where a = F(e+R). Here F(R) = 0 because f is odd.
- If one gadget alone does not give length ≡ 0 mod 12, then a = 0. So only k ≡ 1 mod 12 (ν = e·e = 1) and k ≡ 11 mod 12 (ν = −1) can have a ≠ 0.
- **ν = −1, k ≡ 11 mod 12.** Gluing the gadget to one extra coordinate gives a self-dual code of length k+1 and index −2a, so 12 | a. Conversely, shortening an index-(∓24) code at one coordinate gives a gadget with a = ±12.
- **ν = +1, k ≡ 1 mod 12, k ≥ 3.** Substitute the gadget into Golay at one coordinate and apply Lemma 5.3 with S₁ = the other 11 Golay coordinates. The coset counts there are 0 and ±12, so 24·12 | 24a, i.e. **12 | a**.
- Every substituted code therefore has index 24·∏aᵢ ∈ 288ℤ unless all gadgets are trivial.
- The same applies to Golay with d ≤ 3 coordinates replaced by any nonzero piece: the gcd of the Golay A-vector is 12, 6, 3 for d = 1, 2, 3 (`existence_connected_sum.py` part A).
- [V: `existence_gadgets.py`] 3,000 random gadgets at k = 13 and 1,000 at each of k = 5, 7, 9, 11: every a lies in 12ℤ.

**(d) Multi-step orbifold formula [P; V].** Let W ⊂ F₃ⁿ be isotropic of dimension r with W ∩ C = 0. Then C_W := (C ∩ W^⊥) + W is self-dual, and
      **Index(C_W) = 3^{−r} Σ_{w,v∈W} G_C(w, v).**
- *Proof.* C_W = ⊔_w (w + C∩W^⊥). Then [c ∈ W^⊥] = 3^{−r}Σ_{v∈W} ω^{v·c}, and v·w = 0 by isotropy.
- Every r-step Kneser walk is such a C_W. The r = 1 case is Remark 3(a).
- [V: `existence_orbifold.py` part V] Exact ℤ[ω] evaluation agrees with the Rust index up to sign on chains Golay–tetra³–Golay, Golay–code2, code2–tetra³–Golay, and Golay³.
- **Leaf corollary [P].** Suppose some component L of C = ⊕C_j sees W only through one vector: W = W′ ⊕ ⟨w⟩ with W′ vanishing on L. Then 72 | Index(C_W).
  - Here C_W = (C_{W′})_w, and C_{W′} = L ⊕ R′.
  - If w_{R′} ∉ R′, apply (a). Otherwise C_W = L_{w_L} ⊕ R′, whose index is in 576ℤ.
  - So chains, and more generally tree-shaped gluings with 1-dimensional bonds, never give 24. The glue graph needs a cycle.
- **[C]** If dim W < number of components, then 72 | Index(C_W). Data [V: `existence_walks.py` part W]: walks from Golay⊕code2^m keep 72 | I for the first m steps, and |I| = 24 first appears at step m+1, at n = 24, 36, 60.

**(e) Ring transfer matrices [V].** For a ring of components with 1-dim bonds, Index = Tr(N₁⋯N_s). The N_j are **integer** 9×9 matrices, and conjugation takes N_j to M_j/3, where M_j[(a,b),(a′,b′)] = G_{C_j}(az + a′y, bz + b′y).
- A cell that gives index 24 in every ring length must have all nonzero eigenvalues equal to roots of unity (Kronecker).
- Tetracode 3-cells: nilpotent (index 0) or eigenvalues 8·(cube roots of 1). Rings of 3j tetracodes have index 0 or ±24·8^{j−1}; j = 1 is Golay.
- code2 cells have spectral radius 0 or ≥ 3. Golay cells have radius ≥ 6. No Kronecker cells appear (`existence_orbifold.py` parts T, S).
- Golay rings with 2-dim bonds (81×81): power sums grow like random codes, p₅ ~ 10³ (`scratch/bond2.py`).
- E₃-glued codes (E₃^m glued by a self-dual W): F(u+C) = 3^{m/2}·∏_j ψ(u_j·111), with ψ = (0, 1, −1). So the coset counts are 0 or ±3^{m/2} [P]; this matches code2's {0, ±9}.

**(f) Hadamard gluing [P; V].** Let H act as (x_i, x_j) ↦ (x_i + x_j, x_i − x_j) on every pair of a perfect matching. Since HHᵀ = −I, this is an anti-isometry, so it maps self-dual codes to self-dual codes.
- The full-weight words of H(C) correspond to the words of C with exactly one nonzero entry per pair.
- For cross-pairing, Index(H(E ⊕ E′)) = Σ_{u∈E, u′∈E′, supp u ⊔ supp u′ = [m]} (−1)^{wt u′} = Σ_{T⊂[m]} (−1)^{|T|} 3^{d_E(T)+d_{E′}(T^c)}. Here d_E(T) is the dimension of the subcode of E supported in T, so only the matroid enters.
- Against tetracode blocks: **Index(H(E ⊕ σT^{m/4})) = Σ_{c∈E} ∏_b λ(|supp c ∩ b|)**, with λ = (0, −2, 0, 0, 1).
- **n = 24:** Index(H(Golay ⊕ σT³)) = **−24 + 8h**, where h counts the weight-6 supports of σT³ that are hexads. h = 0 or 6 gives explicit index-24 codes with a closed-form count [P; V: part A, 40/40, the first four sign-exact].
- **2-adic obstruction [P].** Each switched-on component of a Hadamard-glued direct sum contributes a factor 2 (±). Golay² vs tetra⁶ gives Index ≡ 0 mod 16, and so does any gluing where every configuration has ≥ 4 switched-on components. The pieces must have length ≳ n/6.
- **Doubling [V: part C].** 200 random codes H(E₂ ⊕ σT⁶), with E₂ one of the n = 24 index-24 codes, all have **Index ≡ 24 mod 48** (two independent runs of 200). |I| = 24 occurs in 3% (logged run) to 6% (scratch run) of samples. The mod-48 invariance is now Theorem 5.4 below.
- The λ-formula matches Rust exactly at n = 48 (part B).
- Hadamard rings of Golays (6+6 splits; 64×64 transfer matrix with no 3^{−r}) grow like random codes (part D).

**(f′) Mod-48 invariance of doubling, and parity of maximal codewords [P; V].**

*Tool: mod-16 propagation.* Let Λ: F₃^m → ℤ be supported on isotropic vectors, with Λ̂ = 3^{m/2}Λ and Λ(−x) = Λ(x). Let C, C′ be neighbours with D = C ∩ C′, and write S(X) = Σ_{x∈X}Λ(x).
- The proof of (★) applies verbatim and gives **S(C) + S(C′) = 4S(D)**.
- For two such functions Λ₁, Λ₂, put Ψ = S₁ − S₂. Suppose Ψ(D) ≡ 0 mod 4 for every such D. Then Ψ(C′) ≡ −Ψ(C) mod 16.
- So if Ψ vanishes mod 16 on one self-dual code, it vanishes mod 16 on all of them, by connectivity of the neighbour graph (Proof I, Step 5).

**Theorem 5.4 [P].** Let E be self-dual of length m ≡ 0 mod 12, and let σ be any partition of [m] into 4-blocks. Then
      **Index(H(E ⊕ σT^{m/4})) ≡ Index(E) (mod 48).**
- *Proof.* By (f), the left side is S(E) with Λ(x) = ∏_b λ(|supp x ∩ b|).
- **Λ is a Fourier eigenfunction.** On one block F₃⁴, summing over single-point and full-support y gives λ̂(v) = −2(8 − 3 wt v) + 2^{4−wt v}(−1)^{wt v} = 9·λ(wt v). So Λ̂ = 9^{m/4}Λ = 3^{m/2}Λ, the same eigenvalue as f.
- **Λ is supported on isotropic vectors.** Its support consists of weights 4·(m/4) − 3j ≡ 0 mod 3.
- Take Λ₁ = Λ and Λ₂ = f, so Ψ(X) = Σ_X (Λ − f).
  - On each word, Λ − f is even. Full words give 1 − (±1) ∈ {0, 2}. Words with a single-point block give (−2)^j with j ≥ 1, while f = 0 there. All other words give 0.
  - Words pair off as ±x with equal values. Hence Ψ(D) ∈ 4ℤ.
- **Base code.** Take a tetracode on each σ-block. Every block meets a word in 0 or 3 points, so Λ ≡ 0; there are no full-weight words, so f ≡ 0. Hence Ψ = 0 there.
- By propagation, Index(H) ≡ Index(E) mod 16. Both sides lie in 24ℤ (the Theorem, lengths 2m and m), so they agree mod 48. The sign convention of H is irrelevant, since −24 ≡ 24 mod 48. □
- *Consequence.* Doubling preserves Index/24 mod 2. It sends index-24 codes to codes with Index ≡ 24 mod 48, never to 0 or 48 mod 48, but it does not fix the exact value. That matches the spread seen in (f).

**Proposition 5.5 [P].** In every self-dual ternary code, **the numbers of even and of odd maximal codewords are both divisible by 8.** Equivalently, |F| ≡ Index mod 16. I have not checked the literature for this.
- *Proof.* Put U(X) = number of full-weight vectors in X, and Δ = U − F = 2·#odd. Full-weight vectors are isotropic, so Δ(C) + Δ(C′) = Δ(D^⊥) + Δ(D), and F(D^⊥) = 3F(D).
- U is not a Fourier eigenfunction. Poisson summation with 1_{≠0} (Fourier values 2 at 0, −1 elsewhere) gives 3^{n/2−1}U(D^⊥) = Σ_{u∈D} 2^{n−wt u}(−1)^{wt u}.
  - Mod 16 only wt u ∈ {n, n−3} survive, since weights of D are ≡ 0 mod 3. The weight-(n−3) term is 8A_{n−3}(D), and A_{n−3}(D) is even. So U(D^⊥) ≡ 3^{1−n/2}U(D) = 3·9^k·U(D) mod 16, where n = 12k.
  - Since U(D) is even, U(D^⊥) + U(D) ≡ 4U(D) mod 16.
- Hence Δ(C) + Δ(C′) ≡ 4(U(D) − F(D)) = 8·#odd(D) ≡ 0 mod 16, because #odd(D) is even (±x have the same parity when n is even).
- The base code T^{n/4} has Δ = 0. Connectivity finishes the proof. □
- *Checks.* Golay has 24 even and 0 odd maximal codewords. The n = 24 codes E₂ with Index −24 have 24 and 48.

[V: `existence_mod48.py`, log `existence_mod48.log`] Four numerical checks: λ̂ = 9λ on all of F₃⁴; S(C) + S(C′) = 4S(C∩C′) on random neighbour pairs at m = 12, 24; Theorem 5.4 mod 16 on random E and σ at m = 12, 24; Proposition 5.5 on random codes at n = 12, 24 exactly and at n = 36, 48, 60 via Rust's full_weight count.

**(f″) Refinement invariance and index 24 at every length 12·2^j [P; V].**

Notation: S_σ(E) := Σ_{c∈E} ∏_{b∈σ} λ(|supp c ∩ b|). By (f), Index(H(E ⊕ σT)) = S_σ(E), where T is a tetracode on each σ-block and the pairs are (i, m+i).
- *Refinement.* Let E′ = H(E ⊕ σT). A refinement σ′ of σ is obtained by splitting each σ-block {a,b,c,d} into two pairs {a,b}, {c,d}. The E′-blocks are then {a, m+a, b, m+b} and {c, m+c, d, m+d}.

**Lemma 5.6 [P].** For every code E, every 4-block partition σ, and every refinement σ′: **S_{σ′}(E′) = S_σ(E).**
- *Proof.* A word of E′ is H(e, t) with e ∈ E and t ∈ σT.
- On the H-pair of coordinate i, H(e, t) has the following state:
  - X (both entries nonzero) iff exactly one of e_i, t_i is nonzero;
  - B (exactly one entry nonzero) iff both e_i, t_i are nonzero;
  - N (both zero) iff e_i = t_i = 0.
- So a refined block {i, i′, j, j′} meets the word in cnt(i) + cnt(j) points, with cnt(X, B, N) = (2, 1, 0).
- λ of that count is 1 for XX, −2 for {B, N}, and 0 otherwise. The weight therefore factorises over the σ-blocks.
- Fix a σ-block β = {p, q, k, l} with matched pairs {p, q}, {k, l}, and put A = supp e ∩ β. Sum over t|β:
  - t|β = 0 contributes [A = β].
  - t|β with support β∖{p} (2 words):
    - The edge {k, l} (away from p) needs XX, i.e. a_k = a_l = 0.
    - The edge {p, q} needs (a_p, a_q) = (1, 0), weight +1, or (0, 1), weight −2.
- Collecting the cases gives W_β(A) = 1 for A = β, −2 for |A| = 1, and 0 otherwise.
  - For A = {p}: t missing p gives +2; t missing the partner q gives 2·(−2) = −4.
  - So W_β(A) = λ(|A|). □
- [V: `existence_refinement.py` part 1] 40/40 random self-dual E of length 12 with random σ, σ′, enumerated exactly.

**Theorem 5.7 [P; V]. For every j ≥ 0 there is a self-dual ternary code of length 12·2^j and index ±24.**
- *Construction.* E₀ = Golay, with a partition σ₀ into three 4-blocks such that S_{σ₀}(Golay) = −24 + 8h(σ₀) = ±24, i.e. h ∈ {0, 6}. Put E_{j+1} = H(E_j ⊕ σ_jT^{m_j/4}), and let σ_{j+1} be any refinement of σ_j.
- *Proof.* By the λ-formula, Index(E_{j+1}) = S_{σ_j}(E_j). Lemma 5.6 applied j times gives S_{σ_j}(E_j) = S_{σ₀}(E₀) = ±24. □
- **Explicit start.** σ₀ = {1,2,10,11}, {3,4,8,9}, {0,5,6,7} for the `GOLAY` generator in `existence_common.py`, which has h = 0 and S = −24.
- **Checks.** E₁ (n = 24) has Index 24 by brute force. For random refinements σ₁, S_{σ₁}(E₁) = 24 and E₂ (n = 48) has Rust Index ±24 (`existence_refinement.py` part 2).
- Part 3 lists h over all 5775 partitions of the Golay coordinates. Only h = 12 fails.
- [V: `existence_matchings48.py`] Scanned all 10,395 pair-matchings M for the second doubling. 1,083 give |S| = 24, and they include all 27 in-block matchings (the refinements), each giving exactly Index(E₁) = −24. This scan is how Lemma 5.6 was found.
- This is the systematic construction GJF Question 0.1 asks for, but only for lengths 12·2^j. The codes are explicit: Hadamard pairings and tetracode blocks, iterated from Golay.

**What this reduced the rest of the conjecture to** (superseded by (f‴) below, which needs no seeds).
- Lemma 5.6 holds for *any* seed pair (E, σ). So one pair (E, σ) at length 12k₀ with S_σ(E) = ±24 gives index-24 codes at every length 12k₀·2^j with j ≥ 1. E need not have index 24; by Theorem 5.4 it needs Index(E) ≡ 24 mod 48.
- So Conj 1.4 (existence) ⟸ for each odd k₀ ≥ 3: (i) an index-24 code at length 12k₀, and (ii) a seed pair at length 12k₀.
- For k₀ = 3 and 5, (i) is known (GJF Ex 5.7; `codes/index24_len60.txt`).
- **Seed search at k₀ = 3 [V, 2026-09-26; rerun with `existence_seed_search.py`]: none found yet.** Tried 80 random σ each for E = P(17) (Index −744) and for a random index-24 code of length 36, with Rust at n = 72, about 10 s per σ.
  - All 160 values satisfy S ≡ 24 mod 48, as Theorem 5.4 predicts. Their standard deviation is about 7,600–8,100, and the smallest |S| was 120.
  - A Gaussian estimate gives a hit rate of about 0.5% per σ, i.e. roughly 200 tries (about 35 min). A longer run or a local search over σ should find a seed, which would give all k = 3·2^j.
  - At k₀ = 5 the doubled length is 120, beyond the Rust enumeration (2^59 steps). S_σ(E) would need a different algorithm.
- S behaves like an index under gluing and neighbour steps (it is an index), so the obstructions of (a)–(e) apply to finding seeds as well.
- An operation that preserves S and changes the length by an odd factor, or by +12, would finish the conjecture. None is known: every Hadamard-type move doubles the length. There is no tripling analogue either: F₃³ admits no anti-isometry (det² = −1 is impossible), and O₃(F₃) is the signed-permutation group of order 48, generated by reflections in the anisotropic vectors of weight 1 and 2.

**(f‴) Partial quadrupling and index 24 at every length 12k [P; V] (2026-09-26).**

The seed search above is unnecessary: doubling only *some* coordinates, twice, changes the length by +12b instead of ×2, and this reaches every k.

*Partial block systems.* A partial system σ on [m] is a set of b disjoint 4-blocks. The remaining s = m − 4b coordinates are *singletons*. Put
      **R_σ(E) := Σ_{c∈E} ∏_{i singleton} φ(c_i) · ∏_{β∈σ} λ(|supp c ∩ β|).**
- b = 0 gives R = Index(E); s = 0 gives R = S_σ(E) of (f″).

*Partial quadrupling Q_σ.* Let E be self-dual of length m, and σ a partial system with blocks β = (p, q, k, l).
- **Step 1.** Put a tetracode T₁ on 4 new coordinates beside each β, and apply H to the pairs (β_i, β_i*), where β_i* is the new coordinate beside β_i. Refine each doubled block into the two *step-1 blocks* {p, p*, q, q*} and {k, k*, l, l*}. There are 2b of them.
- **Step 2.** Put a tetracode T₂ beside each step-1 block B and apply H to the pairs (B_i, B_i**).
- Singletons are untouched. The result Q_σ(E) has length m + 4b + 8b = **m + 12b**.
- **Self-dual.** Write a vector of E ⊕ T₁^b ⊕ T₂^{2b} as (e, t₁, t₂). Step 1 is an anti-isometry on the block part of (e, t₁); step 2 is an anti-isometry on the block part plus t₂. The form on the image is therefore ⟨e,e′⟩ + ⟨t₁,t₁′⟩ − ⟨t₂,t₂′⟩, which vanishes on E ⊕ T₁^b ⊕ T₂^{2b}. The map is bijective, so the image is self-dual.
- (One step alone is not enough: it is an anti-isometry on the blocks and the identity on the singletons, so it does not preserve self-orthogonality. This is why the naive "partial doubling" fails and the tripling remark above does not apply.)

**Lemma 5.8 [P].** Let σ be a partial system on a self-dual E, and let σ″ be obtained by choosing any subset of the 2b step-1 blocks and refining each once more (in Q_σ(E) coordinates, B = {w,x,y,z} ↦ {w, w**, x, x**}, {y, y**, z, z**}). Then
      **Index(Q_σ(E)) = R_σ(E)   and   R_{σ″}(Q_σ(E)) = R_σ(E).**
- *Proof.* Every weight involved factorises over singletons and over the blocks of σ, and so do Q_σ, T₁ and T₂. Sum over t₂ and then t₁ block by block.
  - A singleton contributes φ(e_i) throughout.
  - Step 2, one step-1 block B, with u the step-1 word: an unrefined B (weight φ⁸ on its 8 coordinates) contributes Σ_{t₂} φ⁸(H(u_B, t₂)) = λ(|supp u ∩ B|). This is the local form of the λ-formula of (f). A refined B (weight λλ) contributes the same, by the local computation in the proof of Lemma 5.6.
  - Step 1, one σ-block β: the two step-1 blocks carry λλ, so Σ_{t₁} gives λ(|supp e ∩ β|), again by Lemma 5.6.
  - Taking every step-1 block unrefined gives Index(Q_σ(E)) = R_σ(E); any other choice gives R_{σ″}. □
- Theorem 5.7 is the special case s = 0 (two doublings at once).
- [V: `existence_quadruple.py` part 1] Random self-dual E of length 12, random single block (n = 24, brute force, sign-exact): Index(Q_σ(E)) = R_σ(E), and R_{σ″} = R_σ for all four σ″, on 40/40.

**Theorem 5.9 [P; V]. For every k ≥ 1 there is a self-dual ternary code of length 12k and index ±24.** This is the existence half of GJF Conj 1.4, and it answers GJF Question 0.1 with an explicit construction.
- *Engine.* Suppose (E, σ) has length m, |σ| = 2, and R_σ(E) = ±24. Q_σ(E) has length m + 24 and Index ±24. It has 4 step-1 blocks; refining exactly one gives σ″ with |σ″| = 2 and R_{σ″}(Q_σ(E)) = ±24 (Lemma 5.8). So the pair propagates, (m, 2) → (m + 24, 2).
- *Odd k.* Over all partial systems on Golay with b = 2, R_σ(Golay) ∈ {±24, ±72}, and 13,365 of the 17,325 give ±24. Starting from one of them, the engine gives index-24 codes at lengths 12 + 24j = 12(2j+1) for all j ≥ 1, and Golay covers k = 1.
- *Even k.* For every single block β, R_β(Golay) = ±24 (all 495). Q_β(Golay) has length 24, Index ±24, and 2 step-1 blocks; refining one gives a pair (24, 2) with R = ±24. The engine gives lengths 24 + 24j. □
- By Theorem 5.4's argument, R_σ(E) ≡ Index(E) mod 48 is expected as well (Λ = φ^s λ^b is again a Fourier eigenfunction supported on isotropic vectors), but it is not needed.
- [V: `existence_quadruple.py` parts 2–3] The R-distributions on Golay above, and the explicit chains (12,1) → 24 → 48 → 72 and (12,2) → 36 → 60 → 84, each step with b″ = 2. Every code is self-dual and has |Index| = 24 (brute force at n = 24; Rust at n ≥ 36). n = 72 and n = 84 were the first open cases.
- The codes are explicit: Golay plus tetracodes, glued by coordinate-pair Hadamard maps. Generator matrices: `ternary60/codes/quad_index24_len{24,36,48,60,72,84}.txt`.
- **Status.** Proved here, but not yet checked by a second reader. The proof uses only the λ-formula of (f) and the local computation of Lemma 5.6, both elementary and verified numerically.
- **Literature check (2026-09-26; web search plus direct arXiv access).** INSPIRE and Semantic Scholar were blocked. Google Scholar was reachable by curl but answered with its "unusual traffic" CAPTCHA (HTTP 429), so no citation list of GJF could be read from the cloud session. Findings:
  - GJF's own wording (TeX line 293), Question 0.1: *"Is there a systematic construction of self-dual ternary codes of index 24 which would avoid the use of intensive computation?"* GJF (line 399) found their examples by random search with Elkies. Theorem 5.9 answers this question.
  - arXiv abstract searches for combinations of ternary code / self-dual ternary / supersymmetric index / superconformal / holomorphic SCFT / TMF return only GJF itself. The same holds for the arXiv author listings of Johnson-Freyd and Gaiotto.
  - arXiv:2609.17359 (Sept 2026, extremal N=1 AdS₃) cites GJF only for the 24/gcd(24,n) divisibility, "verified in nontrivial classes of examples" (GJF; Albert–Kaidi–Lin, *Topological modularity of supermoonshine*, PTEP 2023). It mentions neither a construction at all k nor a proof of Conj 1.4. Albert–Kaidi–Lin treat orbifolds of supermoonshine, not index-24 families.
  - Search engines still describe Question 0.1 and Conj 1.4 as open. Lin–Pei (arXiv:2112.10724) treats bosonic holomorphic CFTs only.
  - The ingredients are standard: gluing through pair maps (x, y) ↦ (x+y, x−y) (cf. (u|u+v)-type and doubling constructions), tetracode sums, and Hadamard-matrix constructions of ternary self-dual codes (e.g. Araya–Harada–Momihara, arXiv:2205.15498). No source found that tracks the index, or a block-weighted index like R_σ, through such maps. Lemmas 5.6/5.8 appear new.
  - To do before any public claim: a proper citation search of GJF (Google Scholar "Cited by" / INSPIRE), done by hand in a browser, and contact with Johnson-Freyd (§5 item 4).

**(g) Coordinate connected sum [P; V].** Delete d-sets V₁ ⊂ C₁ and V₂ ⊂ C₂, and match the deleted values through an anti-isometry φ of F₃^d.
- The result is self-dual of length n₁ + n₂ − 2d, with Index = Σ_q A₁(q)A₂(φq). Here A(q) is the signed count of words restricting to q on V and full-weight off V.
- Golay's A-vector has gcd 12, 6, 3, 1 for d = 1, 2, 3, 6. For d = 6 the entries are 0 and ±1. A(0) = ±2 occurs only when the complement of V is a hexad.
- Chains of cells of length 12 + 2d add 12 per cell and have integer 3^d × 3^d transfer matrices.
- d = 2 (length-16 cells): 300 random cells have spectral radius 0 or ≥ 6 (`existence_connected_sum.py`).

**(h) Assessment.**
- Every *uniform* construction tried grows like random codes, with per-cell spectral radius ≥ 3: rings or chains with 1- or 2-dim bonds, Hadamard rings, connected-sum chains.
- A family with index exactly 24 at every length needs one of:
  1. a cell whose transfer matrix has an eigenvalue exactly 1, with a defect whose support lies in that eigenspace;
  2. a non-uniform, adaptive construction, e.g. choosing σ at each Hadamard doubling to kill all but the leading terms, as h = 0 does at n = 24. Theorem 5.4 shows doubling cannot leave the class Index ≡ 24 mod 48, so only the size of |Index| needs controlling;
  3. a probabilistic argument. Heuristically E[Index²] ≈ 24·(2/√3)^n (average over all codes; the pair count uses that f̂ is an eigenfunction). Index-24 codes should then have density ~ (√3/2)^{n/2}, far above 1/#codes, but a local limit theorem for Index is not in reach.
- A disproof looks implausible: at n = 60, |I| = 24 turns up in a few percent of random codes.
