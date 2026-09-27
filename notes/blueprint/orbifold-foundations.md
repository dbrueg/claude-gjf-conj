# Blueprint: orbifold foundations (the VOA side of the Main Question, as used)

Proof file, 2026-09-27. Purpose: state precisely, and prove where possible, the vertex-algebra facts that the answer to GJF's Main Question uses, so that a Lean development can take the VOA side as a short, explicit list of hypotheses and formalize the rest. It covers:
- **(a)** the hypotheses of GJF Thm 4.2 in the super setting: regularity of V^G for V = V_{Λ(C)} and G solvable (via the even part and Carnahan–Miyamoto), the G̃-crossed structure (McRae), and the holomorphic N=1 structure of V//G;
- **(b)** GJF Prop 2.4 ("index = index"): Ramond ground states of V_{Λ(C)} ↔ maximal codewords, with parities, sign-exact;
- **(c)** twisted modules of odd lattice SVOAs: uniqueness for holomorphic V, the form S[g] ⊗ T_g for fixed-point-free g, the vacuum energy, and the frame computations behind [MQ] Lemma 8.3 and [OI] Lemma 3.1.

For every cited statement the file says whether the literature proves it **for vertex operator superalgebras** or only for VOAs, and flags what is folklore.

Sources in the repository: [MQ] `notes/main-question.md`; [OI] `notes/orbifold-index.md`; [I] `notes/ternary-code-index.md`; [EQ] `notes/blueprint/equivariant-quadrupling.md`; [CS] `notes/blueprint/chains-and-seeds.md`; [GJF] `literature/gjf-1811.00589.tex` (numbering: Prop 2.4 = `prop.index=index`, Rem 2.5 = `remark.alternateproof`, Thm 3.1 = `thm.symmetries lift`, Thm 4.2 = `thm.anomaly`, Ex 4.4 = `eg.anomaly of a lattice automorphism`, Thm 5.6 = `thm.answers`); [Lean] `lean/GJF/*.lean`.

Status labels: [P] proved in this file; [T] cited theorem with exact reference; [T*] cited, but only a proof sketch exists in the literature (folklore level); [V] exact computation (script cited); [H] heuristic estimate.

Script: `ternary60/theory/blueprint_foundations.py` (stdlib Python, ≈ 3 s), log `blueprint_foundations.log` beside it, cited as [V: Part n].

Literature (theorem numbers are those of the arXiv versions, whose sources were read on 2026-09-27; journal numbering may differ):
- [BK04] B. Bakalov, V. Kac, *Twisted modules over lattice vertex algebras*, in *Lie Theory and Its Applications in Physics V* (Varna 2003), World Sci. 2004, 3–26, arXiv:math/0402315. Integral (also odd) lattices; V_Q is then a vertex superalgebra with p(e^α) = |α|² mod 2 (their §4.1). Thm 4.1 (V_Q), Prop 4.1 (lifts e^α ↦ η(α)⁻¹e^{σα}, η: Q → ±1), Lemma 4.4 (centre), Def 4.1 (P_σ, Z_σ), Def 4.2 and the equation before it (defect d(σ)² = |(Q ∩ 𝔥₀^⊥)/Q_σ|), **Thm 4.2** (σ-twisted V_Q-modules: semisimple, simple objects ↔ Z_σ), Rem 4.4 (structure S(𝔥̂_σ⁺) ⊗ e^{λ₀}ℂ[π₀Q] ⊗ ℂ^{d(σ)}).
- [Li96] H. Li, *Local systems of twisted vertex operators, vertex operator superalgebras and twisted modules*, Contemp. Math. 193 (1996) 203–236, arXiv:q-alg/9504022. **Prop 5.4**: the Δ(h,z)-operator turns σ-twisted modules into σe^{2πih(0)}-twisted modules; stated and proved **for vertex operator superalgebras**.
- [DZ05] C. Dong, Z. Zhao, *Modularity in orbifold theory for vertex operator superalgebras*, CMP 260 (2005) 227–256, arXiv:math/0411524. Thm 4.12 (S|γ ∈ 𝒞((g,h)γ)), Thm 5.2 (trace functions lie in 𝒞(g,h)), Thm 7.1 (they form a basis), Thm 7.6 (dimension counts), **Thm 7.7** (V holomorphic and C₂-cofinite ⇒ for each finite-order g a unique σ-stable simple g-twisted module V(g); if ⟨g,h⟩ is cyclic, 𝒞(g,h) is spanned by T_{V(σg)}). Their (g,h)-function is tr_{M} φ(σh) q^{L₀−c/24} on a gσ-twisted module M, and SL₂(ℤ) acts by (g,h) ↦ (g^a h^c, g^b h^d) (their §1).
- [DRY22] C. Dong, L. Ren, M. Yang, *Super orbifold theory*, Adv. Math. 405 (2022) 108481, arXiv:2104.03533. **Prop 3.4** (a self-dual, regular VOSA of CFT type is g-rational for every finite-order g), Lemma 3.5, Thm 4.1, Thm 5.6 (every irreducible V^G-module, σ ∈ G, occurs in a twisted V-module), Thm 6.3 (quantum dimensions).
- [CM16] S. Carnahan, M. Miyamoto, *Regularity of fixed-point vertex operator subalgebras*, arXiv:1603.05645 (v4). **Cor 5.25** (T simple, regular, L₀ ≥ 0, self-dual, G finite solvable ⇒ T^G simple, regular, L₀ ≥ 0, self-dual), Cor 5.26, Thm 6.2. **VOAs only.**
- [McR21] R. McRae, *Twisted modules and G-equivariantization in logarithmic conformal field theory*, CMP 383 (2021) 1939–2019, arXiv:1910.13226. **Thm 4.15, Thm 4.17** (= its Main Theorem 1): V a simple VOSA, G ∋ P_V finite, 𝒞 a category of V^G-modules with vertex tensor category structure containing V ⇒ Rep V is a braided G-crossed supercategory whose objects are sums of g-twisted modules, and 𝒞 ≅ (Rep V)^G. **Stated for vertex operator superalgebras.** Thm 4.20 (semisimplicity; VOAs).
- [HM23] G. Höhn, S. Möller, *Classification of self-dual vertex operator superalgebras of central charge at most 24*, arXiv:2303.17190. §2.3 (V strongly rational ⟺ V₀̄ strongly rational and V₁̄ a simple current of order 2; via [DH12], [ABD04], [CM16]), §2.7 (lattice SVOAs; modules [BK04], σ-twisted modules [Li96]), §3.1 and Table 1 (Rep(V₀̄) of a nice self-dual SVOA depends on c mod 8).
- [vE13] J. van Ekeren, *Modular invariance for twisted modules over a vertex operator superalgebra*, CMP 322 (2013) 333–371, arXiv:1111.0682. Thm 1.3 (main theorem), §12 (lattice VOSAs: NS and Ramond modules and their supercharacters). **Convention warning**: his "1-twisted" modules are Ramond and his "σ-twisted" modules are NS (end of his §1), the opposite of all other sources here.
- [DLM00] C. Dong, H. Li, G. Mason, CMP 214 (2000) 1–56, arXiv:q-alg/9703016: Thm 10.3 (holomorphic C₂-cofinite **VOA**: unique simple g-twisted module). [DLM97] Adv. Math. 132 (1997) 148–166, arXiv:q-alg/9508018: **Thm 3.16** (V_L regular for positive-definite even L). [D93] C. Dong, J. Algebra 161 (1993) 245–265 (modules of V_L, L even).
- [Kac98] V. Kac, *Vertex algebras for beginners*, 2nd ed. 1998, Ch. 5 (lattice vertex superalgebras for integral lattices; [vE13] §12 cites p. 148). [FLM88] (even lattices; GJF cite its Thm 8.10.2). [Lep85] J. Lepowsky, PNAS 82 (1985) 8295–8299, and [DL96] C. Dong, J. Lepowsky, J. Pure Appl. Algebra 110 (1996) 259–295: twisted modules for **even** lattices. [BDM02] K. Barron, C. Dong, G. Mason, CMP 227 (2002) 349–384: permutation orbifolds of tensor powers of **VOAs**.
- [HKL15] Huang–Kirillov–Lepowsky, CMP 337 (2015) 1143–1159, Thm 3.2 (VOA extensions ↔ commutative algebras); [CKL20] Creutzig–Kanade–Linshaw, Commun. Contemp. Math. 22 (2020), Thm 3.13 (the super version); [CKM24] Creutzig–Kanade–McRae, Mem. AMS 295 (2024) no. 1472, arXiv:1705.05017 (module categories of VOSA extensions; untwisted modules only); [KO02] Kirillov–Ostrik, Adv. Math. 171 (2002) 183–227, Thm 3.3; [Hua08] Y.-Z. Huang, Commun. Contemp. Math. 10 (2008) 871–911 (Rep of a strongly rational VOA is modular).
- [DNR21] Dong–Ng–Ren, *Vertex operator superalgebras and the 16-fold way*, Trans. AMS 374 (2021) 7779–7810. [DNR25] Dong–Ng–Ren, *Orbifolds and minimal modular extensions*, arXiv:2108.05225 (Adv. Math. 2025): for holomorphic **VOAs**, Rep(V^G) ≅ 𝒵(Vec_G^α). [Kir02] A. Kirillov Jr., CMP 229 (2002) 309–335. [Mü04] M. Müger, J. Algebra 277 (2004) 256–281. [JFR] T. Johnson-Freyd, D. Reutter, *Minimal nondegenerate extensions*, J. Amer. Math. Soc., arXiv:2105.15167.
- [DL93] C. Dong, J. Lepowsky, *Generalized vertex algebras and relative vertex operators*, Progr. Math. 112, Birkhäuser 1993 (modules and fusion rules of lattice VOAs). [BGK17] L. Bhardwaj, D. Gaiotto, A. Kapustin, JHEP 04 (2017) 096, arXiv:1605.01640 (bosonic shadows of fermionic theories).
- [DH12] Dong–Han, Pacific J. Math. 258 (2012) 269–290; [ABD04] Abe–Buhl–Dong, Trans. AMS 356 (2004) 3391–3402; [Li99] H. Li, J. Algebra 212 (1999) 495–514; [DJX13] Dong–Jiao–Xu, Trans. AMS 365 (2013) 6441–6469; [DN99] Dong–Nagatomo, Contemp. Math. 248 (1999) 117–133 (Aut V_L).

--------------------------------------------------------------------------------------------

## 0. Summary for the formalizer

| # | statement | status | proved for SVOAs in the literature? | Lean route |
|---|---|---|---|---|
| 2.2, 2.5 | χ = √3·𝟙 (and √3·s) characteristic; P_V = e^{2πi(χ/2)(0)}; Λ_ev^*/Λ_ev ≅ ℤ₂², q = (0, ½, k/2, k/2) | [P; V] | – (lattice facts) | formalize (lattice) |
| 2.4 | V_{Λ(C)} is a nice holomorphic SVOA | [P, given T] | yes: [BK04], [HM23] §2.3, §2.7 | hypothesis |
| 2.6, 2.7 | N=1 structure; G₀² = L₀ − c/24 in every gσ-twisted sector; supertrace cancellation | [P, given T] | yes: [Li96] commutator formula | 2.7 formalizable (linear algebra) |
| 3.1 | Ramond sector V_R = V_{Λ+χ/2}, unique, parity (−1)^{⟨χ,λ⟩} | [P, given T] | yes: [Li96] Prop 5.4, [DZ05] Thm 7.7, [vE13] §12 | hypothesis |
| 3.2 | **GJF Prop 2.4, sign-exact**: ground states ↔ maximal codewords, parity = f(w), Z_RR = Index(C) | [P; V] | GJF (parity left implicit) | **formalize** (lattice combinatorics) |
| 3.3 | untwisted twined terms: 0 if −1 ∈ ⟨h⟩; ζ·(±T_h), ζ³ = 1, if ord h odd | [P, given T] | – | combinatorial part formalizable |
| 4.1 | existence and uniqueness of the σ-stable simple g-twisted module | [T] | **yes**: [DZ05] Thm 7.7 + [DRY22] Prop 3.4 | hypothesis |
| 4.3 | Majorana number ⟨χ,(1−g)χ⟩ = 6·#{s_i = −1}; Majorana layer = Π s_i | [P; V] | – | formalize |
| 4.4 | fixed-point-free g: 1 or 2 irreducibles (Majorana ⟺ Π s_i = −1), each S[g] ⊗ ℂ^d, d² = \|det(1−g)\| or half | [P, given T; V] | yes: [BK04] Thm 4.2 (integral lattices) | hypothesis + lattice lemma |
| 4.5 | vacuum energy ρ_g = ¼Σθ(1−θ) = (1/24)Σd_k(k − 1/k) | [P, given T; V] | yes: via [DZ05] (modular proof) | identity formalizable |
| 4.6 | [OI] Lemma 3.1, complete | [P, given T] | yes | hypothesis + 4.5 |
| 4.7 | [MQ] Lemma 8.3 and the x-sector of §8.5 (frame modules) | [P, given T; V] | yes: [BK04] | hypothesis |
| 4.8 | RR modular covariance; S-invariance of NS characters | [P, given T] | **yes**: [DZ05] Thms 4.12, 5.2, 7.1, 7.7 | hypothesis |
| 5.2 | V^{G×⟨σ⟩} strongly rational and V^G nice, G solvable | [P, given T] | [CM16] is for VOAs; applied to V₀̄ | hypothesis |
| 5.3 | G̃-crossed supercategory, Rep(V^{G̃}) ≅ (Rep V)^{G̃} | [T] | **yes**: [McR21] Thms 4.15, 4.17 | hypothesis |
| 5.4 | GJF Thm 4.2 for fermionic V (anomaly in S̃H³, trivialisations ↔ orbifolds) | **[T*]** | **no complete written proof** | hypothesis ORB (5.5) |
| 5.6, 5.7 | index formula (1.2) of [OI]; W = V//G is N=1 | [P, given 5.5] | – | formalize (finite sums) |

**Verdict.** Everything in (b) and (c) is either proved here or is a theorem in the literature that explicitly covers vertex operator superalgebras ([BK04], [Li96], [DZ05], [DRY22]). In (a), regularity (Thm 5.2) and the G̃-crossed structure (Thm 5.3, [McR21]) are rigorous for SVOAs. **The one folklore-level input is the fermionic part of GJF Thm 4.2** (Thm 5.4): the anomaly class in S̃H³(G), and the claim that a trivialisation produces a holomorphic SVOA W ⊃ V^G whose Ramond sector is ⊕_{[g]} V(gσ)^{C(g)}. Its rigorous ingredients exist, but their assembly is not written anywhere. Hypothesis 5.5 (ORB) isolates exactly what is used.

**Issues found**: §9. None changes a result. The main ones: the citations for uniqueness of twisted modules ([OI] §1) and for odd-lattice twisted modules ([OI] Lemma 3.1, [MQ] §8.5) point to bosonic papers, while the correct super references exist and are given here; [OI] §3.2's "unique lift of order 3" is false as stated (the conclusion survives); the status of GJF Thm 4.2 should read [T*].

--------------------------------------------------------------------------------------------

## 1. Conventions

**Definition 1.1 (VOSAs).** A VOSA V = V₀̄ ⊕ V₁̄ is ½ℤ-graded with Y(u,z) = Σ_{n∈ℤ} u_n z^{−n−1} for all u. The parity automorphism is σ := P_V = (−1)^F.
- Automorphisms are even and fix ω ([McR21] Def in §4.1), so σ is central in Aut(V).
- "Nice" = strongly rational (simple, CFT type, self-contragredient, rational, C₂-cofinite) plus positivity of twisted weights ([HM23] §2.3). "Holomorphic" = V is its only irreducible (untwisted) module.

**Definition 1.2 (g-twisted modules; NS-based convention).** For g ∈ Aut(V) of order T and v with gv = e^{−2πir/T}v, Y_M(v,z) = Σ_{n ∈ r/T + ℤ} v_n z^{−n−1}.
- This is the convention of [BK04] Def 3.1, [Li96] §2, [DZ05] §4, [DRY22] Def 2.2 and [McR21] §4.1 (whether g or g⁻¹ appears in the monodromy differs between authors; nothing below depends on it, since G is closed under inverses and ρ_g = ρ_{g⁻¹}).
- So 1-twisted modules are the NS sector and σ-twisted modules are the Ramond sector.
- **The g-twisted Ramond sector is V_{R,g} := V(gσ)**, the gσ-twisted module ([OI] §1).

**Warning 1.3.** [vE13] indexes modes by conformal weight: his "1-twisted" = Ramond = σ-twisted here, and his "σ_V-twisted" = NS = untwisted here ([vE13], end of §1). Citations of [vE13] must be translated.

**Definition 1.4 (σ-stable and Majorana objects).** Let M be an irreducible g-twisted module (g commuting with σ).
- If M ∘ σ ≅ M, then M carries a compatible ℤ₂-grading, unique up to a global shift (two gradings differ by an even automorphism commuting with Y_M, hence by ±1). This is GJF's "ordinary" object, End = ℂ.
- Otherwise M ⊕ M∘σ is the simple σ-stable ("super") object, with super-endomorphism algebra Cl(1). This is GJF's "Majorana" object ([GJF] proof of Thm 4.2; [DRY22] Lemma 3.5 and §1).

**Definition 1.5 (RR functions).** For commuting g, h and an operator ρ_g(h) on V(gσ) with ρ_g(h) Y(v,z) ρ_g(h)⁻¹ = Y(hv,z):
  Z_RR(g,h)(τ) := str_{V(gσ)} ρ_g(h) q^{L₀−c/24}.
- Since φ(σh) = (parity)·ρ_g(h) up to a scalar, this is [DZ05]'s T_{V(gσ)}(𝟙,(g,h),τ) up to a scalar. **The labels coincide**: no σ-shift is needed when citing [DZ05].

**Definition 1.6 (Frame shapes).** For g ∈ O(ℝⁿ) of finite order: det(1 − xg) = Π_k (1 − x^k)^{d_k}, η_g(τ) := Π_k η(kτ)^{d_k}, and ρ_g := ¼ Σ_j θ_j(1 − θ_j), where e^{2πiθ_j} (θ_j ∈ [0,1)) are the eigenvalues. For a signed permutation, a signed L-cycle with sign product +1 contributes (1 − x^L); with product −1 it contributes 1 + x^L = (1 − x^{2L})/(1 − x^L).

--------------------------------------------------------------------------------------------

## 2. The lattice SVOA V_{Λ(C)}

**Definition 2.1.** C ⊂ F₃ⁿ self-dual, n = 12k.
- Λ = Λ(C) := {a/√3 : a ∈ ℤⁿ, a mod 3 ∈ C}. In **a-coordinates** Λ = {a ∈ ℤⁿ : a mod 3 ∈ C} with ⟨a, b⟩ = a·b/3.
- √3ℤⁿ ⊂ Λ ⊂ (1/√3)ℤⁿ. Λ is integral since C ⊂ C^⊥, unimodular since C = C^⊥ [GJF §2], and odd since |√3e₁|² = 3.
- The frame is F := V_{√3ℤⁿ} = V_{√3ℤ}^{⊗n}. Put χ := √3·𝟙 ∈ √3ℤⁿ (a = 3·𝟙).
- A signed permutation g = (p, s) acts by g e_i = s_i e_{p(i)} (the convention of `mainq_common.mono_apply`).

**Lemma 2.2 (characteristic vectors; P_V is inner) [P; V: Part 5].**
- (a) For every sign vector s ∈ {±1}ⁿ, χ_s := √3·s is characteristic: ⟨χ_s, λ⟩ ≡ |λ|² mod 2 for all λ ∈ Λ.
- (b) t_b := e^{2πi b(0)} (b ∈ 𝔥 = Λ ⊗ ℂ) acts on M(1) ⊗ e^λ by e^{2πi⟨b,λ⟩}. So t_{χ/2} = P_V.

*Proof.*
- (a) For λ = a/√3: ⟨χ_s, λ⟩ = Σ s_i a_i ≡ Σ a_i ≡ Σ a_i² = 3|λ|² ≡ |λ|² (mod 2). The last step holds because |λ|² ∈ ℤ and 3m ≡ m (mod 2).
- (b) The parity of M(1) ⊗ e^λ is |λ|² mod 2 ([BK04] §4.1), and e^{2πi⟨χ/2,λ⟩} = (−1)^{⟨χ,λ⟩} = (−1)^{|λ|²} by (a). □

**Proposition 2.3 (lattice VOSAs) [T: Kac98 Ch. 5; BK04 Thm 4.1; HM23 §2.7].** For a positive-definite integral lattice L, V_L = M(1) ⊗ ℂ_ε[L] is a simple VOSA of CFT type and central charge rk L.
- Parity: p(e^α) = |α|² mod 2. Cocycle: ε(α,β)ε(β,α) = (−1)^{⟨α,β⟩ + |α|²|β|²}.
- Its even part is V_{L_ev}.
- For even L this is [FLM88]. **[GJF] §2 cites FLM Thm 8.10.2 for integral L; FLM treat even lattices, so the odd case should be cited to Kac98 or BK04** (minor, §9 item 8).

**Proposition 2.4 (V is nice and holomorphic) [P, given T].** V := V_{Λ(C)} is a nice SVOA and holomorphic.
- V₀̄ = V_{Λ_ev} is strongly rational: it is simple and of CFT type, self-contragredient (the contragredient of V_{L+μ} is V_{L−μ}), and regular [DLM97 Thm 3.16]. Regular plus CFT type gives rational and C₂-cofinite [Li99; ABD04].
- V₁̄ = V_{Λ_odd} is a simple current of order 2 for V_{Λ_ev} (lattice fusion rules [DL93]; [HM23] §2.7). Hence V is strongly rational ([HM23] §2.3, converse proposition, via [DH12], [ABD04]).
- Untwisted irreducible modules: V_{α+Λ}, α ∈ Λ'/Λ ([BK04] Thm 4.2 with σ = id, where Z_id = Λ'/Λ; [HM23] §2.7). Λ is unimodular, so V is holomorphic.
- Positivity: the Ramond sector has lowest weight n/24 > 0 (Prop 3.2). For g ∈ G̃ ∖ {1, σ} (Setting 5.0) g acts nontrivially on 𝔥, and its twisted modules have weights ≥ ρ_g > 0 ([BK04] Rem 4.4, Prop 4.5). This is the positivity hypothesis of [HM23] §2.3 and [DRY22].
- The Ramond sector is Prop 3.1. □

**Lemma 2.5 (the 16-fold-way class of V) [P; V: Part 6].**
- Λ_ev := {λ : |λ|² even} = ker(λ ↦ ⟨χ,λ⟩ mod 2) has index 2 in Λ, so det Λ_ev = 4.
- Λ_ev^* = Λ ∪ (Λ + χ/2) = {0, v, s, c} + Λ_ev, with representatives 0, √3e₁, χ/2, χ/2 + √3e₁. The group is ℤ₂², not ℤ₄: 2(χ/2) = χ ∈ Λ_ev since |χ|² = 3n is even.
- q(x) = |x|²/2 mod 1 = (0, ½, 3n/8, 3n/8) = **(0, ½, k/2, k/2)**. The norms are 0, 3, 3n/4 and 3n/4 + 6.
- So Rep(V₀̄) ≅ 𝒞(2_II^{−2}) for k odd (c ≡ 4 mod 8) and 𝒞(2_II^{+2}) for k even (c ≡ 0 mod 8). This agrees with [HM23] Table 1 [T: consistency check].
- V_R restricts to V₀̄ as V_{Λ_ev+χ/2} ⊕ V_{Λ_odd+χ/2} (the classes s, c), which are its even and odd parts (Prop 3.1(c)). All weights of V_R lie in n/24 + ℤ: Σ(2a_i+3)² ≡ n mod 8 (odd squares) and mod 3 (≡ wt(a mod 3) ≡ 0). Ground states can lie in either part: Golay has 24 even ones, `q8chain_len24` has 56 even and 32 odd [V: Part 2]. □

**Proposition 2.6 (N=1 structure) [P, given T: Li96 twisted Jacobi identity].** Normalise the cocycle so that ε(α,−α) = 1 for α = √3e_i (possible: ε(α,α) = (−1)^{3·4/2} = 1). Put Γ_{±,i} := e^{±√3e_i} and
  τ := (1/√3) Σ_i (Γ_{+,i} + Γ_{−,i}).
Then τ is an odd Virasoro-primary of weight 3/2, and
  τ_{(0)}τ = 2ω, τ_{(1)}τ = 0, τ_{(2)}τ = (2n/3)𝟙.
So V is an N=1 SVOA of central charge c = n. GJF's G = Γ₊ + Γ₋ is √3·τ on each factor.

*Proof.*
- One coordinate, α = √3e_i with |α|² = 3: Y(e^α,z)Y(e^{−α},w) = ε(α,−α)(z−w)^{−3}·e^0·:exp(∫α(z) − ∫α(w)): ([BK04] §4.1, the product formula for Y_α(z)Y_β(w)). So
  Γ₊(z)Γ₋(w) ~ (z−w)⁻³ + α(w)(z−w)⁻² + ½(:α²: + ∂α)(w)(z−w)⁻¹.
- Similarly Γ₋(z)Γ₊(w) ~ (z−w)⁻³ − α(w)(z−w)⁻² + ½(:α²: − ∂α)(w)(z−w)⁻¹, since ε(−α,α) = ε(α,−α)·(−1)^{−3+9} = 1.
- Γ_±Γ_± is regular because ⟨α,α⟩ = 3 > 0. Hence GG ~ 2(z−w)⁻³ + :α²:(z−w)⁻¹, and :α²: = 6T_i since T_i = :α²:/6 (α(z)α(w) ~ 3(z−w)⁻²).
- For τ_i = G_i/√3: τ_iτ_i ~ (2/3)(z−w)⁻³ + 2T_i(z−w)⁻¹.
- Different coordinates have regular OPE (⟨±√3e_i, ±√3e_j⟩ = 0) and anticommute. Summing gives the claim with c = n.
- Γ_{±,i} is Virasoro-primary of weight |α|²/2 = 3/2. □
- **In a gσ-twisted module with gτ = τ** (in particular in every V_{R,g}, g ∈ G), τ has gσ-eigenvalue −1, so its modes are τ_m with m ∈ ½ + ℤ. Put G_r := τ_{r+½} (r ∈ ℤ). The twisted commutator formula [Li96 (M4); BK04 Rem 3.1] gives
  [τ_m, τ_{m'}]₊ = Σ_j C(m, j)(τ_{(j)}τ)_{m+m'−j} = 2L_{r+r'} + (2c/3)·C(r+½, 2)·δ_{r+r',0},
  i.e. {G_r, G_{r'}} = 2L_{r+r'} + (c/3)(r² − ¼)δ_{r+r',0}. In particular **G₀² = L₀ − c/24**. [P, given T]

**Lemma 2.7 (supertrace cancellation) [P].** Let M = ⊕_μ M_μ be a super vector space graded by L₀ with finite-dimensional eigenspaces. Let G₀ be odd with G₀² = L₀ − c/24, and φ an operator commuting with L₀ and G₀. Then str_M φ q^{L₀−c/24} = str_{M_{c/24}} φ.
- If φ is odd, every supertrace vanishes.
- If φ is even and μ ≠ c/24: G₀ is invertible on M_μ and swaps its parity components. From G₀φ₀ = φ₁G₀ we get φ₁ = G₀φ₀G₀⁻¹, so tr φ₁ = tr φ₀. □
- *Lean.* Pure linear algebra on finite-dimensional ℤ₂-graded spaces, ≈ 60–100 lines.

--------------------------------------------------------------------------------------------

## 3. The Ramond sector and GJF Prop 2.4

**Proposition 3.1 (the Ramond sector) [P, given T: Li96 Prop 5.4; DZ05 Thm 7.7; vE13 §12].** Let Λ be odd unimodular and χ characteristic. With
  Δ(h,z) := z^{h(0)} exp(Σ_{n≥1} h(n)(−z)^{−n}/(−n)),
put Y_R(v,z) := Y(Δ(χ/2,z)v, z) on the space V_Λ. Then:
- (a) (V_Λ, Y_R) is a σ-twisted module. This is [Li96] Prop 5.4 (proved for VOSAs) with σ_h = e^{2πi(χ/2)(0)} = P_V (Lemma 2.2); h = χ/2 is even, of weight one, primary, and h(0) is semisimple with spectrum in ½ℤ.
- (b) Y_R(α_{−1}𝟙, z) = α(z) + ⟨χ/2,α⟩z⁻¹, so the Heisenberg zero modes act on e^λ by ⟨λ + χ/2, ·⟩, and L₀ acts on e^λ by |λ + χ/2|²/2 ([vE13] §12, formula for L^δ). As a Heisenberg module, **V_R = ⊕_{λ∈Λ} M(1, λ + χ/2) = V_{Λ+χ/2}**.
- (c) It is irreducible (Δ(−χ/2, z) inverts the construction and preserves submodules), and σ-stable: P_R := e^{πiχ(0)} acts by (−1)^{⟨χ,λ⟩} on M(1)⊗e^λ, commutes with Δ(χ/2,z), and satisfies P_R Y_R(v,z) P_R⁻¹ = Y_R(σv, z). **So the Ramond parity is (−1)^{⟨χ,λ⟩}, unique up to one global sign** (Def 1.4). This is GJF's convention.
- (d) It is the unique σ-stable irreducible σ-twisted module: [DZ05] Thm 7.7 (V holomorphic and C₂-cofinite, Prop 2.4), or directly, since Δ is a bijection between untwisted and σ-twisted modules and the untwisted module is unique (Prop 2.4).
- (e) Another characteristic vector χ' = χ + 2μ (μ ∈ Λ) gives an isomorphic module (translate by e^μ). The parity labels change by the global sign (−1)^{|μ|²}. [P] □

**Proposition 3.2 (GJF Prop 2.4, sign-exact) [P; V: Parts 1–2].** Let n be even (always true here, n = 12k) and χ = √3·𝟙. For a maximal codeword w put ν_w := ι(w)/(2√3), where ι: F₃ → {0, 1, −1}.
- (a) min_{ν ∈ Λ+χ/2} |ν|²/2 = n/24. The minimisers are exactly the ν_w, w ∈ C maximal, each attained by a unique vector.
- (b) The ground-state space of V_R (weight c/24) is ⊕_w ℂ·e^{λ_w} with λ_w := ν_w − χ/2, and **the parity of e^{λ_w} is (−1)^{⟨χ,λ_w⟩} = f(w)**, GJF's evenness (f = Πφ, φ(0,1,2) = (0,−1,+1)).
- (c) **Z_RR(V_{Λ(C)}) = str_{V_R} q^{L₀−c/24} = Index(C) = Σ_{x∈C} f(x)**, exactly.
- (d) (GJF Rem 2.5) η^n·Z_RR = Σ_λ (−1)^{⟨χ,λ⟩} q^{|λ+χ/2|²/2} = CWE_C(θ₀, θ₁, θ₂), where θ₀ = 0, θ₁ = η, θ₂ = −η.

*Proof.*
- (a) In a-coordinates ν = (a + (3/2)𝟙)/√3 with a mod 3 ∈ C, so |ν|²/2 = Σ_i (2a_i + 3)²/24.
  - Over a ≡ r (mod 3): min (2a+3)² = 9 for r = 0 (at a ∈ {0, −3}); = 1 for r = 1 (only at a = −2); = 1 for r = 2 (only at a = −1).
  - Hence Σ(2a_i + 3)² ≥ n + 8·#{i : a_i ≡ 0}, with equality iff every a_i ∈ {−1, −2}.
  - Such a has a mod 3 =: w' maximal, and 2a + 3 = −ι(w'), i.e. ν = ι(−w')/(2√3) = ν_{−w'}. Since C = −C, w := −w' runs over all maximal codewords.
- (b) The weight-c/24 space of M(1, ν) is ℂe^λ. The parity is (−1)^{⟨χ,λ⟩} with ⟨χ,λ⟩ = Σ a_i ≡ #{a_i = −1} = #{w'_i = 2} = #{w_i = 1} (mod 2). So the parity is (−1)^{#1s(w)} = f(w) = f(−w) (n even).
- (c) Lemma 2.7 with φ = 1 and Prop 2.6, then (b).
- (d) Per coordinate, Σ_{a≡r} (−1)^a q^{(2a+3)²/24} = θ_r. The cancellation a ↔ −3 − a gives θ₀ = 0; Euler's pentagonal identity gives θ₁ = η and θ₂ = −η. □
- **Sign bookkeeping.** GJF write λ + χ/2 = ι(w)/(2√3) with w "a maximal codeword" and leave the parity implicit. The lattice vector λ_w reduces to the codeword −w, and the parity equals the GJF-evenness of both w and −w. So with χ = √3𝟙 and the parity of Prop 3.1(c) **there is no sign ambiguity**: Z_RR = +Index(C).
- [V: Part 1] (d) as q-series through q^{n/24+3}, computed by direct per-coordinate lattice sums (no Euler identity), for tetracode³, 4E₃⁺, Golay (n = 12) and `q8chain_len24` (n = 24): Index·ηⁿ = 0, 0, 24ηⁿ, 24ηⁿ. [V: Part 2] (a)–(b) on every maximal codeword of Golay (24 words, 24 even) and `q8chain_len24` (88 words: 56 even, 32 odd, Index 24).
- *Lean.* (a)–(c) at the lattice level are elementary: a per-coordinate lemma (`decide` on residues plus (2a+3)² ≥ 1), a bijection {minimal a} ≃ {maximal codewords}, and a parity lemma matching `GJF.f` / `gjfIndex`. ≈ 200–350 lines. (d) needs Euler's pentagonal theorem and is not needed if (c) is used with Lemma 2.7.

**Proposition 3.3 (the untwisted twined terms, [OI] §1.3 and §3.2) [P, given T: GJF Thm 3.1; BK04 Prop 4.1; Li96 Prop 5.4; V: Part 2].** Let h ∈ Aut(C) with its lift ĥ from GJF Thm 3.1, and let φ be any operator on V_R with φY_R(v,z)φ⁻¹ = Y_R(ĥv,z).
- (i) **φ maps e^{λ_w} to a multiple of e^{λ_{hw}}.** By Prop 3.1(b), φ conjugates the Heisenberg zero modes by h, so it maps the momentum-ν eigenspace to the momentum-hν one. Also hν_w = ν_{hw}, since ι commutes with signed permutations. Each ground-state momentum space is one-dimensional.
- (ii) **If some power of h is −1, then str_{ground} φ = 0**, so Z_RR(1,h) = 0 for every normalisation: a fixed maximal w would satisfy w = −w.
- (iii) **If ord h is odd**:
  - Every signed cycle of h has sign product +1. A cycle with product −1 has order 2L, which is even.
  - Writing h = (p, s), there is a sign vector t with ht = t (t_{p(i)} = s_i t_i along each cycle; solvable because each cycle has sign product +1), and χ' := √3·t is characteristic (Lemma 2.2) and h-fixed.
  - Build V_R from χ' (Prop 3.1(e)). Then ĥ commutes with Δ(χ'/2, z), because ĥ h₀(m) ĥ⁻¹ = (hh₀)(m) = h₀(m) for h₀ = χ'/2. So **ĥ itself** is an admissible φ.
  - GJF's lift lies in Λ̂[2].Aut(C), whose elements act by e^λ ↦ ±e^{gλ} for a ±1-valued cocycle ([BK04] Prop 4.1; [GJF] §3). So on an h-fixed ground state ĥe^λ = u(λ)e^λ with u(λ) = ±1, and ĥ³ = 1 forces u(λ) = 1.
  - Every other admissible φ is ζĥ (Schur); normalised to φ³ = 1, ζ³ = 1.
  - Hence **Z_RR(1,h) = ζ·ε·T_h** with ε = ±1 (the global sign of Prop 3.1(e)) and T_h := Σ_{x∈C, hx=x} f(x). It vanishes iff T_h = 0.
- [V: Part 2] For h = g⁴ on `z12seed_len36_3`: the h-fixed sign vector exists, χ' is characteristic, and the χ'-parity equals the χ-parity on all 16 h-fixed maximal words (one global sign). T_h = 0. On `q8chain_len24`, J and K act equivariantly on the 88 ground states and J fixes none.
- **Correction to [OI] §3.2** (§9 item 3): an element of order 3 does *not* have a unique lift of order 3 in Λ̂[2].Aut(C) (only unique up to Λ̂[2]-conjugacy, by Schur–Zassenhaus). Moreover, the action on V_R carries a scalar ζ fixed by the trivialisation. The conclusion Z_RR(1,h) = 0 for T_h = 0 is unaffected. GJF's proof of Thm 5.6 ("no sign ambiguity") has the same imprecision.

--------------------------------------------------------------------------------------------

## 4. Twisted modules of V_{Λ(C)}

**Theorem 4.1 (existence and uniqueness; super) [T: DZ05 Thm 7.7, DRY22 Prop 3.4; bosonic analogue DLM00 Thm 10.3].** Let V be nice and holomorphic (V_{Λ(C)} by Prop 2.4, or an orbifold W as in 5.5). For every automorphism g of finite order there is a unique σ-stable simple g-twisted module V(g). It is either ordinary or Majorana (Def 1.4).
- The g-rationality that [DZ05] needs comes from [DRY22] Prop 3.4 (self-dual, regular VOSA of CFT type).
- [DZ05]'s uniqueness is for σ-stable ("super") simple modules. In the Majorana case there are two non-isomorphic irreducible g-twisted modules M, M∘σ ([DRY22] §1: "quantum dimensions 1/√2"). Both statements are the super version of [DLM00] Thm 10.3, which is for VOAs only.

**Lemma 4.2 (all lifts of a fixed-point-free g are conjugate; ĝ ~ ĝP_V) [P; V: Part 5].** Let g ∈ O(Λ) have no nonzero fixed vector, and let ĝ, ĝ' ∈ Λ̂.O(Λ) lie over g.
- ĝ' = t_b ĝ with t_b ∈ Λ̂ = Hom(Λ, U(1)) = {t_b : b ∈ 𝔥}, and t_a ĝ t_a⁻¹ = ĝ t_{(g⁻¹−1)a} (check on e^λ, using ⟨a, gλ⟩ = ⟨g⁻¹a, λ⟩).
- Since 1 − g is invertible on 𝔥, a := (g⁻¹ − 1)⁻¹b conjugates ĝ to ĝ'. With b = χ/2: **ĝP_V is conjugate to ĝ**, and V(ĝP_V) = V(ĝ) ∘ Ad(t_a) has the same L₀ (t_a fixes ω).
- This is [OI] Lemma 3.1's first step. [V: Part 5] solves (g⁻¹ − 1)a = χ/2 exactly for −1 (Golay), J (`q8chain_len24`), g and g² (`z12seed_len36_3`). □

**Lemma 4.3 (the Majorana layer of a signed permutation) [P; V: Part 4].** For g = (p, s) ∈ Aut(C) acting on Λ(C):
  ⟨χ, (1−g)χ⟩ = 6·#{i : s_i = −1}.
- Hence ⟨χ,(1−g)χ⟩ ∈ 4ℤ iff ε(g) := Π_i s_i = +1. By [GJF] Ex 4.4 **the Majorana layer of g is the character ε: 2ⁿ:Sₙ → ±1**.
- *Proof.* gχ = √3 Σ_i s_i e_{p(i)}, so ⟨χ, gχ⟩ = 3Σ_i s_i = 3(n − 2#{s_i = −1}), and ⟨χ,χ⟩ = 3n. □
- For the groups used, ε = 1:
  - −1: n is even;
  - J, K on the Q₈-chains: one negative sign per 2-cycle, so n/2 = 6k negatives;
  - g of order 12 on the ℤ/12-chains: one negative per 6-cycle, so n/6 = 2k negatives;
  - elements of odd order: always.
- (In [GJF]'s proof of Thm 5.6 the per-block contribution "3(m/2) − 2×odd" should be 6×odd; the conclusion is unaffected. §9 item 8.)

**Proposition 4.4 (fixed-point-free twisted modules of odd unimodular lattice SVOAs) [P, given T: BK04 Thm 4.2, Def 4.1, Def 4.2, Rem 4.4; V: Part 4].** Let Λ be positive-definite, odd and unimodular, g ∈ O(Λ) of finite order with no nonzero fixed vector, and ĝ any lift.
- (a) **The number of irreducible ĝ-twisted modules is |Z_g| = 1 if ⟨χ,(1−g)χ⟩ ≡ 0 (mod 4), and 2 if ≡ 2 (mod 4).** In the second case the two are M and M∘σ (Majorana). The same holds for ĝP_V (Lemma 4.2).
- (b) Each irreducible is, as a module over the twisted Heisenberg algebra, S(𝔥̂_g⁺) ⊗ ℂ^d with **d² = |det(1−g)|/|Z_g|**. In the ordinary case, V(ĝ) = S[g] ⊗ T_g with dim T_g = |det(1−g)|^{1/2} = Π_k k^{d_k/2}, all of T_g in the lowest weight.

*Proof.*
- (a) [BK04] Lemma 4.4 and Def 4.1: P_g = {λ ∈ Λ_ev^* : (1−g)λ ∈ Λ, and λ ∈ Λ^* if (1−g)λ ∈ Λ_ev}, Z_g = P_g/Λ. Here Λ^* = Λ and Λ_ev^* = Λ ∪ (Λ + χ/2) (Lemma 2.5), so Λ ⊂ P_g ⊂ Λ ∪ (Λ + χ/2).
  - For λ = χ/2 + μ, μ ∈ Λ, put α₀ := (1−g)χ/2. It lies in Λ because gχ is characteristic, and two characteristic vectors of a unimodular lattice differ by 2Λ.
  - So (1−g)λ = α₀ + (1−g)μ ∈ Λ always, and |(1−g)λ|² ≡ |α₀|² (mod 2):
    - the cross term 2⟨α₀, (1−g)μ⟩ is even;
    - |(1−g)μ|² ≡ ⟨χ, (1−g)μ⟩ = 2⟨(1−g⁻¹)χ/2, μ⟩ is even.
  - And |α₀|² = ¼(2|χ|² − 2⟨χ,gχ⟩) = ½⟨χ,(1−g)χ⟩.
  - So χ/2 + μ ∈ P_g iff (1−g)λ ∉ Λ_ev iff ½⟨χ,(1−g)χ⟩ is odd. The count follows from [BK04] Thm 4.2.
  - In the Majorana case both irreducibles cannot be σ-stable, by the uniqueness in Thm 4.1. So they are exchanged by σ.
- (b) [BK04] Rem 4.4 with 𝔥₀ = 0, and the defect d² = |Λ/(1−g)P_g| ([BK04] equation before Def 4.2). 1 − g is injective, so |Λ/(1−g)P_g| = |Λ/(1−g)Λ| / |P_g/Λ| = |det(1−g)|/|Z_g|. Finally |det(1−g)| = Π_k k^{d_k}, from det(1 − xg) = Π(1−x^k)^{d_k} at x = 1 with Σd_k = 0. □
- [V: Part 4] BK's P_g/Λ and d² are computed from their definition by enumerating (1−g)⁻¹Λ/Λ (Hermite normal form):
  - ℤ^m with −1 (m = 1..4); the 90° rotation of ℤ²;
  - all 27 fixed-point-free automorphisms of Λ(tetracode) ≅ ℤ⁴ (12 of them, the order-8 elements, are Majorana, with Π s_i = −1);
  - Λ(Golay) with −1; Λ(`q8chain_len24`) with J and JK; Λ(`z12seed_len36_3`) with g of order 12.
  - In every case |Z_g| is as predicted by (a) and d² = |det(1−g)|/|Z_g|.
- The literature for (a)–(b) in the super case is **[BK04]** (integral lattices, vertex superalgebras). [Lep85], [DL96] and [FLM88] treat even lattices only.

**Proposition 4.5 (vacuum energy) [P, given T; V: Part 3].** In the ordinary case of Prop 4.4, V(ĝ) and V(ĝP_V) have lowest L₀-weight
  **ρ_g = ¼Σ_j θ_j(1−θ_j) = (1/24) Σ_k d_k (k − 1/k)**,
and ch V(ĝ) = |det(1−g)|^{1/2} Π_k η(τ/k)^{−d_k}.
- *Identity.* The two expressions agree for every orthogonal g of finite order. Both are additive over the Frame-shape decomposition, and for the k-th roots of unity Σ_{j<k} (j/k)(1 − j/k) = (k² − 1)/(6k). [P; V: Part 3, 400 random signed permutations and the element types used]
- *Proof 1 (lattice)* [T]. The weight of the vacuum of the twisted Fock space. It depends only on the g-twisted module of the Heisenberg VOA M(1) (bosonic), so the even-lattice computation [Lep85; DL96] applies verbatim; for θ = −1 this is FLM's 1/16 per dimension.
- *Proof 2 (modular; needs no explicit constant)* [P, given T: DZ05 Thms 4.12, 7.1, 7.7].
  - Z_NS(1,ĝ) := tr_V ĝ q^{L₀−c/24} = 1/η_g(τ): only λ = 0 contributes, since gλ ≠ λ, and the Fock trace is Π_m det(1 − q^m g)⁻¹.
  - In [DZ05]'s labels this is T_V(𝟙,(σ, σĝ)) ∈ 𝒞(σ, σĝ). S maps it into 𝒞(σĝ, σ), which is spanned by ch V(ĝ) (Thm 7.1 and uniqueness, Thm 4.1). So ch V(ĝ)(τ) = c·(1/η_g)(−1/τ) with c ≠ 0.
  - η(−1/τ) = √(−iτ)η(τ) and Σ_k d_k = 0 give (1/η_g)(−1/τ) = |det(1−g)|^{1/2} Π_k η(τ/k)^{−d_k}. Its leading exponent is −Σ_k d_k/(24k) = ρ_g − n/24, using n = Σ k d_k.
  - ch V(ĝ) has nonnegative coefficients and a positive leading one, so the lowest weight is ρ_g. The dimension of the lowest-weight space (Prop 4.4) gives c = 1.
- [V: Part 3] The S-transform identity, numerically to 10⁻¹⁴, and the leading exponent, exactly: for −1 (ρ = n/16), J and JK (3n/64), −h (19n/432), g of order 12 (73n/1728), g² and g³.

**Corollary 4.6 ([OI] Lemma 3.1, completed) [P, given T].** For G as in [OI] Theorem O and g ∈ G of even order:
- V_{R,g} = V(gσ) is the unique σ-stable simple gσ-twisted module (Thm 4.1). It is ordinary, since ε(g) = 1 (Lemma 4.3).
- Its lowest weight is ρ_g (Lemma 4.2 and Prop 4.5).
- Its N=1 modes satisfy G₀² = L₀ − c/24 (Prop 2.6).
- So ρ_g > n/24 ⇒ Z_RR(g,h) = 0 for all h ∈ C(g) (Lemma 2.7). [OI] Lemma 3.3 checks ρ_g > n/24.
- This replaces [OI]'s references (Lepowsky, Dong–Lepowsky: even lattices) by [BK04], [Li96] and [DZ05], which cover SVOAs.

**Proposition 4.7 ([MQ] Lemma 8.3 and the x-sector of [MQ] §8.5) [P, given T: BK04 Thm 4.2, Rem 4.4; GJF Thm 3.1; V: Part 4].**
- (a) **Frame, θ = −1.** For Q = √3ℤⁿ and σ = −1: P_σ = Q when n is even.
  - For λ ∈ Q_ev^* = (1/√3)(ℤⁿ ∪ ℤⁿ + ½𝟙) with 2λ ∈ Q, either λ ∈ Q, or λ = (√3/2)y with y all odd.
  - In the second case 2λ ∈ Q_ev (|√3y|² = 3Σy_i² ≡ n ≡ 0 mod 2) but λ ∉ Q^* = (1/√3)ℤⁿ, so λ ∉ P_σ.
  - So F has a **unique irreducible θ-twisted module S[θ] ⊗ T with dim T = |Q/2Q|^{1/2} = 2^{n/2}**, ordinary.
  - T is the graded spinor module of Cl(n), generated by the odd zero modes γ_i of √3e_i. By the commutator formula for C_{α,β} in [BK04] §4.3, γ_iγ_j = −γ_jγ_i for i ≠ j, since (−1)^{|α|²|β|²} = −1 and ⟨α,β⟩ = 0.
  - (For n odd: |Z| = 2, Majorana; n = 1 is the single Cl(1) of [MQ] §8.3.)
- (b) **The (−1)-sector of V_{Λ(C)} is this module.**
  - GJF's lift of −1 restricts to θ^{⊗n} on F (GJF Thm 3.1).
  - θ-twisted F-modules are semisimple ([BK04] Thm 4.2), so V_{−1}|_F ≅ (S[θ] ⊗ T)^{⊕m}.
  - The lowest-weight spaces both have dimension 2^{n/2}: Prop 4.4 with |det(1 − (−1))| = 2ⁿ and ε(−1) = 1. So m = 1.
  - Hence **T = S_n, the spinor module of Cl(n)**, and V_{−1} with its projective Q₈-action depends only on the frame. This is [MQ] Lemma 8.3; "same character" there should read "semisimplicity plus this dimension count".
- (c) **J-type x** (x² = −1, n/2 signed 2-cycles each with one negative sign).
  - On the frame: Q/(1−x)Q ≅ (ℤ/2)^{n/2}, generated by one √3e_i per 2-cycle. These anticommute pairwise ([BK04] commutator with (x^kα|β) = 0), so |Z| = 1 and **T_x(F) = spinor module of Cl(n/2), dim 2^{n/4}**.
  - On Λ(C): ε(x) = 1 and |det(1−x)| = 2^{n/2}, so dim T_x = 2^{n/4} (Prop 4.4), and V(x)|_F ≅ S[x] ⊗ T_x(F).
  - This is the structure [MQ] §8.5 uses, **with [BK04] in place of [BDM02]**, which treats unsigned cyclic permutations of tensor powers of VOAs.
- [V: Part 4] Frame θ for n = 1, 2, 3, 4, 8, 12: |Z| = 1, d² = 2ⁿ for n even, and |Z| = 2, d² = 2^{n−1} for n odd. Frame J-type x for n = 4, 12, 24: |Z| = 1, d² = 2^{n/2}.

**Proposition 4.8 (modular covariance in the RR sector; S-invariance of NS characters) [P, given T: DZ05 Thms 4.12, 5.2, 7.1, 7.7; DRY22 Prop 3.4].** Let V be nice and holomorphic, and g, h ∈ Aut(V) commuting of finite order.
- (a) In the ordinary case (Def 1.4), Z_RR(g,h) (Def 1.5) lies in 𝒞(g,h) ([DZ05] Thm 5.2: V(gσ) is simple, and h- and σ-stable by uniqueness). For γ = (a b; c d) ∈ SL₂(ℤ), Z_RR(g,h)(γτ) is the v = 𝟙 value of an element of 𝒞(g^a h^c, g^b h^d) ([DZ05] Thm 4.12).
- (b) If ⟨g,h⟩ is cyclic, 𝒞(g,h) is one-dimensional, spanned by the trace function of V(σg) ([DZ05] Thm 7.7). Hence Z_RR(g,h)(γτ) = c_γ·Z_RR((g,h)γ)(τ), and **Z_RR((g,h)γ) ≡ 0 ⇒ Z_RR(g,h) ≡ 0**. This is exactly what [OI] §3.3–3.4 use (there ⟨g,h⟩ is cyclic by [OI] Lemma 2.1(a)), and the modular action on labels is the plain (g,h) ↦ (g^a h^c, g^b h^d).
- (c) **ch W(−1/τ) = ch W(τ) for every nice holomorphic SVOA W** ([MQ] Prop 8.5.2).
  - ch W = T_W(𝟙,(σ,σ)) ∈ 𝒞(σ,σ), and S maps 𝒞(σ,σ) to 𝒞(σ,σ⁻¹) = 𝒞(σ,σ). This space is one-dimensional ((b), with ⟨σ⟩ cyclic).
  - So ch W(−1/τ) = c·ch W(τ). At the S-fixed point τ = i, ch W(i) > 0, so c = 1. □
- [vE13] Thm 1.3 gives the same with "odd traces" added, in his Ramond-based labels (Warning 1.3).

--------------------------------------------------------------------------------------------

## 5. The orbifold hypotheses (GJF Thm 4.2) in the super setting

**Setting 5.0.** V = V_{Λ(C)}, and G ⊂ Aut(C) one of the Main Question groups (1, ⟨−1⟩, ⟨J⟩, ℤ/3, ℤ/6, ℤ/12, Q₈, Q₈ × ℤ/3), lifted by GJF Thm 3.1. The lift acts on F by signed permutations, with the reflection lift Γ_{+√3} ↔ Γ_{−√3}, so **G fixes τ, hence ω** (Prop 2.6). All these G are solvable.

**Lemma 5.1 [P].**
- (i) G → Aut(V) is injective, because g acts on 𝔥 as g.
- (ii) G ∩ ⟨σ⟩ = 1, because στ = −τ. σ is central, so G̃ := G × ⟨σ⟩ ⊂ Aut(V).
- (iii) G acts faithfully on V₀̄.
  - If g|_{V₀̄} = 1, then g acts on the irreducible V₀̄-module V₁̄ ([HM23] §2.3) by a scalar c.
  - Since V₁̄·V₁̄ spans a nonzero part of V₀̄ (V simple), c² = 1, so g ∈ {1, σ}.
  - gτ = τ forces g = 1.
- (iv) U := V^{G̃} = (V₀̄)^G is a VOA. □

**Theorem 5.2 (regularity; the super version of GJF's remark after Thm 4.2) [P, given T: CM16 Cor 5.25; Li99; ABD04; Hua08; HM23 §2.3; DRY22 Thm 6.3; DJX13].** For G solvable:
- (a) **U = V^{G̃} is strongly rational** and Rep(U) is a modular tensor category.
- (b) V^G is a nice SVOA (in particular regular, as GJF Thm 4.2 assumes).

*Proof.*
- (a) V₀̄ is simple, regular, of CFT type and self-dual (Prop 2.4), and G acts faithfully (Lemma 5.1(iii)) and is solvable. [CM16] Cor 5.25, **a theorem about VOAs, applied to the VOA V₀̄**, gives U simple, regular, with L₀ ≥ 0, and self-dual.
  - U₀ ⊂ (V₀̄)₀ = ℂ𝟙, so U has CFT type. Regular plus CFT type gives rational and C₂-cofinite [Li99; ABD04].
  - Modularity is [Hua08].
- (b) V^G = U ⊕ U₁ with U₁ := (V₁̄)^G ∋ τ.
  - Schur–Weyl duality (the super version is [McR21]'s citation [McR, Thm 3.2]) gives V = ⊕_{χ∈Irr G̃} W_χ ⊗ V_χ with pairwise distinct irreducible U-modules V_χ, and U₁ = V_{1⊠sgn}.
  - qdim_U V_χ = dim W_χ ([DRY22] Thm 6.3), so qdim U₁ = 1 and U₁ is a simple current [DJX13].
  - The restriction of Y to U₁ ⊗ U₁ → U is a nonzero intertwining operator, so U₁ ⊠ U₁ ≅ U.
  - [HM23] §2.3 (converse proposition: even part strongly rational and odd part a simple current of order 2, via [DH12], [ABD04]) gives V^G nice. □
- **Which regularity is needed.** [DRY22], [DZ05] and [McR21] need (a), not (b). GJF's hypothesis "V^G regular" for fermionic V is best read as (a). GJF's parenthetical ("the fermionic case follows immediately by passing to the bosonic subalgebra") is (a); the step is exactly [CM16] applied to V₀̄.

**Theorem 5.3 (twisted sectors form a G̃-crossed supercategory) [T: McR21 Thm 4.15, Thm 4.17; DRY22 Thm 5.6].** Under Thm 5.2(a), let 𝒞 be the category of grading-restricted U-modules. It has Huang–Lepowsky–Zhang vertex tensor structure because U is strongly rational, and it contains V, a finite sum of irreducible U-modules. Then:
- (i) every indecomposable object of Rep V (U-modules with unital associative V-action) is a g-twisted V-module for some g ∈ G̃;
- (ii) Rep V is a braided G̃-crossed supercategory;
- (iii) induction 𝒞 → (Rep V)^{G̃} is a braided tensor equivalence;
- (iv) every irreducible U-module occurs in an irreducible g-twisted V-module ([DRY22] Thm 5.6).
- Rep V is semisimple [P, given T]: 𝒞 is semisimple and rigid, and V is haploid with nonzero categorical dimension ([KO02] Thm 3.3, as in [McR21] proof of Thm 4.20).
- Each component Rep(V, g), g ∈ G̃, has exactly one simple object up to (possibly odd) isomorphism (Thm 4.1). In the component g ∈ G it is V(g) (the NS twisted sector); in gσ it is V_{R,g}.
- **[McR21] states (i)–(iii) for vertex operator superalgebras with G̃ ∋ P_V; this is rigorous in the super case.**

**Theorem 5.4 (GJF Thm 4.2, fermionic) [T*].** Statement ([GJF] Thm 4.2): for holomorphic V (possibly fermionic), G finite acting faithfully with V^G regular, there is an anomaly α ∈ S̃H³(G), and each trivialisation determines an orbifold V//G.
- *What is rigorous.*
  - The G-graded super fusion category ⊕_{g∈G} Rep(V,g) with invertible components (Thm 5.3, Thm 4.1).
  - The equivalence Rep(U) ≅ (Rep V)^{G̃} (Thm 5.3).
  - The dictionary between commutative superalgebras in Rep(U) and VOSA extensions of U ([HKL15] Thm 3.2; [CKL20] Thm 3.13; [CKM24]).
  - The bosonic analogue (Rep(V^G) ≅ 𝒵(Vec_G^α) for holomorphic VOAs) is a theorem: [DNR25]; also [Kir02], [Mü04], [McR21].
- *What is not written anywhere (folklore).*
  - (1) The identification of the monoidal functor G → {⊠-invertible supercategories} with a class α ∈ S̃H³(G) ([GJF]: "replace category with supercategory"; categorical background [BGK17], [JFR]).
  - (2) The statement that a trivialisation yields a Lagrangian superalgebra in (Rep V)^{G̃} whose VOSA W is holomorphic, with W_R = ⊕_{[g]} V(gσ)^{C(g)} (as in [GJF] §5's formula for Z_RR(V//G)).
- [MQ] §8.2 already says that GJF Thm 4.2 "is at the same level" as the gauging lemma. **In [OI] and [MQ] it is labelled [T]; it should be [T*].**
- A possible bosonic reduction for k even (c ≡ 0 mod 8, so V has bosonic neighbours V_{Λ^±}) is [H] and is not pursued here. It needs G to act on V_R, i.e. control of the Gu–Wen layer.

**Hypothesis 5.5 (ORB(C, G): what is used from Thm 5.4).** Let (C, G) be as in 5.0 with α = 0, and fix a trivialisation. Then there is W = V//G with:
- (O1) W is a nice holomorphic SVOA containing V^G as a sub-VOSA with the same conformal vector;
- (O2) W_R ≅ ⊕_{[g]} V(gσ)^{C(g)} as ℤ₂- and L₀-graded spaces. Here C(g) acts on V(gσ) by a **genuine** representation ρ_g by even operators with ρ_g(h)Y(v,z)ρ_g(h)⁻¹ = Y(hv,z), and the parities of the V(gσ) are fixed by the trivialisation;
- (O3) Z_RR(g,h) = Z_RR(xgx⁻¹, xhx⁻¹) for these ρ's (conjugation compatibility).
- *Remark.* The anomaly statements ([MQ] Thm 8.1 and §8.4–8.5; GJF Ex 4.4) are a separate component. ORB is conditional on α = 0.

**Proposition 5.6 ([OI] (1.2), the index formula) [P, given 5.5].** Index(W) := str_{W_R} q^{L₀−c/24} = (1/|G|) Σ_{gh=hg} Z_RR(g,h).
- For a genuine representation ρ of a finite group C by even operators on a graded super space E, e := (1/|C|)Σ_h ρ(h) is an even projector onto E^C. So str(q^{L₀}|_{E^C}) = (1/|C|)Σ_h str(ρ(h)q^{L₀}).
- Summing over classes and using (O3) gives Σ_{[g]} 1/|C(g)| Σ_{h∈C(g)} = (1/|G|) Σ_{commuting}. [V: `mainq_orbifold_index.py` Part 1]
- The result is a constant by Lemma 2.7, applied in W: τ ∈ W and G₀² = L₀ − c/24 on W_R. □

**Proposition 5.7 (W = V//G is a holomorphic N=1 SVOA) [P, given 5.5].**
- τ ∈ V^G ⊂ W, since G fixes τ.
- The vertex operators of the sub-VOSA V^G are the restrictions of those of W, and ω_W = ω (O1). So τ_{(0)}τ = 2ω_W, τ_{(1)}τ = 0, τ_{(2)}τ = (2c/3)𝟙 hold in W, and τ is ω_W-primary of weight 3/2 (Prop 2.6).
- W is holomorphic by (O1), and its RR index is Prop 5.6. □

--------------------------------------------------------------------------------------------

## 6. What each residue class uses

| k mod 24 | G ([MQ] §6) | foundations used |
|---|---|---|
| gcd 1 | 1 (W = V) | 2.4, 2.6, 2.7, 3.1, **3.2** |
| gcd 2 | ⟨−1⟩ | + 4.1–4.6 (ρ = n/16), 3.3(ii), 5.2–5.7 |
| gcd 4 | ⟨J⟩, J² = −1 | same (ρ_J = 3n/64) |
| gcd 3, 6, 12 | ℤ/3, ℤ/6, ℤ/12 | + 3.3(iii) (T_h = 0, [MQ] Lemma 4.3), **4.8(a)–(b)** ([OI] §3.3–3.4) |
| gcd 8 | Q₈ | as gcd 4, with non-cyclic ORB; no modular transformation ([OI] §3.5) |
| gcd 24 | Q₈ × ℤ/3 | everything |

The anomaly input (non-anomaly of G: GJF Thm 5.6's Frame-shape computation, [MQ] Thm 8.1 for Q₈) is outside this file. It uses Prop 4.4 (structure of the (−1)- and x-sectors, via 4.7) and Prop 4.8(c) (in [MQ] §8.5).

--------------------------------------------------------------------------------------------

## 7. Lean plan and size estimate for this component [H]

The VOA side cannot be stated in current Mathlib: to our knowledge it has at most basic vertex-operator definitions, and no VOSAs with modules, lattice VOSAs, twisted modules or modular invariance (not re-checked in this container, which has no Mathlib checkout). The plan is to formalize the lattice and combinatorial content and take the VOA theorems as a named hypothesis structure.

| item | content | lines |
|---|---|---|
| L1 | Λ(C) in a-coordinates as a ℤ-submodule with ⟨a,b⟩ = a·b/3; integrality; characteristic vectors (Lemma 2.2); Λ_ev and Lemma 2.5 | 200–350 |
| L2 | Prop 3.2 (a)–(c): minimal vectors of Λ + χ/2 ↔ maximal codewords, parity = f(w), signed count = `gjfIndex` (reuses [Lean] `f`, `phi`, `gjfIndex`) | 200–350 |
| L3 | Prop 3.3 combinatorics: −1 fixes no maximal word; h-fixed sign vector for odd-order signed permutations; T_h as a `Finset` sum | 150–250 |
| L4 | Frame shapes of signed permutations, det(1 − xg) = Π(1−x^k)^{d_k}, ρ_g identity (Prop 4.5), Majorana number (Lemma 4.3), and the table ρ_g > n/24 of [OI] Lemma 3.3 | 400–700 |
| L5 | Prop 4.4(a) as a lattice statement (characteristic vectors mod 2Λ; the parity of \|(1−g)λ\|²) | 200–400 |
| L6 | Lemma 2.7 (supertrace cancellation), Prop 5.6 (class sums, genuine representations) | 250–450 |
| L7 | Interface: structures for "nice holomorphic N=1 SVOA with RR index", hypotheses Thm 4.1, Cor 4.6 (lowest weight ρ_g), Prop 4.8 (DZ05 covariance), Hypothesis 5.5 ORB; statement of [OI] Theorem O relative to them | 200–350 |
| L8 | [OI] Theorem O from L1–L7 and the group theory of [OI] §2 (`decide` on Q₈ × ℤ/3) | 300–500 |
| **total** | | **≈ 1,900–3,350** |

- Together with the code-level components ([EQ] ≈ 1,200–1,900, [CS] ≈ 1,200–2,000 plus 800–1,200 for the length-72 certificate) and ≈ 100–200 lines of final assembly, a Lean statement **"for every k there is a holomorphic N=1 SVOA of central charge 12k and index 24/gcd(k,24), assuming ORB, [DZ05]/[BK04]-type interface hypotheses and the non-anomaly of the groups"** is ≈ **5,200–8,700 lines**. The anomaly component ([MQ] §8) is not counted here: stated as a hypothesis it costs ≈ 50–100 lines, and proving it is a different matter.
- **A genuine formalization of the VOA side** (lattice VOSAs, twisted modules [BK04]/[Li96], Zhu algebras and [DZ05] modular invariance, the Huang–Lepowsky–Zhang tensor category theory, [Hua08], [CM16], [McR21], [CKM24], GJF Thm 4.2 with supercohomology, and the anomaly computations of [MQ] §8) is several hundred pages of dense mathematics: an order-of-magnitude guess is **2·10⁵–5·10⁵ lines**, dominated by HLZ tensor categories and modular invariance [H].

--------------------------------------------------------------------------------------------

## 8. Verification [V: `ternary60/theory/blueprint_foundations.py`, log beside it; ≈ 3 s]

- **Part 1** (Prop 3.2(d)). Per-coordinate lattice sums: θ₀ = 0, θ₁ = η, θ₂ = −η termwise to x^200 (x = q^{1/24}). Σ_λ(−1)^{⟨χ,λ⟩}q^{|λ+χ/2|²/2} = Index·ηⁿ through q^{n/24+3} for tetracode³ (Index 0), 4E₃⁺ (0), Golay (24) and `q8chain_len24` (24). The leading term is Index·q^{n/24}.
- **Part 2** (Props 3.2, 3.3).
  - Per-coordinate minima {0: 9 at a ∈ {−3, 0}; 1: 1 at a = −2; 2: 1 at a = −1}.
  - Golay: 24 maximal words, all even. `q8chain_len24`: 88 maximal words, 56 − 32 = 24. For every maximal word: 2a+3 = −ι(w) and parity (−1)^{Σa} = f(w) = f(−w).
  - Equivariance under J, K; J fixes no maximal word.
  - `z12seed_len36_3` with h = g⁴: the h-fixed sign vector exists and is characteristic; 16 h-fixed maximal words with χ'/χ parity ratio constant; T_h = 0.
- **Part 3** (Prop 4.5). 400 random signed permutations (127 fixed-point-free): the ρ identity, Σk·d_k = n, fixed-point-free ⟺ Σd_k = 0, and |det(1−g)| = Πk^{d_k} (exact determinants). For −1, J, JK, −h, g of order 12, g², g³ and h (order 3): Frame shapes, ρ_g, leading exponent ρ_g − n/24, and the S-transform numerically (relative error ≤ 5·10⁻¹⁵).
- **Part 4** (Lemma 4.3, Props 4.4, 4.7). [BK04]'s P_σ/Q and defect computed from the definitions by coset enumeration, on the lattices listed under Prop 4.4 and the frame cases of Prop 4.7. All agree with the predictions. 300 random signed permutations: ⟨χ,(1−g)χ⟩ = 6·#{s_i = −1}.
- **Part 5** (Lemmas 2.2, 4.2). t_{χ/2} = parity on a basis of Λ(C); (g⁻¹ − 1)a = χ/2 solved exactly for −1 (Golay), J (`q8chain_len24`), g and g² (`z12seed_len36_3`).
- **Part 6** (Lemma 2.5). det Λ_ev = 4; the four representatives lie in Λ_ev^*, are distinct mod Λ_ev and have order ≤ 2; q = (0, ½, ½, ½) for n = 12 and (0, ½, 0, 0) for n = 24.

--------------------------------------------------------------------------------------------

## 9. Issues found

*Status (2026-09-27): the items below are tracked, with what has been fixed since, in `README.md` §5.*

None of these changes a result of [MQ] or [OI]. Items 1–3 and 5 concern citations or statements that should be corrected in those files (not edited here).

1. **Uniqueness of twisted sectors is cited to bosonic or non-uniqueness results.** [OI] §1 and §4 cite "Dong–Li–Mason, van Ekeren" for the uniqueness of V_{R,g}.
   - [DLM00] Thm 10.3 is for VOAs.
   - [vE13] proves modular invariance, not uniqueness, and uses the opposite ("Ramond-based") labelling of twisted modules (Warning 1.3).
   - The super statement is **[DZ05] Thm 7.7** (unique σ-stable simple g-twisted module), with g-rationality from [DRY22] Prop 3.4 (Thm 4.1 here). Likewise, the modular covariance of [OI] §3.3 is **[DZ05] Thms 4.12, 7.7**, whose (g,h)-labels are exactly the RR labels (Prop 4.8).
2. **Odd-lattice twisted modules are cited to even-lattice or VOA papers.**
   - [OI] Lemma 3.1 cites Lepowsky 1985 and Dong–Lepowsky (even lattices).
   - [MQ] §8.3 cites FLM/Dong–Lepowsky, and [MQ] §8.5 attributes "each signed 2-cycle contributes one Majorana zero mode" to **Barron–Dong–Mason, which treats unsigned cyclic permutations of tensor powers of VOAs**.
   - The correct references for V_{Λ(C)} (a VOSA) are **[BK04] Thm 4.2 and Rem 4.4** (integral lattices) and **[Li96] Prop 5.4** (Δ-operator for VOSAs).
   - The statements themselves are right: Props 4.4 and 4.7, [V: Part 4].
3. **[OI] §3.2: "The lift of h is unique: an element of order 3 in Λ̂[2].Aut(C) has a unique lift of order 3" is false as stated.** Order-3 lifts are unique only up to Λ̂[2]-conjugacy, and the action on V_R is ζ·ĥ with ζ³ = 1, fixed by the trivialisation. The correct statement is Prop 3.3(iii): Z_RR(1,h) = ζ·(±T_h).
   - The conclusion used (vanishing when T_h = 0) is unaffected.
   - [MQ] §7's heuristic "(Index + 8T_h)/3" states its no-phase assumption explicitly and is labelled [H]. Prop 3.3(iii) identifies the phase of the untwisted term: it is the cube root ζ fixed by the trivialisation.
   - GJF's proof of Thm 5.6 has the same imprecision.
4. **Minor gap in [MQ] Lemma 8.3.** "V_{−1} has the same character, so as an F-module it is this irreducible module" needs complete reducibility of θ-twisted F-modules ([BK04] Thm 4.2) and the dimension count dim T = 2^{n/2} for Λ(C) (Prop 4.4). Filled in Prop 4.7(b).
5. **Status of GJF Thm 4.2 (fermionic).** [OI] §4 and [MQ] (Cor 8.2, Thm 10.1, Cor 10.2) label it [T]. Its rigorous ingredients exist (Thm 5.2 via [CM16]; [McR21]; [DZ05]; [CKL20]/[CKM24]), but no complete written proof of "anomaly in S̃H³ and trivialisations ↔ holomorphic orbifolds with W_R = ⊕V(gσ)^{C(g)}" was found (Thm 5.4). It should be [T*]; the Main Question answer is conditional on Hypothesis 5.5 for the groups used. [MQ] §8.2 already puts GJF Thm 4.2 at the level of the gauging lemma, so this is a labelling issue, not a new gap.
6. **Wording in [OI] §4 table.** "orbifold W = ⊕ V_{R,g}^{C(g)}" should read "W_R = ⊕_{[g]} V_{R,g}^{C(g)}" (W itself is ⊕ V(g)^{C(g)} over NS twisted sectors). [OI] §1.2 has it right.
7. **Dangling reference.** [OI] §4 cites `notes/lean-blueprint.md` for "regularity of V^G … super case via the even part". The file does not exist (also [EQ] issue 5, [CS] issue 7). Thm 5.2 here is the intended argument.
8. **In GJF's own text (not our notes).**
   - The proof of Thm 5.6 counts "3(m/2) − 2×odd" per block for ⟨χ,(1−g)χ⟩; the correct value is 6×odd (Lemma 4.3), and the conclusion is unaffected.
   - Prop 2.4's proof leaves the parity of the ground states implicit (Prop 3.2 makes it sign-exact).
   - §2 cites FLM Thm 8.10.2 (even lattices) for odd lattice SVOAs.
9. **Precision on [MQ] Prop 8.5.2.** "S-invariance of holomorphic SVOA characters (Dong–Zhao, van Ekeren)": the precise derivation is Prop 4.8(c) ([DZ05] Thms 4.12, 7.7 plus positivity at τ = i). No change of substance.
10. (Bookkeeping.) `ternary60/theory/blueprint_foundations.py` has no row in README's layout table yet. This task could not edit existing files.

Confirmed as stated: [OI] Lemma 3.1's formula and its values n/16, 3n/64 (Prop 4.5, [V: Part 3]); the conjugation (−1)^F ~ inner (Lemma 4.2); [OI] (1.1) (Prop 2.6, Lemma 2.7); [OI] (1.3) (Props 3.1–3.3); [MQ] Lemma 8.3's commutator form ⟨α,β⟩ + |α|²|β|² mod 2 ([BK04] §4.3, C_{α,β} for N = 2); the Majorana-layer criterion used in [MQ] §8.2 and §8.4 (Lemma 4.3); T_x = spinor module of Cl(n/2) of dimension 2^{n/4} ([MQ] §8.5; Prop 4.7(c)).
