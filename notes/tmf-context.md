# TMF context for GJF Conjecture 1.4

Background facts that `ternary-code-index.md` relies on.

## The prediction being tested

**The theory.** A self-dual ternary code C of length n = 12k gives a holomorphic N=1 SVOA V_{Λ(C)} with c = n.
- Its RR partition function is Index(C)·Δᵏ.
- Index(C) is #even − #odd maximal codewords (GJF Prop 2.4, Rem 2.5).

**Stolz–Teichner.** GJF Conj 5.4–5.5 predict that such a theory defines a class in π_{24k}TMF mapping to Index·Δᵏ ∈ MF_{12k}.

**Image theorem [T: Hopkins ICM 2002, Prop 4.6].** In degree d = 24ℓ, the image of π_d TMF → MF_{12ℓ} is {Δ^ℓ P(j) : 24/gcd(24,ℓ) divides P(0)}, and the cokernel is ℤ/(24/gcd(24,ℓ)).
- So the TMF prediction is **24/gcd(24,k) | Index(C)**.
- ℓ = 1 is "24 | index of a c = 12 holomorphic SCFT" (GJF).
- The obstruction is detected by (Z/Δ^ℓ)(e^{2πi/3}) mod 24/gcd(24,ℓ).

**For codes.** 24 | Index(C) is proved for all self-dual ternary codes (Proofs I and II in `ternary-code-index.md`). This is stronger than the TMF prediction whenever gcd(24,k) > 1.

## Why codes are special

GJF Thm 5.6 says that orbifolds of V_{Λ(C)} by code automorphisms acting on the frame can realise 24/gcd(24,k)·Δᵏ. The existence half of Conj 1.4 (a code of index exactly 24 at every length 12k) is the input for that construction.

GJF Question 0.1 asks for a systematic construction of index-24 codes. Theorem 5.7 of `ternary-code-index.md` gives one for lengths 12·2^j.

## Prime-by-prime heuristic (Remark 3(b) of `ternary-code-index.md`)

- Level-3 structure (code neighbours, i.e. Z/3-orbifolds) controls the prime 2.
- Level-2 structure (GJF's even neighbours Λ^±, bosonisation) controls the prime 3.
- In terms of level-N descent this is TMF[1/N] = TMF(N)^{hGL₂(ℤ/N)}. At level 3, p = 2, [a₃] detects ν with order 4 and [a₃]² detects ν². At level 2, p = 3, α and β appear.

## The periodicity unit in degree 24² = 576 (2026-09-29)

**Remark (the k = 24 case of the Main Question realises a unit of π_*TMF) [P, given C: GJF Conj 5.4–5.5 (Stolz–Teichner) and the inputs of Cor 10.2 of `main-question.md`; T: as cited].** Suppose V is a holomorphic N=1 SVOA with c = 288 and index ±1. Such a V exists by `main-question.md` Thm 10.1 / Cor 10.2. Then its class [V] ∈ π₅₇₆TMF is invertible in π_*TMF, and [V] ≡ ±Δ²⁴ modulo torsion.
- *Degrees.* c = 12k with k = 24 gives degree 24k = 576 = 24². The Main Question asks for index 24/gcd(24, 24) = 1, so [V] ↦ ±Δ²⁴ ∈ MF₂₈₈. The sign is a convention (Ramond parity, GJF Rem 5.3).
- *Units of π₅₇₆TMF are exactly the lifts of ±Δ²⁴.*
  - TMF = tmf[Δ⁻²⁴], so multiplication by a periodicity class gives π₅₇₆TMF ≅ π₀TMF.
  - The kernel of π_*TMF → MF[Δ⁻¹] is the torsion (rational isomorphism).
  - Torsion in π_*TMF is nilpotent [T: Devinatz–Hopkins–Smith nilpotence theorem]. It maps to zero in MU_*TMF, which is torsion-free: MU_*TMF is the ring of functions on Spec MU_* ×_{M_FG} M_ell, flat over M_ell and hence over ℤ.
  - A unit maps to a unit of Δ²⁴·ℤ[j], i.e. to ±Δ²⁴. Conversely, a lift of ±Δ²⁴ is ±Δ²⁴·(1 + nilpotent), which is a unit.
- *Consequence.* For a holomorphic SVOA with c = 288, "[V] is a unit" and "Index(V) = ±1" are equivalent. So a positive answer to the Main Question at k = 24 is exactly an SVOA representing the periodicity unit, up to torsion.
- *Caveats.*
  1. Stolz–Teichner fixes [V] only through its image Index·Δᵏ, so the torsion part of [V] is not determined. If π₀TMF is torsion-free, then [V] = ±Δ²⁴ exactly. I believe it is, but this has not been checked against the tmf tables (Bauer; Konter) [C].
  2. Only positive powers are realised. [V]ᵐ = [V^{⊗m}] realises Δ^{24m}, but Δ⁻²⁴ lives in degree −576 and cannot come from a holomorphic SVOA (c ≥ 0).
  3. The existence of V rests on everything Cor 10.2 rests on:
     - GJF's orbifold and anomaly theorems, including the fermionic GJF Thm 4.2, used as Hypothesis ORB (`notes/blueprint/orbifold-foundations.md` §5);
     - Thm 8.1;
     - [I], not yet independently read;
     - R_σ(E₇₂) = 24, confirmed by three programs but not certified in Lean.
- *Construction.* The self-dual code C of length 288 with Index 24 comes from the Q₈ × ℤ/3-equivariant chain on the E₇₂ seed (`ternary60/codes/q8z3_chain_len288.txt`). Then V = V_{Λ(C)}//(Q₈ × ℤ/3), with index 24/24 = 1 (`orbifold-index.md`, Theorem O).
