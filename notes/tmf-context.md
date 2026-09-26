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
