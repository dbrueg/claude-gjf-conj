import GJF.Divisibility

/-!
# `IsSelfDual` versus Mathlib's orthogonal complement

`GJF.IsSelfDual C` is stated with the explicit dot product `GJF.dot`. This file relates it to
Mathlib's API:

* `GJF.dot` is definitionally `dotProduct` (`⬝ᵥ`);
* `GJF.dotForm n` is `dotProductBilin` as a `LinearMap.BilinForm`, which is nondegenerate and
  reflexive;
* `GJF.isSelfDual_iff_orthogonal_eq`: `IsSelfDual C ↔ (dotForm n).orthogonal C = C`;
* `GJF.isSelfDual_iff_selfOrthogonal`: `IsSelfDual C ↔ C ≤ C^⊥ ∧ 2 · dim C = n`
  (self-orthogonal of half dimension), via Mathlib's `finrank_orthogonal`;
* `GJF.index_dvd_24'`: the main theorem restated with Mathlib's orthogonal complement.
-/

open Module

namespace GJF

variable {n : ℕ}

lemma dot_eq_dotProduct (x y : Word n) : dot x y = x ⬝ᵥ y := rfl

/-- The standard dot product on `𝔽₃ⁿ` as a Mathlib bilinear form. -/
noncomputable def dotForm (n : ℕ) : LinearMap.BilinForm (ZMod 3) (Word n) :=
  dotProductBilin (ZMod 3) (ZMod 3)

@[simp] lemma dotForm_apply (x y : Word n) : dotForm n x y = dot x y := rfl

lemma dotForm_isRefl : (dotForm n).IsRefl := by
  intro x y h
  simpa [dotForm_apply, dot_comm] using h

lemma dotForm_nondegenerate : (dotForm n).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · funext k
    have := hx (Pi.single k 1)
    simpa [dotForm_apply, dot_eq_dotProduct, dotProduct_single] using this
  · funext k
    have := hy (Pi.single k 1)
    simpa [dotForm_apply, dot_eq_dotProduct, single_dotProduct] using this


/-- **Self-duality is Mathlib's `C^⊥ = C`** for the dot-product form. -/
theorem isSelfDual_iff_orthogonal_eq (C : Submodule (ZMod 3) (Word n)) :
    IsSelfDual C ↔ (dotForm n).orthogonal C = C := by
  constructor
  · intro h
    ext x
    rw [LinearMap.BilinForm.mem_orthogonal_iff, h x]
    exact forall₂_congr fun c _ => by rw [dotForm_apply, dot_comm]
  · intro h x
    conv_lhs => rw [← h]
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact forall₂_congr fun c _ => by rw [dotForm_apply, dot_comm]

/-- `dim C^⊥ = n - dim C`, from Mathlib's `finrank_orthogonal`.

`ZMod 3` carries two instance paths (from its `CommRing` and from its `Field` structure) whose
additive groups agree only up to default transparency, so the field lemma is applied with explicit
instance arguments and the result is transported by `Eq.trans` (definitional unfolding). -/
lemma finrank_orthogonal_dot (C : Submodule (ZMod 3) (Word n)) :
    finrank (ZMod 3) ((dotForm n).orthogonal C) = n - finrank (ZMod 3) C := by
  have h := @LinearMap.BilinForm.finrank_orthogonal (Word n) (ZMod 3) _ _
    (Pi.Function.module (Fin n) (ZMod 3) (ZMod 3)) Module.Finite.pi (dotForm n)
    dotForm_nondegenerate C
  exact h.trans (congrArg (· - finrank (ZMod 3) C) (finrank_fin_fun (ZMod 3)))

lemma finrank_le_length (C : Submodule (ZMod 3) (Word n)) : finrank (ZMod 3) C ≤ n :=
  (Submodule.finrank_le C).trans_eq (finrank_fin_fun (ZMod 3))

/-- A self-dual code has dimension `n / 2`. -/
theorem two_mul_finrank_of_isSelfDual {C : Submodule (ZMod 3) (Word n)} (hC : IsSelfDual C) :
    2 * finrank (ZMod 3) C = n := by
  have h := finrank_orthogonal_dot C
  rw [(isSelfDual_iff_orthogonal_eq C).1 hC] at h
  have hle := finrank_le_length C
  omega

/-- **Standard characterization:** self-dual ⟺ self-orthogonal of half dimension. -/
theorem isSelfDual_iff_selfOrthogonal (C : Submodule (ZMod 3) (Word n)) :
    IsSelfDual C ↔ (∀ x ∈ C, ∀ y ∈ C, dot x y = 0) ∧ 2 * finrank (ZMod 3) C = n := by
  constructor
  · intro hC
    exact ⟨fun x hx y hy => (hC x).1 hx y hy, two_mul_finrank_of_isSelfDual hC⟩
  · rintro ⟨hso, hdim⟩
    rw [isSelfDual_iff_orthogonal_eq]
    have hle : C ≤ (dotForm n).orthogonal C := fun x hx c hc => by
      rw [dotForm_apply]; exact hso c hc x hx
    have h := finrank_orthogonal_dot C
    have hfin : finrank (ZMod 3) C = finrank (ZMod 3) ((dotForm n).orthogonal C) := by omega
    exact (@Submodule.eq_of_le_of_finrank_eq (ZMod 3) (Word n) _ _
      (Pi.Function.module (Fin n) (ZMod 3) (ZMod 3)) C _ _ hle hfin).symm

/-- Self-dual ternary codes have even length. -/
theorem even_of_isSelfDual {C : Submodule (ZMod 3) (Word n)} (hC : IsSelfDual C) : Even n :=
  ⟨finrank (ZMod 3) C, by have := two_mul_finrank_of_isSelfDual hC; omega⟩

/-- **The main theorem with Mathlib's orthogonal complement.** -/
theorem index_dvd_24' (C : Submodule (ZMod 3) (Fin n → ZMod 3))
    (hC : LinearMap.BilinForm.orthogonal (dotProductBilin (ZMod 3) (ZMod 3)) C = C) (hn : 0 < n) :
    (24 : ℤ) ∣ gjfIndex C :=
  index_dvd_24 C ((isSelfDual_iff_orthogonal_eq C).2 hC) hn

end GJF
