import GJF.SPerm
import GJF.Sanity

/-!
# Theorem D: an automorphism with `g⁴ = -1` forces `48 ∣ Index`

A formalization of Theorem D of `paper/conj14.tex` (§8; notes `main-question.md`, Thm 5.1).

**Theorem D.** Let `C` be a self-dual ternary code of length `n > 0` and `g` a signed permutation
with `g C ⊆ C` (so `g ∈ Aut C`) and `g⁴ = -1`. Then `4 ∣ n`, `48 ∣ Index(C)`, and `Index(C) = 0` if `n/4` is odd
(`GJF.Obs.theoremD`; for length `12k`: `GJF.Obs.theoremD_twelve`).

The proof is the one of the paper, with the field `𝔽₉` eliminated.
* `V₊ = ker p(g)`, `V₋ = ker q(g)` with `p = x² + x - 1`, `q = x² - x - 1` (`pq = x⁴ + 1` over `𝔽₃`)
  are totally isotropic, `e₊ = g³ + g - 1` projects onto `V₊` along `V₋`, and `V₋` contains no
  maximal word.
* **Four-code identity** (`Setup.four_code`). For `v ∈ C ∩ V₊`, `v ≠ 0`, choose `w ∈ V₋` with
  `v·w = 1`, put `W = ⟨w, gw⟩` and `D = C ∩ W^⊥`. Then `D^⊥ = C ⊕ W`; a maximal word of `D^⊥` lies
  in `C`, in `C₂ = D + W`, or in one of the graphs `C₃`, `C₄` of `±L` with
  `L c = (c·w) gw - (c·gw) w`. Poisson summation (`F(D^⊥) = 9 F(D)`) gives
  `Index C + Index C₂ + Index C₃ + Index C₄ = 12 F(D)`, and `g` maps `C₃` onto `C₄`.
* **Induction** on `|C ∩ V₊|` (`sixteen_dvd`): `16 ∣ Index C₂`, `8 ∣ Index C₃` (Theorem A),
  `4 ∣ F(D)` (the free action of `⟨g²⟩ ≅ ℤ/4`), so `16 ∣ Index C`. At the bottom `C ⊆ V₋`.
* For a signed permutation, `g⁴ = -1` forces all cycles to have length `4` and sign product `-1`
  (`orbit_count`), so `4 ∣ n` and `f ∘ g = (-1)^(n/4) f`.
-/

open Finset

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Obs

open GJF

local notation "F" => ZMod 3

variable {n : ℕ}

/-! ### The dot product -/

lemma dot_add_right (x y z : Word n) : dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_sub_left (x y z : Word n) : dot (x - y) z = dot x z - dot y z := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_sub_right (x y z : Word n) : dot x (y - z) = dot x y - dot x z := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

lemma dot_smul_left (a : F) (x y : Word n) : dot (a • x) y = a * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma dot_smul_right (a : F) (x y : Word n) : dot x (a • y) = a * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `x ↦ x·w` as a linear form. -/
def dotL (w : Word n) : Word n →ₗ[F] F where
  toFun x := dot x w
  map_add' x y := dot_add_left x y w
  map_smul' a x := dot_smul_left a x w

@[simp] lemma dotL_apply (w x : Word n) : dotL w x = dot x w := rfl

lemma F_add_self : ∀ a : F, a + a = 0 → a = 0 := by decide

/-! ### Polynomials in `G` -/

section Poly

variable (G : Module.End F (Word n))

/-- `p(G) = G² + G - 1`; `V₊ = ker p(G)`. -/
def Pp : Module.End F (Word n) := G ^ 2 + G - 1

/-- `q(G) = G² - G - 1`; `V₋ = ker q(G)`. -/
def Qm : Module.End F (Word n) := G ^ 2 - G - 1

/-- `e₊ = G³ + G - 1`, the projector onto `V₊` along `V₋`. -/
def Ep : Module.End F (Word n) := G ^ 3 + G - 1

variable {G}

lemma pow_two_apply (x : Word n) : (G ^ 2) x = G (G x) := by
  rw [pow_two, Module.End.mul_apply]

lemma pow_three_apply (x : Word n) : (G ^ 3) x = G (G (G x)) := by
  rw [pow_succ, Module.End.mul_apply, pow_two_apply]

lemma pow_four_apply (x : Word n) : (G ^ 4) x = G (G (G (G x))) := by
  rw [pow_succ, Module.End.mul_apply, pow_three_apply]

lemma Pp_apply (x : Word n) : Pp G x = G (G x) + G x - x := by
  simp [Pp, pow_two_apply]

lemma Qm_apply (x : Word n) : Qm G x = G (G x) - G x - x := by
  simp [Qm, pow_two_apply]

lemma Ep_apply (x : Word n) : Ep G x = G (G (G x)) + G x - x := by
  simp [Ep, pow_three_apply]

/-- Close an identity in `𝔽₃` that holds as a polynomial identity modulo `3`. -/
macro "f3" : tactic => `(tactic| (rw [← sub_eq_zero]; ring_nf; reduce_mod_char; try simp))

/-- Close an identity between words that holds coordinatewise modulo `3`. -/
macro "wf3" : tactic => `(tactic| (funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
  Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; f3))

variable (h4 : ∀ x, G (G (G (G x))) = -x)
include h4 in
/-- `e₊ x ∈ V₊`. -/
lemma Pp_Ep (x : Word n) : Pp G (Ep G x) = 0 := by
  simp only [Pp_apply, Ep_apply, map_add, map_sub, map_neg, h4]
  wf3

include h4 in
/-- `x - e₊ x ∈ V₋`. -/
lemma Qm_sub_Ep (x : Word n) : Qm G (x - Ep G x) = 0 := by
  simp only [Qm_apply, Ep_apply, map_add, map_sub, map_neg, h4]
  wf3

/-- `e₊` kills `V₋`. -/
lemma Ep_of_Qm {y : Word n} (hy : Qm G y = 0) : Ep G y = 0 := by
  rw [Qm_apply, sub_sub, sub_eq_zero] at hy
  rw [Ep_apply, hy, map_add, hy]
  wf3

/-- `e₊` is the identity on `V₊`. -/
lemma Ep_of_Pp {x : Word n} (hx : Pp G x = 0) : Ep G x = x := by
  rw [Pp_apply, add_sub_assoc, add_eq_zero_iff_eq_neg, neg_sub] at hx
  rw [Ep_apply, hx, map_sub, hx]
  wf3

end Poly

/-! ### The hypotheses on `G` -/

/-- What the induction uses about `G` (a signed permutation with `g⁴ = -1` and `f ∘ g = f`) and
about the length. -/
structure Hyp (G : Module.End F (Word n)) : Prop where
  pos : 0 < n
  three : 3 ∣ n
  four_dvd : 4 ∣ n
  isom : ∀ x y, dot (G x) (G y) = dot x y
  four : G ^ 4 = -1
  fG : ∀ x, f (G x) = f x
  noMax : ∀ x, Qm G x = 0 → ¬ ∀ i, x i ≠ 0

namespace Hyp

variable {G : Module.End F (Word n)} (hG : Hyp G)
include hG

lemma G4 (x : Word n) : G (G (G (G x))) = -x := by
  have := LinearMap.congr_fun hG.four x
  rwa [pow_four_apply] at this

lemma G2_of_Qm {x : Word n} (hx : Qm G x = 0) : G (G x) = G x + x := by
  rw [Qm_apply, sub_sub, sub_eq_zero] at hx; exact hx

lemma G2_of_Pp {x : Word n} (hx : Pp G x = 0) : G (G x) = x - G x := by
  rw [Pp_apply, add_sub_assoc, add_eq_zero_iff_eq_neg, neg_sub] at hx; exact hx

/-- `V₋` is totally isotropic. -/
lemma dot_of_Qm {x y : Word n} (hx : Qm G x = 0) (hy : Qm G y = 0) : dot x y = 0 := by
  have e1 := hG.isom (G x) y
  have e2 := hG.isom x (G y)
  rw [hG.G2_of_Qm hx, dot_add_left, hG.isom] at e1
  rw [hG.G2_of_Qm hy, dot_add_right, hG.isom] at e2
  apply F_add_self
  linear_combination e1 + e2

/-- `V₊` is totally isotropic. -/
lemma dot_of_Pp {x y : Word n} (hx : Pp G x = 0) (hy : Pp G y = 0) : dot x y = 0 := by
  have e1 := hG.isom (G x) y
  have e2 := hG.isom x (G y)
  rw [hG.G2_of_Pp hx, dot_sub_left, hG.isom] at e1
  rw [hG.G2_of_Pp hy, dot_sub_right, hG.isom] at e2
  apply F_add_self
  linear_combination -e1 - e2

/-- On `V₋`, `g⁻¹ = g - 1`: `(gv)·w = v·(gw) - v·w`. -/
lemma dot_G_left_of_Qm (v : Word n) {w : Word n} (hw : Qm G w = 0) :
    dot (G v) w = dot v (G w) - dot v w := by
  have h := hG.isom v (G w - w)
  rw [map_sub, hG.G2_of_Qm hw, add_sub_cancel_left] at h
  rw [h, dot_sub_right]

lemma Qm_G {x : Word n} (hx : Qm G x = 0) : Qm G (G x) = 0 := by
  rw [Qm_apply] at hx ⊢
  rw [← map_sub, ← map_sub, hx, map_zero]

lemma f_G2 (x : Word n) : f (G (G x)) = f x := by rw [hG.fG, hG.fG]

lemma even : Even n := by
  obtain ⟨m, hm⟩ := hG.four_dvd
  exact ⟨2 * m, by omega⟩

end Hyp

/-! ### `4 ∣ F(A)` for a set with a free action of `⟨J⟩ ≅ ℤ/4` -/

lemma f_neg_of_even (hn : Even n) (x : Word n) : f (-x) = f x := by
  rw [show f (-x) = (-1) ^ n * f x from f_neg x, hn.neg_one_pow, one_mul]

/-- If `A` is closed under `-1` and `J` with `J² = -1` and `f ∘ J = f`, then `4 ∣ Σ_{x ∈ A} f x`.
The orbits of `⟨J⟩` on nonzero words have size `4`. -/
lemma four_dvd_sum (hn : Even n) (hpos : 0 < n) (J : Word n → Word n) (hJJ : ∀ x, J (J x) = -x)
    (hJneg : ∀ x, J (-x) = -J x) (hfJ : ∀ x, f (J x) = f x) (A : Finset (Word n))
    (hA : ∀ x ∈ A, -x ∈ A) (hAJ : ∀ x ∈ A, J x ∈ A) : (4 : ℤ) ∣ ∑ x ∈ A, f x := by
  classical
  let a : Fin n := ⟨0, hpos⟩
  rw [sum_eq_two_mul hn A hA a]
  -- the involution `τ x = ±J x` on `B = {x ∈ A : x_a = 1, f x ≠ 0}`
  set B := (A.filter fun x => x a = 1).filter fun x => f x ≠ 0 with hB
  have hsum : ∑ x ∈ A.filter (fun x => x a = 1), f x = ∑ x ∈ B, f x := by
    rw [hB, Finset.sum_filter_ne_zero]
  let τ : Word n → Word n := fun x => if J x a = 1 then J x else -J x
  have hmemB : ∀ {x}, x ∈ B ↔ (x ∈ A ∧ x a = 1) ∧ f x ≠ 0 := by
    intro x; simp [hB, Finset.mem_filter]
  have hτf : ∀ x, f (τ x) = f x := by
    intro x; simp only [τ]; split_ifs
    · exact hfJ x
    · rw [f_neg_of_even hn, hfJ]
  have hτB : ∀ x ∈ B, τ x ∈ B := by
    intro x hx
    rw [hmemB] at hx ⊢
    obtain ⟨⟨hxA, hxa⟩, hfx⟩ := hx
    refine ⟨⟨?_, ?_⟩, by rwa [hτf]⟩
    · simp only [τ]; split_ifs
      · exact hAJ x hxA
      · exact hA _ (hAJ x hxA)
    · have hJa : J x a ≠ 0 := max_of_f_ne_zero (by rwa [hfJ]) a
      simp only [τ]; split_ifs with h
      · exact h
      · rw [Pi.neg_apply]
        revert hJa h; generalize J x a = b; revert b; decide
  have hne : ∀ x ∈ B, τ x ≠ x := by
    intro x hx heq
    rw [hmemB] at hx
    have hxa := hx.1.2
    have hJx : J x = x ∨ J x = -x := by
      simp only [τ] at heq; split_ifs at heq
      · exact Or.inl heq
      · exact Or.inr (neg_eq_iff_eq_neg.1 heq)
    have hxx : -x = x := by
      rcases hJx with h | h
      · rw [← hJJ x, h, h]
      · rw [← hJJ x, h, hJneg, h, neg_neg]
    have := congrFun hxx a
    rw [Pi.neg_apply, hxa] at this
    exact absurd this (by decide)
  have hinv : ∀ x ∈ B, τ (τ x) = x := by
    intro x hx
    have hxa := (hmemB.1 hx).1.2
    have hττ := hmemB.1 (hτB _ (hτB x hx))
    -- `τ (τ x) = ±x`, and its `a`-entry is `1`
    have hpm : τ (τ x) = x ∨ τ (τ x) = -x := by
      simp only [τ]
      split_ifs <;> simp [hJJ, hJneg]
    rcases hpm with h | h
    · exact h
    · have := hττ.1.2
      rw [h, Pi.neg_apply, hxa] at this
      exact absurd this (by decide)
  have h2 : (2 : ℤ) ∣ ∑ x ∈ B, f x := by
    have hz : ∑ x ∈ B, ((f x : ℤ) : ZMod 2) = 0 := by
      refine Finset.sum_involution (fun x _ => τ x) ?_ ?_ (fun x hx => hτB x hx)
        (fun x hx => hinv x hx)
      · intro x _
        rw [hτf, ← two_mul]
        exact mul_eq_zero_of_left (by decide) _
      · intro x hx _; exact hne x hx
    have : (((∑ x ∈ B, f x : ℤ)) : ZMod 2) = 0 := by push_cast; exact hz
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 this
  rw [hsum]
  obtain ⟨m, hm⟩ := h2
  exact ⟨m, by rw [hm]; ring⟩

/-! ### Poisson summation for a pair `D`, `D^⊥` -/

/-- The words orthogonal to `D`, as a finset. -/
noncomputable def perpS (D : Submodule F (Word n)) : Finset (Word n) := by
  classical exact univ.filter fun x => ∀ u ∈ D, dot u x = 0

lemma mem_perpS {D : Submodule F (Word n)} {x : Word n} :
    x ∈ perpS D ↔ ∀ u ∈ D, dot u x = 0 := by
  classical simp [perpS]

lemma charsum_perp (D : Submodule F (Word n)) (x : Word n) :
    ∑ u ∈ CS D, ψ (dot u x) = if x ∈ perpS D then (#(CS D) : ℂ) else 0 := by
  split_ifs with hx
  · have h1 : ∀ u ∈ CS D, ψ (dot u x) = 1 := fun u hu => by
      rw [mem_perpS.1 hx u (mem_CS.1 hu), ψ_zero]
    rw [Finset.sum_congr rfl h1]
    simp
  · rw [mem_perpS] at hx
    push Not at hx
    obtain ⟨c, hc, hcx⟩ := hx
    have hshift : ∑ u ∈ CS D, ψ (dot (u + c) x) = ∑ u ∈ CS D, ψ (dot u x) := by
      refine Finset.sum_nbij' (fun u => u + c) (fun u => u - c) ?_ ?_ ?_ ?_ ?_
      · intro u hu; exact mem_CS.2 (D.add_mem (mem_CS.1 hu) hc)
      · intro u hu; exact mem_CS.2 (D.sub_mem (mem_CS.1 hu) hc)
      · intro u _; simp
      · intro u _; simp
      · intro u _; rfl
    simp_rw [dot_add_left, ψ_add, ← Finset.sum_mul] at hshift
    have h1 : (∑ u ∈ CS D, ψ (dot u x)) * (ψ (dot c x) - 1) = 0 := by
      rw [mul_sub, hshift, mul_one, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) (ψ_ne_one hcx)

/-- Poisson summation: `Σ_{u ∈ D} ĥ(u) = |D| Σ_{x ∈ D^⊥} h(x)`. -/
lemma poisson_perp (D : Submodule F (Word n)) (h : Word n → ℂ) :
    ∑ u ∈ CS D, hat h u = (#(CS D) : ℂ) * ∑ x ∈ perpS D, h x := by
  simp only [hat]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, charsum_perp, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- `|D| · |D^⊥| = 3ⁿ`. -/
lemma card_mul_card_perpS (D : Submodule F (Word n)) :
    (#(CS D) : ℂ) * #(perpS D) = 3 ^ n := by
  have h := poisson_perp D (fun _ => (1 : ℂ))
  simp_rw [hat_one] at h
  simp only [Finset.sum_ite_eq', mem_CS.2 D.zero_mem, ite_true, Finset.sum_const, nsmul_eq_mul,
    mul_one] at h
  exact h.symm

/-- `f̂ = κⁿ f`. -/
lemma hat_f (u : Word n) : hat (fun x : Word n => (f x : ℂ)) u = κ ^ n * f u := by
  have e : (fun x : Word n => (f x : ℂ)) = fun x => ∏ k, ((phi (x k) : ℤ) : ℂ) := by
    funext x; simp [f]
  rw [e, hat_prod (fun _ a => ((phi a : ℤ) : ℂ))]
  simp_rw [phi_hat, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, f, Int.cast_prod]

/-! ### Finite facts about `𝔽₃` -/

lemma F_indep : ∀ t a b : F, a + b * t = 0 → a * (t - 1) + b = 0 → a = 0 ∧ b = 0 := by decide

lemma F_surj : ∀ t α β : F, ∃ a b : F, a + b * (t - 1) = α ∧ a * t + b = β := by decide

lemma F_line : ∀ p q a b : F, ¬ (p = 0 ∧ q = 0) → a * p + b * q = 0 →
    (a = 0 ∧ b = 0) ∨ (a = -q ∧ b = p) ∨ (a = q ∧ b = -p) := by decide

lemma F_line_ne : ∀ p q : F, ¬ (p = 0 ∧ q = 0) →
    ((0 : F), (0 : F)) ≠ (-q, p) ∧ ((0 : F), (0 : F)) ≠ (q, -p) ∧ (-q, p) ≠ (q, -p) := by decide

/-- A sum over `𝔽₃²` of a function supported on the line `a p + b q = 0`. -/
lemma sum_line (Φ : F × F → ℤ) (p q : F) (hpq : ¬ (p = 0 ∧ q = 0))
    (h : ∀ ab : F × F, ab.1 * p + ab.2 * q ≠ 0 → Φ ab = 0) :
    ∑ ab : F × F, Φ ab = Φ (0, 0) + Φ (-q, p) + Φ (q, -p) := by
  classical
  obtain ⟨h1, h2, h3⟩ := F_line_ne p q hpq
  rw [← Finset.sum_subset (Finset.subset_univ ({(0, 0), (-q, p), (q, -p)} : Finset (F × F)))]
  · rw [Finset.sum_insert (by rw [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1, h2⟩),
      Finset.sum_pair h3, add_assoc]
  · intro ab _ hab
    apply h
    intro h0
    apply hab
    rcases F_line p q ab.1 ab.2 hpq h0 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      simp [Prod.ext_iff, e1, e2]

/-! ### The four codes through `D` -/

section Four

variable {G : Module.End F (Word n)} {C : Submodule F (Word n)} {v w : Word n}

/-- `D = C ∩ ⟨w, gw⟩^⊥`. -/
def Dsub (G : Module.End F (Word n)) (C : Submodule F (Word n)) (w : Word n) :
    Submodule F (Word n) :=
  C ⊓ LinearMap.ker (dotL w) ⊓ LinearMap.ker (dotL (G w))

lemma mem_Dsub {x : Word n} : x ∈ Dsub G C w ↔ x ∈ C ∧ dot x w = 0 ∧ dot x (G w) = 0 := by
  simp [Dsub, and_assoc]

lemma D_le : Dsub G C w ≤ C := fun _ hx => (mem_Dsub.1 hx).1

/-- `L c = (c·w) gw - (c·gw) w`. -/
def Lm (G : Module.End F (Word n)) (w : Word n) : Word n →ₗ[F] Word n where
  toFun x := dot x w • G w - dot x (G w) • w
  map_add' x y := by simp only [dot_add_left, add_smul]; abel
  map_smul' a x := by simp only [dot_smul_left, mul_smul, smul_sub, RingHom.id_apply]

lemma Lm_apply (x : Word n) : Lm G w x = dot x w • G w - dot x (G w) • w := rfl

/-- `L c ∈ W`, with coefficients `(-(c·gw), c·w)`. -/
lemma Lm_eq (x : Word n) : Lm G w x = (-dot x (G w)) • w + dot x w • G w := by
  rw [Lm_apply, neg_smul]; abel

lemma sub_Lm (x : Word n) : x - Lm G w x = x + (dot x (G w) • w + (-dot x w) • G w) := by
  rw [Lm_eq, neg_smul, neg_smul]; abel

lemma Lm_of_D {d : Word n} (hd : d ∈ Dsub G C w) : Lm G w d = 0 := by
  rw [mem_Dsub] at hd
  rw [Lm_apply, hd.2.1, hd.2.2, zero_smul, zero_smul, sub_zero]

/-- `C₃ = {c + L c : c ∈ C}`, the graph of `L`. -/
def C3 (G : Module.End F (Word n)) (C : Submodule F (Word n)) (w : Word n) :
    Submodule F (Word n) :=
  C.map (LinearMap.id + Lm G w)

lemma mem_C3 {x : Word n} : x ∈ C3 G C w ↔ ∃ c ∈ C, c + Lm G w c = x := by
  simp [C3]

/-- `W = ⟨w, gw⟩`. -/
def Wsp (G : Module.End F (Word n)) (w : Word n) : Submodule F (Word n) :=
  Submodule.span F {w, G w}

/-- `C₂ = D + W`. -/
def C2 (G : Module.End F (Word n)) (C : Submodule F (Word n)) (w : Word n) :
    Submodule F (Word n) :=
  Dsub G C w ⊔ Wsp G w

lemma mem_C2 {x : Word n} :
    x ∈ C2 G C w ↔ ∃ d ∈ Dsub G C w, ∃ a b : F, d + (a • w + b • G w) = x := by
  simp only [C2, Submodule.mem_sup, Wsp, Submodule.mem_span_pair]
  constructor
  · rintro ⟨d, hd, y, ⟨a, b, rfl⟩, rfl⟩; exact ⟨d, hd, a, b, rfl⟩
  · rintro ⟨d, hd, a, b, rfl⟩; exact ⟨d, hd, _, ⟨a, b, rfl⟩, rfl⟩

lemma dot_add_add (x y x' y' : Word n) :
    dot (x + y) (x' + y') = dot x x' + dot x y' + dot y x' + dot y y' := by
  rw [dot_add_left, dot_add_right, dot_add_right]; ring

lemma dot_comb_right (x : Word n) (a b : F) :
    dot x (a • w + b • G w) = a * dot x w + b * dot x (G w) := by
  rw [dot_add_right, dot_smul_right, dot_smul_right]

/-- An isotropic code with `|X|² = 3ⁿ` is self-dual. -/
lemma selfDual_of_iso_card (X : Submodule F (Word n))
    (hiso : ∀ x ∈ X, ∀ y ∈ X, dot x y = 0) (hcard : #(CS X) * #(CS X) = 3 ^ n) :
    IsSelfDual X := by
  classical
  have hsub : CS X ⊆ perpS X := fun x hx =>
    mem_perpS.2 fun u hu => hiso u hu x (mem_CS.1 hx)
  have hmul : #(CS X) * #(perpS X) = 3 ^ n := by exact_mod_cast card_mul_card_perpS X
  have hpos : 0 < #(CS X) := Finset.card_pos.2 ⟨0, mem_CS.2 X.zero_mem⟩
  have hc : #(perpS X) = #(CS X) := Nat.eq_of_mul_eq_mul_left hpos (hmul.trans hcard.symm)
  have heq : CS X = perpS X := Finset.eq_of_subset_of_card_le hsub hc.le
  intro x
  rw [← mem_CS, heq, mem_perpS]
  exact ⟨fun h c hc => by rw [dot_comm]; exact h c hc, fun h u hu => by rw [dot_comm]; exact h u hu⟩

lemma kappa_pow (m : ℕ) : κ ^ (4 * m) = (9 : ℂ) ^ m := by
  rw [pow_mul, show κ ^ 4 = 9 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, κ_sq]; norm_num]

lemma card_eq_pow (hC : IsSelfDual C) {m : ℕ} (hm : n = 4 * m) : #(CS C) = 9 ^ m := by
  have h : #(CS C) * #(CS C) = 3 ^ n := by exact_mod_cast card_sq hC
  have h' : #(CS C) ^ 2 = (9 ^ m) ^ 2 := by
    rw [sq, h, hm, ← pow_mul, show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_mul]
    congr 1; ring
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h'

/-- The data of one induction step: `v ∈ C ∩ V₊` and `w ∈ V₋` with `v·w = 1`. -/
structure Setup (G : Module.End F (Word n)) (C : Submodule F (Word n)) (v w : Word n) : Prop where
  hG : Hyp G
  sd : IsSelfDual C
  inv : ∀ x ∈ C, G x ∈ C
  vC : v ∈ C
  vP : Pp G v = 0
  wM : Qm G w = 0
  vw : dot v w = 1

namespace Setup

variable (S : Setup G C v w)
include S

lemma GwM : Qm G (G w) = 0 := S.hG.Qm_G S.wM

lemma Qm_comb (a b : F) : Qm G (a • w + b • G w) = 0 := by
  rw [map_add, map_smul, map_smul, S.wM, S.GwM, smul_zero, smul_zero, add_zero]

lemma dot_W (a b a' b' : F) : dot (a • w + b • G w) (a' • w + b' • G w) = 0 :=
  S.hG.dot_of_Qm (S.Qm_comb a b) (S.Qm_comb a' b')

lemma dotC {x y : Word n} (hx : x ∈ C) (hy : y ∈ C) : dot x y = 0 :=
  dot_eq_zero_of_mem S.sd hx hy

lemma GvC : G v ∈ C := S.inv v S.vC

/-- `C ∩ W = 0`. -/
lemma comb_mem {a b : F} (h : a • w + b • G w ∈ C) : a = 0 ∧ b = 0 := by
  have h1 := S.dotC S.vC h
  have h2 := S.dotC S.GvC h
  rw [dot_comb_right, S.vw] at h1
  rw [dot_comb_right, S.hG.dot_G_left_of_Qm v S.wM, S.hG.isom, S.vw] at h2
  exact F_indep (dot v (G w)) a b (by linear_combination h1) (by linear_combination h2)

/-- `c ↦ (c·w, c·gw)` maps `C` onto `𝔽₃²`. -/
lemma surj (α β : F) : ∃ c ∈ C, dot c w = α ∧ dot c (G w) = β := by
  obtain ⟨a, b, h1, h2⟩ := F_surj (dot v (G w)) α β
  refine ⟨a • v + b • G v, C.add_mem (C.smul_mem a S.vC) (C.smul_mem b S.GvC), ?_, ?_⟩
  · rw [dot_add_left, dot_smul_left, dot_smul_left, S.vw, S.hG.dot_G_left_of_Qm v S.wM, S.vw]
    linear_combination h1
  · rw [dot_add_left, dot_smul_left, dot_smul_left, S.hG.isom, S.vw]
    linear_combination h2

/-- `C + W` is a direct sum. -/
lemma inj {p q : Word n × F × F} (hp : p.1 ∈ C) (hq : q.1 ∈ C)
    (h : p.1 + (p.2.1 • w + p.2.2 • G w) = q.1 + (q.2.1 • w + q.2.2 • G w)) : p = q := by
  have e : (q.2.1 - p.2.1) • w + (q.2.2 - p.2.2) • G w = p.1 - q.1 := by
    funext i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at this ⊢
    linear_combination -this
  obtain ⟨h1, h2⟩ := S.comb_mem (e ▸ C.sub_mem hp hq)
  have ha : p.2.1 = q.2.1 := (sub_eq_zero.1 h1).symm
  have hb : p.2.2 = q.2.2 := (sub_eq_zero.1 h2).symm
  rw [ha, hb] at h
  exact Prod.ext (add_right_cancel h) (Prod.ext ha hb)

/-- `D^⊥ = C ⊕ W`. -/
lemma mem_perp_iff (x : Word n) :
    x ∈ perpS (Dsub G C w) ↔ ∃ c ∈ C, ∃ a b : F, c + (a • w + b • G w) = x := by
  constructor
  · intro hx
    rw [mem_perpS] at hx
    obtain ⟨c1, hc1, h11, h12⟩ := S.surj 1 0
    obtain ⟨c2, hc2, h21, h22⟩ := S.surj 0 1
    refine ⟨x - (dot c1 x • w + dot c2 x • G w), ?_, dot c1 x, dot c2 x, sub_add_cancel _ _⟩
    refine (S.sd _).2 fun c hc => ?_
    have hd : c - (dot c w • c1 + dot c (G w) • c2) ∈ Dsub G C w := by
      rw [mem_Dsub]
      refine ⟨C.sub_mem hc (C.add_mem (C.smul_mem _ hc1) (C.smul_mem _ hc2)), ?_, ?_⟩
      · rw [dot_sub_left, dot_add_left, dot_smul_left, dot_smul_left, h11, h21]; ring
      · rw [dot_sub_left, dot_add_left, dot_smul_left, dot_smul_left, h12, h22]; ring
    have h0 := hx _ hd
    rw [dot_sub_left, dot_add_left, dot_smul_left, dot_smul_left] at h0
    rw [dot_comm, dot_sub_right, dot_comb_right]
    linear_combination h0
  · rintro ⟨c, hc, a, b, rfl⟩
    rw [mem_perpS]
    intro u hu
    rw [mem_Dsub] at hu
    rw [dot_add_right, dot_comb_right, S.dotC hu.1 hc, hu.2.1, hu.2.2]; ring

/-- The sum over `D^⊥` as a sum over `C × 𝔽₃²`. -/
lemma sum_perp {β : Type*} [AddCommMonoid β] (h : Word n → β) :
    ∑ x ∈ perpS (Dsub G C w), h x =
      ∑ c ∈ CS C, ∑ ab : F × F, h (c + (ab.1 • w + ab.2 • G w)) := by
  rw [← Finset.sum_product' (CS C) univ (fun c (ab : F × F) => h (c + (ab.1 • w + ab.2 • G w)))]
  symm
  refine Finset.sum_bij (fun p _ => p.1 + (p.2.1 • w + p.2.2 • G w)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product] at hp
    exact (S.mem_perp_iff _).2 ⟨p.1, mem_CS.1 hp.1, p.2.1, p.2.2, rfl⟩
  · intro p hp q hq hpq
    rw [Finset.mem_product] at hp hq
    exact S.inj (mem_CS.1 hp.1) (mem_CS.1 hq.1) hpq
  · intro x hx
    obtain ⟨c, hc, a, b, rfl⟩ := (S.mem_perp_iff x).1 hx
    exact ⟨(c, (a, b)), Finset.mem_product.2 ⟨mem_CS.2 hc, Finset.mem_univ _⟩, rfl⟩
  · intro p _; rfl

/-- The sum over `C₂` as a sum over `D × 𝔽₃²`. -/
lemma sum_C2 {β : Type*} [AddCommMonoid β] (h : Word n → β) :
    ∑ x ∈ CS (C2 G C w), h x =
      ∑ d ∈ CS (Dsub G C w), ∑ ab : F × F, h (d + (ab.1 • w + ab.2 • G w)) := by
  rw [← Finset.sum_product' (CS (Dsub G C w)) univ
    (fun d (ab : F × F) => h (d + (ab.1 • w + ab.2 • G w)))]
  symm
  refine Finset.sum_bij (fun p _ => p.1 + (p.2.1 • w + p.2.2 • G w)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product] at hp
    exact mem_CS.2 (mem_C2.2 ⟨p.1, mem_CS.1 hp.1, p.2.1, p.2.2, rfl⟩)
  · intro p hp q hq hpq
    rw [Finset.mem_product] at hp hq
    exact S.inj (D_le (mem_CS.1 hp.1)) (D_le (mem_CS.1 hq.1)) hpq
  · intro x hx
    obtain ⟨d, hd, a, b, rfl⟩ := mem_C2.1 (mem_CS.1 hx)
    exact ⟨(d, (a, b)), Finset.mem_product.2 ⟨mem_CS.2 hd, Finset.mem_univ _⟩, rfl⟩
  · intro p _; rfl

/-- The sum over `C₃` as a sum over `C`. -/
lemma sum_C3 {β : Type*} [AddCommMonoid β] (h : Word n → β) :
    ∑ x ∈ CS (C3 G C w), h x = ∑ c ∈ CS C, h (c + Lm G w c) := by
  symm
  refine Finset.sum_bij (fun c _ => c + Lm G w c) ?_ ?_ ?_ ?_
  · intro c hc; exact mem_CS.2 (mem_C3.2 ⟨c, mem_CS.1 hc, rfl⟩)
  · intro c hc c' hc' h'
    have := S.inj (p := (c, (-dot c (G w), dot c w))) (q := (c', (-dot c' (G w), dot c' w)))
      (mem_CS.1 hc) (mem_CS.1 hc') (by
        show c + ((-dot c (G w)) • w + dot c w • G w) = c' + ((-dot c' (G w)) • w + dot c' w • G w)
        rw [← Lm_eq, ← Lm_eq]; exact h')
    exact congrArg Prod.fst this
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := mem_C3.1 (mem_CS.1 hx)
    exact ⟨c, mem_CS.2 hc, rfl⟩
  · intro c _; rfl

lemma card_perp : #(perpS (Dsub G C w)) = 9 * #(CS C) := by
  have := S.sum_perp (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_prod,
    ZMod.card] at this
  rw [this]; ring

lemma card_C : #(CS C) = 9 * #(CS (Dsub G C w)) := by
  have h1 : #(CS (Dsub G C w)) * #(perpS (Dsub G C w)) = 3 ^ n := by
    exact_mod_cast card_mul_card_perpS _
  have h2 : #(CS C) * #(CS C) = 3 ^ n := by exact_mod_cast card_sq S.sd
  rw [S.card_perp] at h1
  have hpos : 0 < #(CS C) := Finset.card_pos.2 ⟨0, mem_CS.2 C.zero_mem⟩
  have : #(CS C) * #(CS C) = #(CS C) * (9 * #(CS (Dsub G C w))) := by rw [h2, ← h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

lemma card_C2 : #(CS (C2 G C w)) = #(CS C) := by
  have := S.sum_C2 (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_prod,
    ZMod.card] at this
  rw [this, S.card_C]; ring

lemma card_C3 : #(CS (C3 G C w)) = #(CS C) := by
  have := S.sum_C3 (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
  exact this

lemma iso_C2 : ∀ x ∈ C2 G C w, ∀ y ∈ C2 G C w, dot x y = 0 := by
  intro x hx y hy
  obtain ⟨d, hd, a, b, rfl⟩ := mem_C2.1 hx
  obtain ⟨d', hd', a', b', rfl⟩ := mem_C2.1 hy
  have hd1 := mem_Dsub.1 hd
  have hd2 := mem_Dsub.1 hd'
  rw [dot_add_add, S.dotC hd1.1 hd2.1, dot_comb_right d, hd1.2.1, hd1.2.2, S.dot_W,
    dot_comm _ d', dot_comb_right d', hd2.2.1, hd2.2.2]
  ring

lemma iso_C3 : ∀ x ∈ C3 G C w, ∀ y ∈ C3 G C w, dot x y = 0 := by
  intro x hx y hy
  obtain ⟨c, hc, rfl⟩ := mem_C3.1 hx
  obtain ⟨c', hc', rfl⟩ := mem_C3.1 hy
  rw [Lm_eq, Lm_eq, dot_add_add, S.dotC hc hc', dot_comb_right c, S.dot_W, dot_comm _ c',
    dot_comb_right c']
  ring

lemma selfDual_C2 : IsSelfDual (C2 G C w) := by
  refine selfDual_of_iso_card _ S.iso_C2 ?_
  rw [S.card_C2]; exact_mod_cast card_sq S.sd

lemma selfDual_C3 : IsSelfDual (C3 G C w) := by
  refine selfDual_of_iso_card _ S.iso_C3 ?_
  rw [S.card_C3]; exact_mod_cast card_sq S.sd

lemma G_D {d : Word n} (hd : d ∈ Dsub G C w) : G d ∈ Dsub G C w := by
  rw [mem_Dsub] at hd ⊢
  refine ⟨S.inv d hd.1, ?_, ?_⟩
  · rw [S.hG.dot_G_left_of_Qm d S.wM, hd.2.1, hd.2.2, sub_zero]
  · rw [S.hG.isom, hd.2.1]

lemma inv_C2 : ∀ x ∈ C2 G C w, G x ∈ C2 G C w := by
  intro x hx
  obtain ⟨d, hd, a, b, rfl⟩ := mem_C2.1 hx
  refine mem_C2.2 ⟨G d, S.G_D hd, b, a + b, ?_⟩
  rw [map_add, map_add, map_smul, map_smul, S.hG.G2_of_Qm S.wM, add_smul, smul_add]
  abel

lemma dot_C2_w {x : Word n} (hx : x ∈ C2 G C w) : dot x w = 0 := by
  obtain ⟨d, hd, a, b, rfl⟩ := mem_C2.1 hx
  rw [dot_add_left, (mem_Dsub.1 hd).2.1, S.hG.dot_of_Qm (S.Qm_comb a b) S.wM, add_zero]

/-- The induction measure drops: `C₂ ∩ V₊ ⊊ C ∩ V₊`. -/
lemma measure_lt :
    #(CS (C2 G C w ⊓ LinearMap.ker (Pp G))) < #(CS (C ⊓ LinearMap.ker (Pp G))) := by
  have hsub : CS (C2 G C w ⊓ LinearMap.ker (Pp G)) ⊆ CS (C ⊓ LinearMap.ker (Pp G)) := by
    intro x hx
    obtain ⟨hx2, hxP⟩ := Submodule.mem_inf.1 (mem_CS.1 hx)
    rw [LinearMap.mem_ker] at hxP
    refine mem_CS.2 (Submodule.mem_inf.2 ⟨?_, LinearMap.mem_ker.2 hxP⟩)
    obtain ⟨d, hd, a, b, rfl⟩ := mem_C2.1 hx2
    have hE := Ep_of_Pp hxP
    rw [map_add, Ep_of_Qm (S.Qm_comb a b), add_zero] at hE
    rw [← hE, Ep_apply]
    have hdC := (mem_Dsub.1 hd).1
    exact C.sub_mem (C.add_mem (S.inv _ (S.inv _ (S.inv _ hdC))) (S.inv _ hdC)) hdC
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset hsub).2
    ⟨v, mem_CS.2 (Submodule.mem_inf.2 ⟨S.vC, LinearMap.mem_ker.2 S.vP⟩), fun hv => ?_⟩
  have := S.dot_C2_w (Submodule.mem_inf.1 (mem_CS.1 hv)).1
  rw [S.vw] at this
  exact one_ne_zero this

/-- A maximal word `c + a w + b gw` of `D^⊥` is isotropic: `a (c·w) + b (c·gw) = 0`. -/
lemma line_of_f {c : Word n} (hc : c ∈ C) (a b : F) (hf : f (c + (a • w + b • G w)) ≠ 0) :
    a * dot c w + b * dot c (G w) = 0 := by
  have hmax := max_of_f_ne_zero hf
  have h0 : dot (c + (a • w + b • G w)) (c + (a • w + b • G w)) = 0 := by
    rw [dot_self_of_max hmax]
    exact (ZMod.natCast_eq_zero_iff n 3).2 S.hG.three
  rw [dot_add_add, S.dotC hc hc, dot_comb_right c, S.dot_W, dot_comm _ c,
    dot_comb_right c] at h0
  apply F_add_self
  linear_combination h0

/-- For `c ∈ C \ D` only three words `c + y`, `y ∈ W`, can be maximal: `c`, `c ± L c`. -/
lemma inner_sum {c : Word n} (hc : c ∈ C) (hcD : c ∉ Dsub G C w) :
    ∑ ab : F × F, f (c + (ab.1 • w + ab.2 • G w)) =
      f c + f (c + Lm G w c) + f (c - Lm G w c) := by
  have hpq : ¬ (dot c w = 0 ∧ dot c (G w) = 0) := fun h => hcD (mem_Dsub.2 ⟨hc, h.1, h.2⟩)
  rw [sum_line _ (dot c w) (dot c (G w)) hpq]
  · rw [sub_Lm, Lm_eq]
    simp only [zero_smul, add_zero]
  · intro ab hab
    by_contra hf
    exact hab (S.line_of_f hc ab.1 ab.2 hf)

lemma Lm_G (c : Word n) : Lm G w (G c) = -G (Lm G w c) := by
  rw [Lm_apply, Lm_apply, map_sub, map_smul, map_smul, S.hG.G2_of_Qm S.wM,
    S.hG.dot_G_left_of_Qm c S.wM, S.hG.isom]
  simp only [sub_smul, smul_add]
  abel

/-- `g` maps `C₃` onto `C₄ = {c - L c}`. -/
lemma sum_minus : ∑ c ∈ CS C, f (c - Lm G w c) = ∑ c ∈ CS C, f (c + Lm G w c) := by
  symm
  refine Finset.sum_nbij' (fun c => G c) (fun c => -G (G (G c))) ?_ ?_ ?_ ?_ ?_
  · intro c hc; exact mem_CS.2 (S.inv c (mem_CS.1 hc))
  · intro c hc; exact mem_CS.2 (C.neg_mem (S.inv _ (S.inv _ (S.inv c (mem_CS.1 hc)))))
  · intro c _; simp [S.hG.G4]
  · intro c _; simp [S.hG.G4]
  · intro c _
    show f (c + Lm G w c) = f (G c - Lm G w (G c))
    rw [S.Lm_G, sub_neg_eq_add, ← map_add, S.hG.fG]

/-- `F(D^⊥) = 9 F(D)` (Poisson summation, `f̂ = κⁿ f`, `κⁿ = |C| = 9|D|`). -/
lemma perp_sum : ∑ x ∈ perpS (Dsub G C w), f x = 9 * ∑ d ∈ CS (Dsub G C w), f d := by
  obtain ⟨m, hm⟩ := S.hG.four_dvd
  have hP := poisson_perp (Dsub G C w) (fun x => (f x : ℂ))
  simp_rw [hat_f] at hP
  rw [← Finset.mul_sum] at hP
  have hk : κ ^ n = (#(CS C) : ℂ) := by
    rw [card_eq_pow S.sd hm, congrArg (κ ^ ·) hm, kappa_pow]; push_cast; ring
  rw [hk, S.card_C] at hP
  have hD : (#(CS (Dsub G C w)) : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨0, mem_CS.2 (Dsub G C w).zero_mem⟩).ne'
  push_cast at hP
  have : ((∑ x ∈ perpS (Dsub G C w), f x : ℤ) : ℂ) =
      ((9 * ∑ d ∈ CS (Dsub G C w), f d : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ hD
    linear_combination -hP
  exact_mod_cast this

/-- **The four-code identity** `Index C + Index C₂ + Index C₃ + Index C₄ = 12 F(D)`, with
`Index C₄ = Index C₃`. -/
lemma four_code :
    index C + index (C2 G C w) + 2 * index (C3 G C w) =
      12 * ∑ d ∈ CS (Dsub G C w), f d := by
  classical
  have hfilter : (CS C).filter (fun c => c ∈ Dsub G C w) = CS (Dsub G C w) := by
    ext x
    simp only [Finset.mem_filter, mem_CS]
    exact ⟨fun h => h.2, fun h => ⟨D_le h, h⟩⟩
  have h1 : ∑ c ∈ CS C, ∑ ab : F × F, f (c + (ab.1 • w + ab.2 • G w)) =
      ∑ x ∈ CS (C2 G C w), f x + ∑ c ∈ (CS C).filter (fun c => c ∉ Dsub G C w),
        (f c + f (c + Lm G w c) + f (c - Lm G w c)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (CS C) (fun c => c ∈ Dsub G C w), hfilter,
      S.sum_C2]
    congr 1
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mem_filter] at hc
    exact S.inner_sum (mem_CS.1 hc.1) hc.2
  have h2 : ∑ c ∈ CS C, (f c + f (c + Lm G w c) + f (c - Lm G w c)) =
      3 * ∑ d ∈ CS (Dsub G C w), f d + ∑ c ∈ (CS C).filter (fun c => c ∉ Dsub G C w),
        (f c + f (c + Lm G w c) + f (c - Lm G w c)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (CS C) (fun c => c ∈ Dsub G C w), hfilter,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Lm_of_D (mem_CS.1 hd), add_zero, sub_zero]; ring
  have h3 : ∑ c ∈ CS C, (f c + f (c + Lm G w c) + f (c - Lm G w c)) =
      index C + 2 * index (C3 G C w) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, S.sum_minus]
    unfold index
    rw [S.sum_C3 f]; ring
  have hP := S.perp_sum
  rw [S.sum_perp f, h1] at hP
  have : index (C2 G C w) = ∑ x ∈ CS (C2 G C w), f x := rfl
  linarith

/-- `4 ∣ F(D)`: `⟨g²⟩ ≅ ℤ/4` acts freely on `D \ 0` and preserves `f`. -/
lemma four_dvd_FD : (4 : ℤ) ∣ ∑ d ∈ CS (Dsub G C w), f d := by
  refine four_dvd_sum S.hG.even S.hG.pos (fun x => G (G x)) (fun x => S.hG.G4 x)
    (fun x => by simp only [map_neg]) (fun x => S.hG.f_G2 x) _ ?_ ?_
  · intro x hx; exact mem_CS.2 ((Dsub G C w).neg_mem (mem_CS.1 hx))
  · intro x hx; exact mem_CS.2 (S.G_D (S.G_D (mem_CS.1 hx)))

/-- **The induction step.** If `16 ∣ Index C₂` then `16 ∣ Index C`. -/
theorem step_dvd (h2 : (16 : ℤ) ∣ index (C2 G C w)) : (16 : ℤ) ∣ index C := by
  have hid := S.four_code
  have h3 : (8 : ℤ) ∣ index (C3 G C w) := eight_dvd_index S.selfDual_C3 S.hG.pos
  have h4 := S.four_dvd_FD
  omega

end Setup

end Four

/-! ### The induction -/

variable {G : Module.End F (Word n)}

lemma exists_w (hG : Hyp G) {v : Word n} (hvP : Pp G v = 0) (hv0 : v ≠ 0) :
    ∃ w, Qm G w = 0 ∧ dot v w = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  simp only [Pi.zero_apply] at hi
  have hz : dot v (Pi.single i 1) = v i := by simp [dot, Pi.single_apply]
  have hE : dot v (Ep G (Pi.single i 1)) = 0 := hG.dot_of_Pp hvP (Pp_Ep hG.G4 _)
  refine ⟨v i • (Pi.single i 1 - Ep G (Pi.single i 1)), ?_, ?_⟩
  · rw [map_smul, Qm_sub_Ep hG.G4, smul_zero]
  · rw [dot_smul_right, dot_sub_right, hz, hE, sub_zero]
    exact mul_self_of_ne_zero _ hi

/-- `16 ∣ Index C` for every `G`-invariant self-dual code, by induction on `|C ∩ V₊|`. -/
theorem sixteen_dvd (hG : Hyp G) : ∀ (N : ℕ) (C : Submodule F (Word n)), IsSelfDual C →
    (∀ x ∈ C, G x ∈ C) → #(CS (C ⊓ LinearMap.ker (Pp G))) = N → (16 : ℤ) ∣ index C := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro C hC hCG hN
  by_cases hex : ∃ v ∈ C, Pp G v = 0 ∧ v ≠ 0
  · obtain ⟨v, hvC, hvP, hv0⟩ := hex
    obtain ⟨w, hwM, hvw⟩ := exists_w hG hvP hv0
    have S : Setup G C v w := ⟨hG, hC, hCG, hvC, hvP, hwM, hvw⟩
    exact S.step_dvd (ih _ (hN ▸ S.measure_lt) _ S.selfDual_C2 S.inv_C2 rfl)
  · push Not at hex
    have hI : index C = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      by_contra hf
      have hxC := mem_CS.1 hx
      have hEC : Ep G x ∈ C := by
        rw [Ep_apply]
        exact C.sub_mem (C.add_mem (hCG _ (hCG _ (hCG _ hxC))) (hCG _ hxC)) hxC
      have hE : Ep G x = 0 := hex _ hEC (Pp_Ep hG.G4 x)
      have hQ := Qm_sub_Ep hG.G4 x
      rw [hE, sub_zero] at hQ
      exact hG.noMax x hQ (max_of_f_ne_zero hf)
    rw [hI]; exact dvd_zero _

theorem sixteen_dvd_index (hG : Hyp G) {C : Submodule F (Word n)} (hC : IsSelfDual C)
    (hCG : ∀ x ∈ C, G x ∈ C) : (16 : ℤ) ∣ index C :=
  sixteen_dvd hG _ C hC hCG rfl

/-! ### Signed permutations with `g⁴ = -1` -/

section SignedPerm

/-- Counting over the orbits of a permutation with all cycles of length `4`: a `π`-invariant
set `S` has `4 ∣ |S|`, and `∏_S σ = (-1)^(|S|/4)` if `σ` has product `-1` along every cycle. -/
lemma orbit_count (π : Equiv.Perm (Fin n)) (σ : Fin n → ℤ)
    (h4 : ∀ i, π (π (π (π i))) = i) (h1 : ∀ i, π i ≠ i) (h2 : ∀ i, π (π i) ≠ i)
    (hσ : ∀ i, σ i * σ (π i) * σ (π (π i)) * σ (π (π (π i))) = -1) :
    ∀ (N : ℕ) (S : Finset (Fin n)), #S = N → (∀ i ∈ S, π i ∈ S) →
      4 ∣ #S ∧ ∏ i ∈ S, σ i = (-1) ^ (#S / 4) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro S hN hS
  rcases S.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp
  have e01 : i ≠ π i := (h1 i).symm
  have e02 : i ≠ π (π i) := (h2 i).symm
  have e03 : i ≠ π (π (π i)) := fun h => h1 i (by have h' := congrArg π h; rwa [h4] at h')
  have e12 : π i ≠ π (π i) := fun h => e01 (π.injective h)
  have e13 : π i ≠ π (π (π i)) := fun h => e02 (π.injective h)
  have e23 : π (π i) ≠ π (π (π i)) := fun h => e12 (π.injective h)
  have hO : ({i, π i, π (π i), π (π (π i))} : Finset (Fin n)) ⊆ S := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact hi
    · exact hS _ hi
    · exact hS _ (hS _ hi)
    · exact hS _ (hS _ (hS _ hi))
  have hcardO : #({i, π i, π (π i), π (π (π i))} : Finset (Fin n)) = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair e23]
    all_goals simp [e01, e02, e03, e12, e13]
  have hprodO : ∏ j ∈ ({i, π i, π (π i), π (π (π i))} : Finset (Fin n)), σ j = -1 := by
    rw [Finset.prod_insert, Finset.prod_insert, Finset.prod_pair e23, ← hσ i]
    · ring
    all_goals simp [e01, e02, e03, e12, e13]
  have hS' : ∀ j ∈ S \ {i, π i, π (π i), π (π (π i))},
      π j ∈ S \ {i, π i, π (π i), π (π (π i))} := by
    intro j hj
    rw [Finset.mem_sdiff] at hj ⊢
    refine ⟨hS j hj.1, fun hjO => hj.2 ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjO ⊢
    rcases hjO with h | h | h | h
    · right; right; right
      have := congrArg (fun k => π (π (π k))) h
      simp only [h4] at this
      exact this
    · left; exact π.injective h
    · right; left; exact π.injective h
    · right; right; left; exact π.injective h
  have hcard := Finset.card_sdiff_add_card_eq_card hO
  rw [hcardO] at hcard
  obtain ⟨hd, hp⟩ := ih _ (by omega) _ rfl hS'
  refine ⟨by omega, ?_⟩
  rw [← Finset.prod_sdiff hO, hp, hprodO, ← hcard,
    show (#(S \ {i, π i, π (π i), π (π (π i))}) + 4) / 4 =
      #(S \ {i, π i, π (π i), π (π (π i))}) / 4 + 1 by omega, pow_succ]

variable (g : Ex.SP (Fin n))

/-- A signed permutation as a linear map. -/
def actL : Module.End F (Word n) where
  toFun := g.act
  map_add' := g.act_add
  map_smul' c x := g.act_smul c x

lemma actL_apply (x : Word n) : actL g x = g.act x := rfl

lemma dot_act (x y : Word n) : dot (g.act x) (g.act y) = dot x y := by
  unfold dot
  rw [← Equiv.sum_comp g.perm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ex.SP.act_perm, Ex.SP.act_perm]
  linear_combination (x i * y i) * g.sgn_sq i

/-- The sign `ε(g) = ∏ sgn ∈ {±1}`. -/
def eps : ℤ := ∏ i, -phi (g.sgn i)

lemma phi_mul_sgn : ∀ s a : F, s ≠ 0 → phi (s * a) = -phi s * phi a := by decide

/-- `f(g x) = ε(g) f(x)`. -/
lemma f_act (x : Word n) : f (g.act x) = eps g * f x := by
  unfold f eps
  rw [← Equiv.prod_comp g.perm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Ex.SP.act_perm, phi_mul_sgn _ _ (g.sgn_ne_zero i)]

variable {g}

lemma act_four (h4 : g ^ 4 = -1) (x : Word n) : g.act (g.act (g.act (g.act x))) = -x := by
  have := congrArg (fun h => Ex.SP.act h x) h4
  simpa [pow_succ, Ex.SP.act_mul, Ex.SP.act_one, Ex.SP.act_neg] using this

lemma perm_four (h4 : g ^ 4 = -1) (i : Fin n) : g.perm (g.perm (g.perm (g.perm i))) = i := by
  have := congrArg (fun h => h.perm i) h4
  simpa [pow_succ] using this

lemma sgn_four (h4 : g ^ 4 = -1) (i : Fin n) :
    g.sgn i * g.sgn (g.perm i) * g.sgn (g.perm (g.perm i)) *
      g.sgn (g.perm (g.perm (g.perm i))) = -1 := by
  have := congrArg (fun h => h.sgn i) h4
  simp [pow_succ] at this
  linear_combination this

lemma F_sq_sq : ∀ a b : F, a * a = 1 → b * b = 1 → a * b * a * b ≠ -1 := by decide

lemma perm_ne (h4 : g ^ 4 = -1) (i : Fin n) : g.perm i ≠ i := by
  intro h
  have := sgn_four h4 i
  simp only [h] at this
  exact F_sq_sq _ _ (g.sgn_sq i) (g.sgn_sq i) this

lemma perm_two_ne (h4 : g ^ 4 = -1) (i : Fin n) : g.perm (g.perm i) ≠ i := by
  intro h
  have := sgn_four h4 i
  rw [h] at this
  exact F_sq_sq _ _ (g.sgn_sq i) (g.sgn_sq (g.perm i)) this

lemma F_sign4 : ∀ a b c d : F, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → a * b * c * d = -1 →
    -phi a * -phi b * -phi c * -phi d = -1 := by decide

/-- `g⁴ = -1` forces all cycles to have length `4`: `4 ∣ n` and `ε(g) = (-1)^(n/4)`. -/
lemma eps_eq (h4 : g ^ 4 = -1) : 4 ∣ n ∧ eps g = (-1) ^ (n / 4) := by
  have hσ : ∀ i, -phi (g.sgn i) * -phi (g.sgn (g.perm i)) * -phi (g.sgn (g.perm (g.perm i))) *
      -phi (g.sgn (g.perm (g.perm (g.perm i)))) = -1 := fun i =>
    F_sign4 _ _ _ _ (g.sgn_ne_zero _) (g.sgn_ne_zero _) (g.sgn_ne_zero _) (g.sgn_ne_zero _)
      (sgn_four h4 i)
  have := orbit_count g.perm (fun i => -phi (g.sgn i)) (perm_four h4) (perm_ne h4)
    (perm_two_ne h4) hσ _ univ rfl (fun i _ => Finset.mem_univ _)
  simpa [eps] using this

lemma F_noMax : ∀ s t a b c : F, s ≠ 0 → t ≠ 0 → a ≠ 0 → b ≠ 0 → c ≠ 0 →
    t * (s * a) - t * b - c = 0 → s * a = -b := by decide

/-- `V₋` contains no maximal word: on such a word `g` would act as `-1`. -/
lemma noMax_act (hn : 0 < n) (x : Word n) (hx : Qm (actL g) x = 0) : ¬ ∀ i, x i ≠ 0 := by
  intro hmax
  rw [Qm_apply] at hx
  simp only [actL_apply] at hx
  have hneg : g.act x = -x := by
    funext j
    obtain ⟨i, rfl⟩ := g.perm.surjective j
    have h := congrFun hx (g.perm (g.perm i))
    simp only [Pi.sub_apply, Pi.zero_apply, Ex.SP.act_perm] at h
    rw [Ex.SP.act_perm, Pi.neg_apply]
    exact F_noMax _ _ _ _ _ (g.sgn_ne_zero i) (g.sgn_ne_zero _) (hmax i) (hmax _) (hmax _) h
  rw [hneg, Ex.SP.act_neg_word, hneg, neg_neg] at hx
  have h0 : x = 0 := by
    funext j
    have := congrFun hx j
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at this ⊢
    linear_combination this
  exact hmax ⟨0, hn⟩ (by rw [h0]; rfl)

end SignedPerm

/-! ### Theorem D -/

/-- **Theorem D** (`paper/conj14.tex`). Let `C` be a self-dual ternary code of length `n > 0` and
`g` a signed permutation with `g C ⊆ C` and `g⁴ = -1`. Then `4 ∣ n`, `48 ∣ Index(C)`, and
`Index(C) = 0` if `n/4` is odd. -/
theorem theoremD (C : Submodule F (Word n)) (hC : IsSelfDual C) (hn : 0 < n)
    (g : Ex.SP (Fin n)) (hgC : g.Inv C) (h4 : g ^ 4 = -1) :
    4 ∣ n ∧ (48 : ℤ) ∣ gjfIndex C ∧ (Odd (n / 4) → gjfIndex C = 0) := by
  obtain ⟨h4n, heps⟩ := eps_eq h4
  have hinv : eps g * index C = index C := by
    unfold index
    rw [Finset.mul_sum]
    simp_rw [← f_act]
    refine Finset.sum_nbij' (fun x => g.act x) (fun x => -g.act (g.act (g.act x))) ?_ ?_ ?_ ?_
      (fun _ _ => rfl)
    · intro x hx; exact mem_CS.2 (hgC x (mem_CS.1 hx))
    · intro x hx; exact mem_CS.2 (C.neg_mem (hgC _ (hgC _ (hgC _ (mem_CS.1 hx)))))
    · intro x _; simp [act_four h4]
    · intro x _; simp [Ex.SP.act_neg_word, act_four h4]
  have hodd : Odd (n / 4) → index C = 0 := by
    intro ho
    rw [heps, ho.neg_one_pow] at hinv
    linarith
  rw [gjfIndex_eq]
  refine ⟨h4n, ?_, hodd⟩
  rcases Nat.even_or_odd (n / 4) with he | ho
  · by_cases hI : index C = 0
    · rw [hI]; exact dvd_zero _
    obtain ⟨x0, hx0, hmax⟩ := exists_max_of_index_ne_zero hI
    have hG : Hyp (actL g) :=
      { pos := hn
        three := three_dvd_of_max hC hx0 hmax
        four_dvd := h4n
        isom := dot_act g
        four := LinearMap.ext fun x => by
          rw [pow_four_apply]; simp [actL_apply, act_four h4]
        fG := fun x => by rw [actL_apply, f_act, heps, he.neg_one_pow, one_mul]
        noMax := noMax_act hn }
    have h16 := sixteen_dvd_index hG hC hgC
    have h24 := index_dvd_24 C hC hn
    rw [gjfIndex_eq] at h24
    omega
  · rw [hodd ho]; exact dvd_zero _

/-- Theorem D in the paper's form: length `12k`, `48 ∣ Index`, and `Index = 0` for odd `k`. -/
theorem theoremD_twelve (k : ℕ) (hk : 1 ≤ k) (C : Submodule F (Word (12 * k)))
    (hC : IsSelfDual C) (g : Ex.SP (Fin (12 * k))) (hgC : g.Inv C) (h4 : g ^ 4 = -1) :
    (48 : ℤ) ∣ gjfIndex C ∧ (Odd k → gjfIndex C = 0) := by
  obtain ⟨-, h48, hodd⟩ := theoremD C hC (by omega) g hgC h4
  refine ⟨h48, fun hk' => hodd ?_⟩
  rw [show 12 * k / 4 = 3 * k by omega]
  exact Nat.odd_mul.2 ⟨by decide, hk'⟩

/-- In particular, a self-dual code of index `±24` has no automorphism `g` with `g⁴ = -1`
(the hypothesis of [GJF, Thm 5.6] fails for `8 ∣ k`, see the paper). -/
theorem index_ne_24 (C : Submodule F (Word n)) (hC : IsSelfDual C) (hn : 0 < n)
    (g : Ex.SP (Fin n)) (hgC : g.Inv C) (h4 : g ^ 4 = -1) :
    gjfIndex C ≠ 24 ∧ gjfIndex C ≠ -24 := by
  obtain ⟨-, h48, -⟩ := theoremD C hC hn g hgC h4
  constructor <;> intro h <;> rw [h] at h48 <;> norm_num at h48

/-! ### Non-vacuity: the hypotheses hold for the tetracode -/

/-- `g = (x₀,x₁,x₂,x₃) ↦ (x₃, x₀, -x₁, x₂)`, of order `8` with `g⁴ = -1`. -/
def g8 : Ex.SP (Fin 4) := ⟨finRotate 4, ![1, 2, 1, 1], by decide⟩

lemma g8_four : g8 ^ 4 = -1 := by decide

set_option maxRecDepth 100000 in
lemma g8_inv : g8.Inv Sanity.tetra := by
  show ∀ x : Word 4, (dot x Sanity.t1 = 0 ∧ dot x Sanity.t2 = 0) →
    dot (g8.act x) Sanity.t1 = 0 ∧ dot (g8.act x) Sanity.t2 = 0
  decide

/-- Theorem D applies to the tetracode (`n/4 = 1` is odd, so its index is `0`). -/
example : gjfIndex Sanity.tetra = 0 :=
  (theoremD Sanity.tetra Sanity.tetra_selfDual (by norm_num) g8 g8_inv g8_four).2.2
    (by decide)

end GJF.Obs
