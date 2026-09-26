import Mathlib

/-!
# The index of a self-dual ternary code is divisible by 24

A formalization of the finite proof (route C of `paper/divisibility.tex`, notes §2 Step 1′).

* `GJF.gjfIndex C` is the index of Gaiotto–Johnson-Freyd: the number of even minus the number of
  odd maximal codewords (maximal = no zero entry, parity = number of entries equal to `1`).
* `GJF.design`: the signed maximal codewords form a 2-design,
  `∑_{x ∈ C} f(x) φ(x_i) φ(x_j) = 0` for `i ≠ j`. Proof: Poisson summation over `C = C^⊥`
  for `g_ij(x) = ∏_{k ≠ i,j} φ(x_k) · [x_i ≠ 0][x_j ≠ 0]`, whose Fourier transform is
  `κ^(n-2) g_ij` on every word of a self-orthogonal code when `3 ∣ n` (`κ = ω - ω²`, `κ² = -3`).
* `GJF.eight_dvd_index`, `GJF.three_dvd_index`: the two counting arguments.
* `GJF.index_dvd_24`: `24 ∣ gjfIndex C` for every self-dual ternary code of positive length.
  (At length `0` the empty word is an even maximal codeword and the index is `1`.)
-/

open Finset

namespace GJF

/-- Words of length `n` over `𝔽₃`. -/
abbrev Word (n : ℕ) := Fin n → ZMod 3

variable {n : ℕ}

/-! ### Basic definitions -/

/-- The standard dot product on `𝔽₃ⁿ`. -/
def dot (x y : Word n) : ZMod 3 := ∑ k, x k * y k

lemma dot_comm (x y : Word n) : dot x y = dot y x := by
  simp [dot, mul_comm]

lemma dot_add_left (x y z : Word n) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

/-- Self-duality for the standard dot product: `C = C^⊥`. -/
def IsSelfDual (C : Submodule (ZMod 3) (Word n)) : Prop :=
  ∀ x : Word n, x ∈ C ↔ ∀ c ∈ C, dot x c = 0

/-- `φ(0) = 0`, `φ(1) = -1`, `φ(2) = 1`. -/
def phi (a : ZMod 3) : ℤ := if a = 0 then 0 else if a = 1 then -1 else 1

/-- `ι(a) = [a ≠ 0]`. -/
def iota (a : ZMod 3) : ℤ := if a = 0 then 0 else 1

/-- `f(x) = ∏ φ(x_k)`. -/
def f (x : Word n) : ℤ := ∏ k, phi (x k)

/-- The codewords of `C`, as a finset. -/
noncomputable def CS (C : Submodule (ZMod 3) (Word n)) : Finset (Word n) := by
  classical exact univ.filter (· ∈ C)

lemma mem_CS {C : Submodule (ZMod 3) (Word n)} {x : Word n} : x ∈ CS C ↔ x ∈ C := by
  classical simp [CS]

/-- `Σ_{x ∈ C} f(x)`. -/
noncomputable def index (C : Submodule (ZMod 3) (Word n)) : ℤ := ∑ x ∈ CS C, f x

/-- The number of entries equal to `1`. -/
def ones (x : Word n) : ℕ := #(univ.filter fun k => x k = 1)

/-- The index of Gaiotto–Johnson-Freyd: even minus odd maximal codewords. -/
noncomputable def gjfIndex (C : Submodule (ZMod 3) (Word n)) : ℤ :=
  (#((CS C).filter fun x => (∀ k, x k ≠ 0) ∧ Even (ones x)) : ℤ) -
    #((CS C).filter fun x => (∀ k, x k ≠ 0) ∧ Odd (ones x))

/-! ### Facts about `𝔽₃` -/

lemma zmod3_cases (b : ZMod 3) : b = 0 ∨ b = 1 ∨ b = 2 := by
  revert b; decide

lemma phi_neg (a : ZMod 3) : phi (-a) = -phi a := by
  revert a; decide

lemma phi_ne_zero_iff (a : ZMod 3) : phi a ≠ 0 ↔ a ≠ 0 := by
  revert a; decide

lemma iota_ne_zero_iff (a : ZMod 3) : iota a ≠ 0 ↔ a ≠ 0 := by
  revert a; decide

lemma iota_eq_phi_mul_phi (a : ZMod 3) : iota a = phi a * phi a := by
  revert a; decide

lemma phi_of_ne_zero (a : ZMod 3) (ha : a ≠ 0) : phi a = if a = 1 then -1 else 1 := by
  revert a; decide

lemma phi_sq_of_ne_zero (a : ZMod 3) (ha : a ≠ 0) : phi a * phi a = 1 := by
  revert a; decide

lemma mul_self_of_ne_zero (a : ZMod 3) (ha : a ≠ 0) : a * a = 1 := by
  revert a; decide

lemma cast_neg_phi (a : ZMod 3) : ((-phi a : ℤ) : ZMod 3) = a := by
  rcases zmod3_cases a with rfl | rfl | rfl <;> decide

lemma neg_eq_one_iff (b : ZMod 3) : -b = 1 ↔ b = 2 := by
  revert b; decide

/-- The only way to get `a² + b² + 1 = 0` in `𝔽₃` is with `a, b ≠ 0`. -/
lemma sq_add_sq_add_one (a b : ZMod 3) (h : a * a + b * b + 1 = 0) : a ≠ 0 ∧ b ≠ 0 := by
  revert a b; decide

/-- `4·[p = q = r] = 1 + φpφq + φpφr + φqφr` for nonzero `p, q, r`. -/
lemma key3 (p q r : ZMod 3) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    (if p = q ∧ q = r then (4 : ℤ) else 0) = 1 + phi p * phi q + phi p * phi r + phi q * phi r := by
  revert p q r; decide

/-! ### The cube root of unity and the additive character `ψ` -/

/-- `ω = e^{2πi/3}`. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

lemma ω_prim : IsPrimitiveRoot ω 3 := by
  simpa [ω] using Complex.isPrimitiveRoot_exp 3 (by norm_num)

lemma ω_cube : ω ^ 3 = 1 := ω_prim.pow_eq_one

lemma ω_sum : 1 + ω + ω ^ 2 = 0 := by
  have h := ω_prim.geom_sum_eq_zero (by norm_num : 1 < 3)
  simpa [Finset.sum_range_succ] using h

lemma ω_ne_one : ω ≠ 1 := ω_prim.ne_one (by norm_num)

lemma ω_sq_ne_one : ω ^ 2 ≠ 1 := ω_prim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)

/-- `κ = ω - ω² = i√3`. -/
noncomputable def κ : ℂ := ω - ω ^ 2

lemma κ_sq : κ ^ 2 = -3 := by
  unfold κ
  linear_combination (ω - 2) * ω_cube + ω_sum

/-- The additive character `ψ(a) = ω^a` of `𝔽₃`. -/
noncomputable def ψ (a : ZMod 3) : ℂ := ω ^ a.val

lemma ψ_zero : ψ 0 = 1 := by simp [ψ]

lemma ψ_one : ψ 1 = ω := by
  simp [ψ, show (1 : ZMod 3).val = 1 from rfl]

lemma ψ_two : ψ 2 = ω ^ 2 := by
  simp [ψ, show (2 : ZMod 3).val = 2 from rfl]

lemma pow_mod_three (m : ℕ) : ω ^ (m % 3) = ω ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, ω_cube, one_pow, mul_one]

lemma ψ_add (a b : ZMod 3) : ψ (a + b) = ψ a * ψ b := by
  simp only [ψ, ZMod.val_add, pow_mod_three, pow_add]

lemma ψ_sum {ι : Type*} (s : Finset ι) (g : ι → ZMod 3) :
    ψ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ψ_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ψ_add, ih]

lemma ψ_ne_one {a : ZMod 3} (ha : a ≠ 0) : ψ a ≠ 1 := by
  rcases zmod3_cases a with rfl | rfl | rfl
  · exact absurd rfl ha
  · rw [ψ_one]; exact ω_ne_one
  · rw [ψ_two]; exact ω_sq_ne_one

lemma sum_zmod3 (F : ZMod 3 → ℂ) : ∑ a, F a = F 0 + F 1 + F 2 := by
  rw [show (univ : Finset (ZMod 3)) = {0, 1, 2} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

lemma two_mul_two : (2 : ZMod 3) * 2 = 1 := by decide

@[simp] lemma two_ne_zero3 : (2 : ZMod 3) ≠ 0 := by decide
@[simp] lemma two_ne_one3 : (2 : ZMod 3) ≠ 1 := by decide
@[simp] lemma one_ne_zero3 : (1 : ZMod 3) ≠ 0 := by decide
@[simp] lemma one_ne_two3 : (1 : ZMod 3) ≠ 2 := by decide

/-- `φ̂ = κ φ`. -/
lemma phi_hat (b : ZMod 3) : ∑ a, (phi a : ℂ) * ψ (b * a) = κ * phi b := by
  rw [sum_zmod3]
  rcases zmod3_cases b with rfl | rfl | rfl <;>
    simp [phi, κ, ψ_zero, ψ_one, ψ_two, two_mul_two] <;> ring1

/-- `ι̂(b) = 2` for `b = 0` and `-1` otherwise. -/
lemma iota_hat (b : ZMod 3) :
    ∑ a, (iota a : ℂ) * ψ (b * a) = if b = 0 then 2 else -1 := by
  rw [sum_zmod3]
  rcases zmod3_cases b with rfl | rfl | rfl <;>
    simp [iota, ψ_zero, ψ_one, ψ_two, two_mul_two] <;>
    first | ring1 | linear_combination ω_sum

/-- `1̂(b) = 3` for `b = 0` and `0` otherwise. -/
lemma one_hat (b : ZMod 3) : ∑ a, (1 : ℂ) * ψ (b * a) = if b = 0 then 3 else 0 := by
  rw [sum_zmod3]
  rcases zmod3_cases b with rfl | rfl | rfl <;>
    simp [ψ_zero, ψ_one, ψ_two, two_mul_two] <;>
    first | ring1 | linear_combination ω_sum

/-! ### Fourier transform and Poisson summation -/

/-- `ĥ(u) = Σ_x h(x) ψ(u·x)`. -/
noncomputable def hat (h : Word n → ℂ) (u : Word n) : ℂ := ∑ x, h x * ψ (dot u x)

/-- The transform of a product function is the product of the one-variable transforms. -/
lemma hat_prod (h : Fin n → ZMod 3 → ℂ) (u : Word n) :
    hat (fun x => ∏ k, h k (x k)) u = ∏ k, ∑ a, h k a * ψ (u k * a) := by
  rw [Fintype.prod_sum]
  simp only [hat]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dot, ψ_sum, ← Finset.prod_mul_distrib]

variable {C : Submodule (ZMod 3) (Word n)}

lemma dot_eq_zero_of_mem (hC : IsSelfDual C) {x y : Word n} (hx : x ∈ C) (hy : y ∈ C) :
    dot x y = 0 :=
  (hC x).1 hx y hy

/-- Orthogonality of characters over a self-dual code. -/
lemma charsum (hC : IsSelfDual C) (x : Word n) :
    ∑ u ∈ CS C, ψ (dot u x) = if x ∈ CS C then (#(CS C) : ℂ) else 0 := by
  split_ifs with hx
  · have h1 : ∀ u ∈ CS C, ψ (dot u x) = 1 := fun u hu => by
      rw [dot_eq_zero_of_mem hC (mem_CS.1 hu) (mem_CS.1 hx), ψ_zero]
    rw [Finset.sum_congr rfl h1]
    simp
  · obtain ⟨c, hc, hcx⟩ : ∃ c ∈ C, dot x c ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (mem_CS.2 ((hC x).2 h))
    have hshift : ∑ u ∈ CS C, ψ (dot (u + c) x) = ∑ u ∈ CS C, ψ (dot u x) := by
      refine Finset.sum_nbij' (fun u => u + c) (fun u => u - c) ?_ ?_ ?_ ?_ ?_
      · intro u hu; exact mem_CS.2 (C.add_mem (mem_CS.1 hu) hc)
      · intro u hu; exact mem_CS.2 (C.sub_mem (mem_CS.1 hu) hc)
      · intro u _; simp
      · intro u _; simp
      · intro u _; rfl
    simp_rw [dot_add_left, ψ_add, ← Finset.sum_mul] at hshift
    have hne : ψ (dot c x) ≠ 1 := ψ_ne_one (by rwa [dot_comm])
    have h1 : (∑ u ∈ CS C, ψ (dot u x)) * (ψ (dot c x) - 1) = 0 := by
      rw [mul_sub, hshift, mul_one, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne

/-- Poisson summation over a self-dual code: `Σ_{u ∈ C} ĥ(u) = |C| Σ_{x ∈ C} h(x)`. -/
lemma poisson (hC : IsSelfDual C) (h : Word n → ℂ) :
    ∑ u ∈ CS C, hat h u = (#(CS C) : ℂ) * ∑ x ∈ CS C, h x := by
  simp only [hat]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, charsum hC, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

lemma hat_one (u : Word n) : hat (fun _ => (1 : ℂ)) u = if u = 0 then 3 ^ n else 0 := by
  have h := hat_prod (fun _ _ => (1 : ℂ)) u
  simp only [Finset.prod_const_one] at h
  rw [h]
  simp_rw [one_hat]
  split_ifs with hu
  · subst hu; simp
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 hu
    simp only [Pi.zero_apply] at hk
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

/-- `|C|² = 3ⁿ` for a self-dual code (Poisson summation of the constant function). -/
lemma card_sq (hC : IsSelfDual C) : (#(CS C) : ℂ) * #(CS C) = 3 ^ n := by
  have h := poisson hC (fun _ => (1 : ℂ))
  simp_rw [hat_one] at h
  simp only [Finset.sum_ite_eq', mem_CS.2 C.zero_mem, ite_true, Finset.sum_const, nsmul_eq_mul,
    mul_one] at h
  exact h.symm

/-! ### The function `g_ij` and the pointwise identity -/

/-- `g_T(x) = ∏_{k ∉ T} φ(x_k) · ∏_{k ∈ T} [x_k ≠ 0]`. -/
def g (T : Finset (Fin n)) (x : Word n) : ℤ := ∏ k, if k ∈ T then iota (x k) else phi (x k)

lemma f_mul_phi_mul_phi {i j : Fin n} (hij : i ≠ j) (x : Word n) :
    f x * phi (x i) * phi (x j) = g {i, j} x := by
  have h : ∀ k, (if k ∈ ({i, j} : Finset (Fin n)) then iota (x k) else phi (x k))
      = phi (x k) * (if k ∈ ({i, j} : Finset (Fin n)) then phi (x k) else 1) := by
    intro k; split_ifs <;> simp [iota_eq_phi_mul_phi]
  rw [g, Finset.prod_congr rfl (fun k _ => h k), Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.univ_inter, Finset.prod_pair hij, f, mul_assoc]

/-- The coordinate factors of `g_T`, as complex functions. -/
noncomputable def gfac (T : Finset (Fin n)) (k : Fin n) (a : ZMod 3) : ℂ :=
  ((if k ∈ T then iota a else phi a : ℤ) : ℂ)

lemma hat_g (T : Finset (Fin n)) (u : Word n) :
    hat (fun x => (g T x : ℂ)) u =
      ∏ k, if k ∈ T then (if u k = 0 then (2 : ℂ) else -1) else κ * phi (u k) := by
  have e : (fun x => (g T x : ℂ)) = fun x => ∏ k, gfac T k (x k) := by
    funext x; simp [g, gfac]
  rw [e, hat_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k ∈ T
  · simp only [gfac, hk, ite_true]; exact iota_hat (u k)
  · simp only [gfac, hk, ite_false]; exact phi_hat (u k)

lemma card_compl_pair {i j : Fin n} (hij : i ≠ j) :
    #(univ.filter fun k => k ∉ ({i, j} : Finset (Fin n))) + 2 = n := by
  have h := Finset.card_filter_add_card_filter_not (s := univ)
    (fun k => k ∈ ({i, j} : Finset (Fin n)))
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_pair hij, Finset.card_univ,
    Fintype.card_fin] at h
  omega

lemma two_three_aux (m : ZMod 3) (h : m + 2 = 0) : m = 1 := by
  revert m; decide

/-- The weight argument: a word of a self-orthogonal code that is nonzero off `{i, j}` is also
nonzero at `i` and `j`, because its weight is divisible by `3` and so is `n`. -/
lemma weight_lemma (hC : IsSelfDual C) (h3 : 3 ∣ n) {i j : Fin n} (hij : i ≠ j) {u : Word n}
    (hu : u ∈ C) (hz : ∀ k, k ∉ ({i, j} : Finset (Fin n)) → u k ≠ 0) : u i ≠ 0 ∧ u j ≠ 0 := by
  apply sq_add_sq_add_one
  have h0 : dot u u = 0 := dot_eq_zero_of_mem hC hu hu
  have hsplit : dot u u = u i * u i + u j * u j +
      (#(univ.filter fun k => k ∉ ({i, j} : Finset (Fin n))) : ZMod 3) := by
    rw [dot, ← Finset.sum_filter_add_sum_filter_not univ (fun k => k ∈ ({i, j} : Finset (Fin n))),
      Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_pair hij]
    congr 1
    rw [Finset.sum_congr rfl fun k hk => mul_self_of_ne_zero (u k) (hz k (Finset.mem_filter.1 hk).2)]
    simp
  have hm : (#(univ.filter fun k => k ∉ ({i, j} : Finset (Fin n))) : ZMod 3) = 1 := by
    apply two_three_aux
    have h := congrArg (fun m : ℕ => (m : ZMod 3)) (card_compl_pair hij)
    simp only [Nat.cast_add, Nat.cast_ofNat] at h
    rw [h]
    exact (ZMod.natCast_eq_zero_iff n 3).2 h3
  rw [hsplit, hm] at h0
  exact h0

/-- The pointwise identity `ĝ(u) = κ^(n-2) g(u)` on a self-dual code, when `3 ∣ n`. -/
lemma hat_g_eq (hC : IsSelfDual C) (h3 : 3 ∣ n) {i j : Fin n} (hij : i ≠ j) {u : Word n}
    (hu : u ∈ C) :
    (∏ k, if k ∈ ({i, j} : Finset (Fin n)) then (if u k = 0 then (2 : ℂ) else -1)
        else κ * phi (u k)) =
      κ ^ #(univ.filter fun k => k ∉ ({i, j} : Finset (Fin n))) * (g {i, j} u : ℂ) := by
  by_cases hz : ∃ k, k ∉ ({i, j} : Finset (Fin n)) ∧ u k = 0
  · obtain ⟨k, hkT, hk0⟩ := hz
    have h1 : (∏ k, if k ∈ ({i, j} : Finset (Fin n)) then (if u k = 0 then (2 : ℂ) else -1)
        else κ * phi (u k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hkT, hk0, phi])
    have h2 : g {i, j} u = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hkT, hk0, phi])
    rw [h1, h2]
    simp
  · push Not at hz
    have hij0 := weight_lemma hC h3 hij hu hz
    have hfac : ∀ k, (if k ∈ ({i, j} : Finset (Fin n)) then (if u k = 0 then (2 : ℂ) else -1)
        else κ * phi (u k)) = (if k ∈ ({i, j} : Finset (Fin n)) then (-1 : ℂ) else κ) *
          ((if k ∈ ({i, j} : Finset (Fin n)) then iota (u k) else phi (u k) : ℤ) : ℂ) := by
      intro k
      by_cases hk : k ∈ ({i, j} : Finset (Fin n))
      · have hk0 : u k ≠ 0 := by
          rw [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact hij0.1
          · exact hij0.2
        simp [hk, hk0, iota]
      · simp [hk]
    rw [Finset.prod_congr rfl (fun k _ => hfac k), Finset.prod_mul_distrib, Finset.prod_ite,
      Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_pair hij, g, Int.cast_prod]
    ring

lemma three_pow_ne (m : ℕ) : (3 : ℂ) ^ (m + 2) ≠ (-3) ^ m := by
  intro h
  have h' : ((3 : ℤ) ^ (m + 2) : ℤ) = (-3) ^ m := by exact_mod_cast h
  have h'' := congrArg Int.natAbs h'
  simp only [Int.natAbs_pow] at h''
  have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h''
  omega

lemma max_of_f_ne_zero {x : Word n} (h : f x ≠ 0) : ∀ k, x k ≠ 0 := by
  intro k
  have := (Finset.prod_ne_zero_iff.1 h) k (Finset.mem_univ k)
  exact (phi_ne_zero_iff _).1 this

lemma max_of_g_ne_zero {T : Finset (Fin n)} {x : Word n} (h : g T x ≠ 0) : ∀ k, x k ≠ 0 := by
  intro k
  have := (Finset.prod_ne_zero_iff.1 h) k (Finset.mem_univ k)
  split_ifs at this
  · exact (iota_ne_zero_iff _).1 this
  · exact (phi_ne_zero_iff _).1 this

lemma dot_self_of_max {x : Word n} (h : ∀ k, x k ≠ 0) : dot x x = n := by
  rw [dot, Finset.sum_congr rfl fun k _ => mul_self_of_ne_zero (x k) (h k)]
  simp

/-- A self-dual code with a maximal codeword has length divisible by `3`. -/
lemma three_dvd_of_max (hC : IsSelfDual C) {x : Word n} (hx : x ∈ C) (h : ∀ k, x k ≠ 0) :
    3 ∣ n := by
  have h0 := dot_eq_zero_of_mem hC hx hx
  rw [dot_self_of_max h] at h0
  exact (ZMod.natCast_eq_zero_iff n 3).1 h0

/-! ### The signed 2-design -/

/-- **The signed 2-design.** For a self-dual ternary code and `i ≠ j`,
`Σ_{x ∈ C} f(x) φ(x_i) φ(x_j) = 0`. -/
theorem design (hC : IsSelfDual C) {i j : Fin n} (hij : i ≠ j) :
    ∑ x ∈ CS C, f x * phi (x i) * phi (x j) = 0 := by
  simp_rw [f_mul_phi_mul_phi hij]
  by_cases h3 : 3 ∣ n
  · have hP := poisson hC (fun x => (g {i, j} x : ℂ))
    have hL : ∑ u ∈ CS C, hat (fun x => (g {i, j} x : ℂ)) u =
        κ ^ #(univ.filter fun k => k ∉ ({i, j} : Finset (Fin n))) *
          ((∑ x ∈ CS C, g {i, j} x : ℤ) : ℂ) := by
      rw [Int.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [hat_g, hat_g_eq hC h3 hij (mem_CS.1 hu)]
    rw [hL, ← Int.cast_sum] at hP
    by_contra hG
    have hGc : ((∑ x ∈ CS C, g {i, j} x : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 hG
    have hcard := mul_right_cancel₀ hGc hP
    have hsq := card_sq hC
    have hn := card_compl_pair hij
    obtain ⟨m, hm⟩ : ∃ m, #(univ.filter fun k => k ∉ ({i, j} : Finset (Fin n))) = m := ⟨_, rfl⟩
    rw [hm] at hcard hn
    rw [← hcard, ← mul_pow, ← sq, κ_sq, ← hn] at hsq
    exact three_pow_ne m hsq.symm
  · apply Finset.sum_eq_zero
    intro x hx
    by_contra hne
    exact h3 (three_dvd_of_max hC (mem_CS.1 hx) (max_of_g_ne_zero hne))

/-! ### The factor `8` -/

lemma f_neg (x : Word n) : f (-x) = (-1) ^ n * f x := by
  simp only [f, Pi.neg_apply, phi_neg, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]

lemma index_eq_zero_of_odd (hn : Odd n) : index C = 0 := by
  have h : index C = -index C := by
    unfold index
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_ ?_
    · intro x hx; exact mem_CS.2 (C.neg_mem (mem_CS.1 hx))
    · intro x hx; exact mem_CS.2 (C.neg_mem (mem_CS.1 hx))
    · intro x _; exact neg_neg x
    · intro x _; exact neg_neg x
    · intro x _; rw [f_neg, hn.neg_one_pow]; ring
  linarith

lemma exists_max_of_index_ne_zero (h : index C ≠ 0) : ∃ x ∈ C, ∀ k, x k ≠ 0 := by
  obtain ⟨x, hx, hfx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨x, mem_CS.1 hx, max_of_f_ne_zero hfx⟩

/-- Pairing `x ↔ -x`: over a negation-closed set, `Σ f = 2 Σ_{x_a = 1} f` (for `n` even). -/
lemma sum_eq_two_mul (hn : Even n) (A : Finset (Word n)) (hA : ∀ x ∈ A, -x ∈ A) (a : Fin n) :
    ∑ x ∈ A, f x = 2 * ∑ x ∈ A.filter (fun x => x a = 1), f x := by
  have hsplit : ∀ x : Word n,
      f x = (if x a = 1 then f x else 0) + (if x a = 2 then f x else 0) := by
    intro x
    rcases zmod3_cases (x a) with h | h | h
    · have hf : f x = 0 := Finset.prod_eq_zero (Finset.mem_univ a) (by rw [h]; decide)
      simp [hf]
    · simp [h]
    · simp [h]
  have hsym : ∑ x ∈ A, (if x a = 2 then f x else 0) = ∑ x ∈ A, (if x a = 1 then f x else 0) := by
    refine Finset.sum_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_ ?_
    · exact fun x hx => hA x hx
    · exact fun x hx => hA x hx
    · intro x _; exact neg_neg x
    · intro x _; exact neg_neg x
    · intro x _
      simp only [Pi.neg_apply, neg_eq_one_iff, f_neg, hn.neg_one_pow, one_mul]
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib, hsym, Finset.sum_filter]
  ring

/-- `4 Σ_{x_a = x_b = x_c} f(x) = Index`, from the design identity. -/
lemma four_mul_triple (hC : IsSelfDual C) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    4 * ∑ x ∈ (CS C).filter (fun x => x a = x b ∧ x b = x c), f x = index C := by
  have hpt : ∀ x : Word n, 4 * (if x a = x b ∧ x b = x c then f x else 0) =
      f x + f x * phi (x a) * phi (x b) + f x * phi (x a) * phi (x c) +
        f x * phi (x b) * phi (x c) := by
    intro x
    by_cases hf : f x = 0
    · simp [hf]
    · have hmax := max_of_f_ne_zero hf
      have hk := key3 (x a) (x b) (x c) (hmax a) (hmax b) (hmax c)
      calc 4 * (if x a = x b ∧ x b = x c then f x else 0)
          = f x * (if x a = x b ∧ x b = x c then (4 : ℤ) else 0) := by split_ifs <;> ring
        _ = f x * (1 + phi (x a) * phi (x b) + phi (x a) * phi (x c) +
              phi (x b) * phi (x c)) := by rw [hk]
        _ = _ := by ring
  rw [Finset.sum_filter, Finset.mul_sum, Finset.sum_congr rfl (fun x _ => hpt x),
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    design hC hab, design hC hac, design hC hbc]
  simp [index]

/-- **The factor 8.** -/
theorem eight_dvd_index (hC : IsSelfDual C) (hn0 : 0 < n) : 8 ∣ index C := by
  by_cases hI : index C = 0
  · rw [hI]; exact dvd_zero 8
  have hev : Even n := by
    rcases Nat.even_or_odd n with h | h
    · exact h
    · exact absurd (index_eq_zero_of_odd h) hI
  obtain ⟨x0, hx0, hmax⟩ := exists_max_of_index_ne_zero hI
  have hn3 : 3 ≤ n := Nat.le_of_dvd hn0 (three_dvd_of_max hC hx0 hmax)
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have hA : ∀ x ∈ (CS C).filter (fun x => x a = x b ∧ x b = x c),
      -x ∈ (CS C).filter (fun x => x a = x b ∧ x b = x c) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨mem_CS.2 (C.neg_mem (mem_CS.1 hx.1)), by simp [hx.2.1], by simp [hx.2.2]⟩
  rw [← four_mul_triple hC hab hac hbc, sum_eq_two_mul hev _ hA a, ← mul_assoc]
  exact dvd_mul_of_dvd_left (by norm_num) _

/-! ### The factor `3` -/

/-- The `±1` lift of a maximal word: `ε_k(x) = -φ(x_k)` (`1 ↦ 1`, `2 ↦ -1`). -/
def eps (x : Word n) (k : Fin n) : ℤ := -phi (x k)

lemma cast_eps (x : Word n) (k : Fin n) : ((eps x k : ℤ) : ZMod 3) = x k :=
  cast_neg_phi (x k)

lemma eps_sq (x : Word n) (k : Fin n) (h : x k ≠ 0) : eps x k ^ 2 = 1 := by
  rw [eps, neg_sq, sq, phi_sq_of_ne_zero _ h]

lemma pair_sum (hC : IsSelfDual C) (k l : Fin n) :
    ∑ x ∈ CS C, f x * (eps x k * eps x l) = if k = l then index C else 0 := by
  split_ifs with hkl
  · subst hkl
    unfold index
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x k = 0
    · have hf : f x = 0 := Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hx]; decide)
      simp [hf]
    · rw [← sq, eps_sq x k hx, mul_one]
  · rw [← design hC hkl]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [eps]
    ring

/-- `Σ_{x ∈ C} f(x) (ε(x)·v)² = Index · |v|²` for every integer vector `v`. -/
lemma sq_identity (hC : IsSelfDual C) (v : Fin n → ℤ) :
    ∑ x ∈ CS C, f x * (∑ k, eps x k * v k) ^ 2 = index C * ∑ k, v k ^ 2 := by
  have expand : ∀ x : Word n, f x * (∑ k, eps x k * v k) ^ 2 =
      ∑ k, ∑ l, v k * v l * (f x * (eps x k * eps x l)) := by
    intro x
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  calc ∑ x ∈ CS C, f x * (∑ k, eps x k * v k) ^ 2
      = ∑ x ∈ CS C, ∑ k, ∑ l, v k * v l * (f x * (eps x k * eps x l)) :=
        Finset.sum_congr rfl fun x _ => expand x
    _ = ∑ k, ∑ l, v k * v l * ∑ x ∈ CS C, f x * (eps x k * eps x l) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ k, ∑ l, if k = l then v k * v l * index C else 0 := by
        simp_rw [pair_sum hC, mul_ite, mul_zero]
    _ = index C * ∑ k, v k ^ 2 := by
        simp_rw [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

/-- **The factor 3.** -/
theorem three_dvd_index (hC : IsSelfDual C) (hn0 : 0 < n) : 3 ∣ index C := by
  by_cases hI : index C = 0
  · rw [hI]; exact dvd_zero 3
  obtain ⟨x0, hx0, hmax⟩ := exists_max_of_index_ne_zero hI
  have hdiv : ∀ v : Fin n → ℤ, (∀ k, ((v k : ℤ) : ZMod 3) = x0 k) →
      (9 : ℤ) ∣ index C * ∑ k, v k ^ 2 := by
    intro v hv
    rw [← sq_identity hC v]
    refine Finset.dvd_sum fun x hx => ?_
    apply Dvd.dvd.mul_left
    have hcast : ((∑ k, eps x k * v k : ℤ) : ZMod 3) = 0 := by
      rw [Int.cast_sum]
      simp_rw [Int.cast_mul, cast_eps, hv]
      exact dot_eq_zero_of_mem hC (mem_CS.1 hx) hx0
    have h3 : (3 : ℤ) ∣ ∑ k, eps x k * v k := by
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 hcast
    have h9 := pow_dvd_pow_of_dvd h3 2
    norm_num at h9
    exact h9
  have h1 := hdiv (fun k => eps x0 k) (fun k => cast_eps x0 k)
  have hsum1 : ∑ k, (eps x0 k) ^ 2 = (n : ℤ) := by
    rw [Finset.sum_congr rfl (fun k _ => eps_sq x0 k (hmax k))]
    simp
  let k0 : Fin n := ⟨0, hn0⟩
  have h2 := hdiv (fun k => if k = k0 then 4 * eps x0 k else eps x0 k) (by
    intro k
    split_ifs
    · rw [Int.cast_mul, cast_eps, show ((4 : ℤ) : ZMod 3) = 1 by decide, one_mul]
    · exact cast_eps x0 k)
  have hsum2 : ∑ k, (if k = k0 then 4 * eps x0 k else eps x0 k) ^ 2 = (n : ℤ) + 15 := by
    have hk : ∀ k, (if k = k0 then 4 * eps x0 k else eps x0 k) ^ 2 =
        1 + if k = k0 then 15 else 0 := by
      intro k
      split_ifs
      · rw [mul_pow, eps_sq x0 k (hmax k)]; norm_num
      · rw [eps_sq x0 k (hmax k)]; norm_num
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Finset.mem_univ, ite_true]
  rw [hsum1] at h1
  rw [hsum2] at h2
  have h15 : (9 : ℤ) ∣ index C * 15 := by
    have h := dvd_sub h2 h1
    rwa [show index C * ((n : ℤ) + 15) - index C * n = index C * 15 by ring] at h
  omega

/-! ### The theorem -/

lemma f_eq (x : Word n) : f x = if ∀ k, x k ≠ 0 then (-1) ^ ones x else 0 := by
  split_ifs with h
  · rw [f, Finset.prod_congr rfl (fun k _ => phi_of_ne_zero (x k) (h k)), Finset.prod_ite,
      Finset.prod_const, Finset.prod_const_one, mul_one]
    rfl
  · push Not at h
    obtain ⟨k, hk⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; decide)

/-- `Σ_{x ∈ C} f(x)` is GJF's index (#even − #odd maximal codewords). -/
lemma gjfIndex_eq (C : Submodule (ZMod 3) (Word n)) : gjfIndex C = index C := by
  unfold gjfIndex index
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [f_eq]
  by_cases hmax : ∀ k, x k ≠ 0
  · rcases Nat.even_or_odd (ones x) with he | ho
    · simp [hmax, he, he.neg_one_pow, Nat.not_odd_iff_even.2 he]
    · simp [hmax, ho, ho.neg_one_pow, Nat.not_even_iff_odd.2 ho]
  · simp [hmax]

/-- **Theorem** (GJF Conjecture 1.4, divisibility half). The index of a self-dual ternary code
of positive length is divisible by `24`. -/
theorem index_dvd_24 (C : Submodule (ZMod 3) (Word n)) (hC : IsSelfDual C) (hn : 0 < n) :
    (24 : ℤ) ∣ gjfIndex C := by
  rw [gjfIndex_eq]
  have h8 := eight_dvd_index hC hn
  have h3 := three_dvd_index hC hn
  omega

/-- The hypothesis `0 < n` is needed: the unique code of length `0` is self-dual ... -/
example : IsSelfDual (⊤ : Submodule (ZMod 3) (Word 0)) := by
  intro x
  simp [dot]

/-- ... and its index is `1`, because the empty word is an even maximal codeword. -/
example : gjfIndex (⊤ : Submodule (ZMod 3) (Word 0)) = 1 := by
  rw [gjfIndex_eq]
  simp [index, CS, f]

end GJF
