import GJF.Divisibility

/-!
# Existence of self-dual ternary codes of index 24 in every length `12k`

A formalization of Theorem 5.9 of the notes (`paper/index24.tex`): partial Hadamard quadrupling.

Codes live on finite index types. A code with a block system has coordinates `S ⊕ (B × P)`,
where `S` are the singletons, `B` the blocks and `P = Fin 2 × Fin 2` the four positions of a
block (paired by the first component).

* `D E` doubles every block of `E` against a tetracode (`Φ(e,t) = (e+t, e-t)` on each pair).
* `sum_D`: for any weight that factors over singletons and doubled blocks and satisfies the local
  identity `Σ_{t ∈ T} G(dbl u t) = λ(wt u)` on each block, the sum over `D E` equals the block
  weighted index `R E`. Lemmas A and B of the paper (`localA`, `localB`) are the two instances.
* `engine`: two doublings (one step-one block refined, the others made singletons) give a
  self-dual code of length `|S| + 16|B|` with index `R E`, and a new two-block state with the same `R`.
* `exists_selfDual_index24`: for every `k ≥ 1` there is a self-dual ternary code of length `12k`
  and index exactly `24`.
-/

open Finset

set_option linter.unusedSectionVars false
-- instance search for `DecidableEq` on the nested coordinate types needs more room
set_option synthInstance.maxSize 2048

/- Mathlib's instance `[IsSimpleAddGroup G] [AddGroup.IsNilpotent G] : AddCommGroup G` applies to
`ZMod 3` and hijacks the search for `Neg (ZMod 3)`; simp lemmas and `ring` then fail to match terms
built with the ring structure. Disable it in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Ex

open GJF

/-- The field `𝔽₃` (a notation, so that all terms use the instances of `ZMod 3`). -/
local notation "F" => ZMod 3

/-! ### Codes on a general finite index type -/

section General

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The dot product on `𝔽₃^ι`. -/
def dotG (x y : ι → F) : F := ∑ i, x i * y i

lemma dotG_comm (x y : ι → F) : dotG x y = dotG y x := by
  simp [dotG, mul_comm]

lemma dotG_add_left (x y z : ι → F) : dotG (x + y) z = dotG x z + dotG y z := by
  simp [dotG, add_mul, Finset.sum_add_distrib]

/-- Self-duality. -/
def SelfDualG (C : Submodule F (ι → F)) : Prop := ∀ x, x ∈ C ↔ ∀ c ∈ C, dotG x c = 0

/-- The codewords as a finset. -/
noncomputable def CSG (C : Submodule F (ι → F)) : Finset (ι → F) := by
  classical exact univ.filter (· ∈ C)

lemma mem_CSG {C : Submodule F (ι → F)} {x : ι → F} : x ∈ CSG C ↔ x ∈ C := by
  classical simp [CSG]

/-- `f(x) = ∏ φ(x_i)`. -/
def fG (x : ι → F) : ℤ := ∏ i, phi (x i)

/-- `Σ_{x ∈ C} f(x)`, the index. -/
noncomputable def indexG (C : Submodule F (ι → F)) : ℤ := ∑ x ∈ CSG C, fG x

/-- Transport a code on `κ` to `ι` along `e : ι ≃ κ`: `y ∈ relabel e C ↔ y ∘ e.symm ∈ C`. -/
def relabel (e : ι ≃ κ) (C : Submodule F (κ → F)) : Submodule F (ι → F) :=
  C.comap (LinearMap.funLeft F F e.symm)

lemma mem_relabel {e : ι ≃ κ} {C : Submodule F (κ → F)} {y : ι → F} :
    y ∈ relabel e C ↔ (fun k => y (e.symm k)) ∈ C := Iff.rfl

lemma sum_relabel {M : Type*} [AddCommMonoid M] (e : ι ≃ κ) (C : Submodule F (κ → F))
    (g : (ι → F) → M) :
    ∑ y ∈ CSG (relabel e C), g y = ∑ x ∈ CSG C, g (fun i => x (e i)) := by
  refine Finset.sum_nbij' (fun y => fun k => y (e.symm k)) (fun x => fun i => x (e i))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy; exact mem_CSG.2 (mem_relabel.1 (mem_CSG.1 hy))
  · intro x hx; apply mem_CSG.2; apply mem_relabel.2; simpa using mem_CSG.1 hx
  · intro y _; funext i; simp
  · intro x _; funext k; simp
  · intro y _; congr 1; funext i; simp

lemma card_relabel (e : ι ≃ κ) (C : Submodule F (κ → F)) :
    #(CSG (relabel e C)) = #(CSG C) := by
  have h := sum_relabel e C (fun _ => (1 : ℕ))
  simpa using h

lemma dotG_comp (e : ι ≃ κ) (x y : κ → F) :
    dotG (fun i => x (e i)) (fun i => y (e i)) = dotG x y := by
  unfold dotG
  exact Equiv.sum_comp e (fun k => x k * y k)

lemma selfDual_relabel (e : ι ≃ κ) {C : Submodule F (κ → F)} (hC : SelfDualG C) :
    SelfDualG (relabel e C) := by
  intro y
  rw [mem_relabel, hC]
  constructor
  · intro h z hz
    have := h _ (mem_relabel.1 hz)
    rwa [dotG_comp e.symm] at this
  · intro h c hc
    have hz : (fun i => c (e i)) ∈ relabel e C := by
      apply mem_relabel.2; simpa using hc
    have h1 := h _ hz
    have h2 := dotG_comp e.symm y (fun i => c (e i))
    simp only [Equiv.apply_symm_apply] at h2
    rw [h2]
    exact h1

lemma indexG_relabel (e : ι ≃ κ) (C : Submodule F (κ → F)) :
    indexG (relabel e C) = indexG C := by
  unfold indexG
  rw [sum_relabel]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Equiv.prod_comp e (fun k => phi (x k))

/-! #### Character sums and a counting criterion for self-duality -/

lemma sum_char_univ (u : ι → F) (hu : u ≠ 0) : ∑ x, ψ (dotG u x) = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
  simp only [Pi.zero_apply] at hi
  have hshift : ∑ x, ψ (dotG u (x + Pi.single i 1)) = ∑ x, ψ (dotG u x) :=
    Fintype.sum_equiv (Equiv.addRight (Pi.single i 1)) _ _ (fun _ => rfl)
  have hdot : ∀ x, dotG u (x + Pi.single i 1) = dotG u x + u i := by
    intro x
    simp [dotG, mul_add, Finset.sum_add_distrib, Pi.single_apply]
  simp_rw [hdot, ψ_add, ← Finset.sum_mul] at hshift
  have h1 : (∑ x, ψ (dotG u x)) * (ψ (u i) - 1) = 0 := by
    rw [mul_sub, hshift, mul_one, sub_self]
  rcases mul_eq_zero.1 h1 with h | h
  · exact h
  · exact absurd (sub_eq_zero.1 h) (ψ_ne_one hi)

lemma sum_char_code (C : Submodule F (ι → F)) (x : ι → F) (c : ι → F) (hc : c ∈ C)
    (hcx : dotG c x ≠ 0) : ∑ u ∈ CSG C, ψ (dotG u x) = 0 := by
  have hshift : ∑ u ∈ CSG C, ψ (dotG (u + c) x) = ∑ u ∈ CSG C, ψ (dotG u x) := by
    refine Finset.sum_nbij' (fun u => u + c) (fun u => u - c) ?_ ?_ ?_ ?_ ?_
    · intro u hu; exact mem_CSG.2 (C.add_mem (mem_CSG.1 hu) hc)
    · intro u hu; exact mem_CSG.2 (C.sub_mem (mem_CSG.1 hu) hc)
    · intro u _; simp
    · intro u _; simp
    · intro u _; rfl
  simp_rw [dotG_add_left, ψ_add, ← Finset.sum_mul] at hshift
  have h1 : (∑ u ∈ CSG C, ψ (dotG u x)) * (ψ (dotG c x) - 1) = 0 := by
    rw [mul_sub, hshift, mul_one, sub_self]
  rcases mul_eq_zero.1 h1 with h | h
  · exact h
  · exact absurd (sub_eq_zero.1 h) (ψ_ne_one hcx)

/-- The dual code as a finset. -/
noncomputable def perp (C : Submodule F (ι → F)) : Finset (ι → F) := by
  classical exact univ.filter fun x => ∀ c ∈ C, dotG x c = 0

lemma mem_perp {C : Submodule F (ι → F)} {x : ι → F} :
    x ∈ perp C ↔ ∀ c ∈ C, dotG x c = 0 := by
  classical simp [perp]

lemma card_F_fun : Fintype.card (ι → F) = 3 ^ Fintype.card ι := by
  simp [ZMod.card]

/-- `|C| · |C^⊥| = 3^|ι|`. -/
lemma card_mul_card_perp (C : Submodule F (ι → F)) :
    #(CSG C) * #(perp C) = 3 ^ Fintype.card ι := by
  have hA : ∑ u ∈ CSG C, ∑ x, ψ (dotG u x) = (3 : ℂ) ^ Fintype.card ι := by
    have : ∀ u ∈ CSG C, ∑ x, ψ (dotG u x) = if u = 0 then (3 : ℂ) ^ Fintype.card ι else 0 := by
      intro u _
      split_ifs with hu
      · subst hu
        simp [dotG, ψ_zero]
      · exact sum_char_univ u hu
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (CSG C) 0]
    simp [mem_CSG.2 C.zero_mem]
  have hB : ∑ u ∈ CSG C, ∑ x, ψ (dotG u x) = (#(CSG C) : ℂ) * #(perp C) := by
    rw [Finset.sum_comm]
    have : ∀ x : ι → F, ∑ u ∈ CSG C, ψ (dotG u x) =
        if x ∈ perp C then (#(CSG C) : ℂ) else 0 := by
      intro x
      split_ifs with hx
      · have h1 : ∀ u ∈ CSG C, ψ (dotG u x) = 1 := fun u hu => by
          rw [dotG_comm, mem_perp.1 hx u (mem_CSG.1 hu), ψ_zero]
        rw [Finset.sum_congr rfl h1]; simp
      · rw [mem_perp] at hx
        push Not at hx
        obtain ⟨c, hc, hxc⟩ := hx
        exact sum_char_code C x c hc (by rwa [dotG_comm])
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_ite_mem, Finset.univ_inter]
    simp [mul_comm]
  have h := hA.symm.trans hB
  exact_mod_cast h.symm

lemma card_sq_of_selfDual {C : Submodule F (ι → F)} (hC : SelfDualG C) :
    #(CSG C) ^ 2 = 3 ^ Fintype.card ι := by
  have hp : perp C = CSG C := by
    ext x; rw [mem_perp, mem_CSG, hC x]
  rw [sq, ← card_mul_card_perp C, hp]

/-- **Counting criterion.** An isotropic code with `|C|² = 3^|ι|` is self-dual. -/
lemma selfDual_of_iso_card (C : Submodule F (ι → F))
    (hiso : ∀ x ∈ C, ∀ y ∈ C, dotG x y = 0) (hcard : #(CSG C) ^ 2 = 3 ^ Fintype.card ι) :
    SelfDualG C := by
  have hsub : CSG C ⊆ perp C := fun x hx =>
    mem_perp.2 fun c hc => hiso x (mem_CSG.1 hx) c hc
  have hpos : 0 < #(CSG C) := Finset.card_pos.2 ⟨0, mem_CSG.2 C.zero_mem⟩
  have hmul := card_mul_card_perp C
  rw [← hcard, sq] at hmul
  have hcard' : #(perp C) = #(CSG C) := Nat.eq_of_mul_eq_mul_left hpos hmul
  have heq : CSG C = perp C := Finset.eq_of_subset_of_card_le hsub hcard'.le
  intro x
  rw [← mem_CSG, heq, mem_perp]

end General

/-! ### The tetracode on a block and the two local identities -/

/-- The four positions of a block; the pairs are `{(a,0),(a,1)}`. -/
abbrev P := Fin 2 × Fin 2

/-- The dot product on a block. -/
def dotP (x y : P → F) : F := ∑ p, x p * y p

/-- Generators of the tetracode `(1,1,1,0)` and `(0,1,2,1)`, positions ordered `(a,b) ↦ 2a+b`. -/
def t1 : P → F := fun p => ![![1, 1], ![1, 0]] p.1 p.2
def t2 : P → F := fun p => ![![0, 1], ![2, 1]] p.1 p.2

/-- The tetracode `T = ⟨t1, t2⟩ = ⟨t1, t2⟩^⊥`. -/
def inT (t : P → F) : Prop := dotP t t1 = 0 ∧ dotP t t2 = 0

instance : DecidablePred inT := fun t => by unfold inT; infer_instance

/-- The tetracode as a finset. -/
def Tfin : Finset (P → F) := univ.filter inT

lemma mem_Tfin {t : P → F} : t ∈ Tfin ↔ inT t := by simp [Tfin]

lemma card_Tfin : #Tfin = 9 := by decide

set_option maxRecDepth 100000 in
lemma inT_iso : ∀ t t' : P → F, inT t → inT t' → dotP t t' = 0 := by decide

lemma dotP_add_left (x y z : P → F) : dotP (x + y) z = dotP x z + dotP y z := by
  simp [dotP, add_mul, Finset.sum_add_distrib]

lemma dotP_smul_left (c : F) (x z : P → F) : dotP (c • x) z = c * dotP x z := by
  simp [dotP, Finset.mul_sum, mul_assoc]

lemma inT_zero : inT 0 := by simp [inT, dotP]

lemma inT_add {t t' : P → F} (h : inT t) (h' : inT t') : inT (t + t') := by
  unfold inT at *
  rw [dotP_add_left, dotP_add_left, h.1, h.2, h'.1, h'.2]
  simp

lemma inT_smul (c : F) {t : P → F} (h : inT t) : inT (c • t) := by
  unfold inT at *
  rw [dotP_smul_left, dotP_smul_left, h.1, h.2]
  simp

/-- `λ(0..4) = (0, -2, 0, 0, 1)`. -/
def lam (w : ℕ) : ℤ := if w = 4 then 1 else if w = 1 then -2 else 0

/-- The weight of a block. -/
def wtP (u : P → F) : ℕ := #(univ.filter fun p => u p ≠ 0)

/-- One Hadamard doubling of a block: `(u + t, u - t)` on each position. -/
def dbl (u t : P → F) : P × Fin 2 → F := fun q => if q.2 = 0 then u q.1 + t q.1 else u q.1 - t q.1

/-- A doubled block whose eight coordinates become singletons. -/
def sgl (v : P × Fin 2 → F) : ℤ := ∏ q, phi (v q)

/-- A doubled block refined into two blocks `{(a,b,s)}_{b,s}`, `a = 0, 1`. -/
def refd (v : P × Fin 2 → F) : ℤ :=
  ∏ a : Fin 2, lam (#(univ.filter fun q : Fin 2 × Fin 2 => v ((a, q.1), q.2) ≠ 0))

set_option maxRecDepth 100000 in
/-- **Lemma A** (doubling identity), checked by the kernel for all `u`. -/
theorem localA : ∀ u : P → F, ∑ t ∈ Tfin, sgl (dbl u t) = lam (wtP u) := by decide

set_option maxRecDepth 100000 in
/-- **Lemma B** (refinement identity), checked by the kernel for all `u`. -/
theorem localB : ∀ u : P → F, ∑ t ∈ Tfin, refd (dbl u t) = lam (wtP u) := by decide

lemma pair_inj : ∀ a b c d : F, a + c = b + d → a - c = b - d → a = b ∧ c = d := by decide

lemma three_eq_zero : (3 : F) = 0 := by decide

/-- The local form computation behind isotropy: `Σ_q dbl(u,t) dbl(u',t') = -Σ u u'`. -/
lemma block_sum (u u' t t' : P → F) (ht : inT t) (ht' : inT t') :
    ∑ q : P × Fin 2, dbl u t q * dbl u' t' q = -∑ p, u p * u' p := by
  rw [Fintype.sum_prod_type]
  have hT := inT_iso t t' ht ht'
  unfold dotP at hT
  calc ∑ p, ∑ s : Fin 2, dbl u t (p, s) * dbl u' t' (p, s)
      = ∑ p, (-(u p * u' p) - t p * t' p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [Fin.sum_univ_two, dbl, Fin.isValue, one_ne_zero, ↓reduceIte]
        linear_combination (u p * u' p + t p * t' p) * three_eq_zero
    _ = -∑ p, u p * u' p - ∑ p, t p * t' p := by
        simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    _ = -∑ p, u p * u' p := by simp [hT]

/-! ### Block codes and Hadamard doubling -/

section Blocks

variable {S B B' : Type*} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
  [Fintype B'] [DecidableEq B']

/-- Coordinates of a code with a block system: singletons `S`, blocks `B × P`. -/
abbrev Blk (S B : Type*) := S ⊕ (B × P)

/-- Coordinates after doubling every block. -/
abbrev Dbl (S B : Type*) := S ⊕ (B × (P × Fin 2))

/-- The doubling map `(e, t) ↦ Φ(e,t)`. -/
def Φ (e : Blk S B → F) (t : B → P → F) : Dbl S B → F :=
  Sum.elim (fun s => e (.inl s)) (fun q => dbl (fun p => e (.inr (q.1, p))) (t q.1) q.2)

lemma Φ_add (e e' : Blk S B → F) (t t' : B → P → F) : Φ (e + e') (t + t') = Φ e t + Φ e' t' := by
  funext v
  rcases v with s | ⟨β, p, s⟩
  · rfl
  · simp only [Φ, Sum.elim_inr, dbl, Pi.add_apply]
    split_ifs <;> ring

lemma Φ_smul (c : F) (e : Blk S B → F) (t : B → P → F) : Φ (c • e) (c • t) = c • Φ e t := by
  funext v
  rcases v with s | ⟨β, p, s⟩
  · rfl
  · simp only [Φ, Sum.elim_inr, dbl, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring

lemma Φ_zero : Φ (0 : Blk S B → F) 0 = 0 := by
  funext v
  rcases v with s | ⟨β, p, s⟩
  · rfl
  · simp only [Φ, Sum.elim_inr, dbl, Pi.zero_apply]
    split_ifs <;> simp

/-- `D E`: double every block of `E` against a tetracode. -/
def D (E : Submodule F (Blk S B → F)) : Submodule F (Dbl S B → F) where
  carrier := {v | ∃ e ∈ E, ∃ t : B → P → F, (∀ β, inT (t β)) ∧ Φ e t = v}
  add_mem' := by
    rintro _ _ ⟨e, he, t, ht, rfl⟩ ⟨e', he', t', ht', rfl⟩
    exact ⟨e + e', E.add_mem he he', t + t', fun β => inT_add (ht β) (ht' β), Φ_add _ _ _ _⟩
  zero_mem' := ⟨0, E.zero_mem, 0, fun _ => inT_zero, Φ_zero⟩
  smul_mem' := by
    rintro c _ ⟨e, he, t, ht, rfl⟩
    exact ⟨c • e, E.smul_mem c he, c • t, fun β => inT_smul c (ht β), Φ_smul _ _ _⟩

lemma mem_D {E : Submodule F (Blk S B → F)} {v : Dbl S B → F} :
    v ∈ D E ↔ ∃ e ∈ E, ∃ t : B → P → F, (∀ β, inT (t β)) ∧ Φ e t = v := Iff.rfl

lemma Φ_inj {e e' : Blk S B → F} {t t' : B → P → F} (h : Φ e t = Φ e' t') :
    e = e' ∧ t = t' := by
  have key : ∀ β p, e (.inr (β, p)) = e' (.inr (β, p)) ∧ t β p = t' β p := by
    intro β p
    have h0 := congrFun h (.inr (β, p, 0))
    have h1 := congrFun h (.inr (β, p, 1))
    simp only [Φ, Sum.elim_inr, dbl, Fin.isValue, one_ne_zero, ↓reduceIte] at h0 h1
    exact pair_inj _ _ _ _ h0 h1
  refine ⟨?_, ?_⟩
  · funext i
    rcases i with s | ⟨β, p⟩
    · exact congrFun h (.inl s)
    · exact (key β p).1
  · funext β p
    exact (key β p).2

lemma CSG_D (E : Submodule F (Blk S B → F)) :
    CSG (D E) = (CSG E ×ˢ Fintype.piFinset fun _ : B => Tfin).image (fun et => Φ et.1 et.2) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_product, Fintype.mem_piFinset, mem_CSG, mem_Tfin,
    mem_D, Prod.exists]
  constructor
  · rintro ⟨e, he, t, ht, rfl⟩
    exact ⟨e, t, ⟨he, ht⟩, rfl⟩
  · rintro ⟨e, t, ⟨he, ht⟩, rfl⟩
    exact ⟨e, he, t, ht, rfl⟩

lemma card_D (E : Submodule F (Blk S B → F)) :
    #(CSG (D E)) = #(CSG E) * 9 ^ Fintype.card B := by
  rw [CSG_D, Finset.card_image_of_injOn (fun a _ b _ hab => Prod.ext_iff.2 (Φ_inj hab)),
    Finset.card_product, Fintype.card_piFinset]
  simp [card_Tfin]

/-- The block-weighted weight `∏_{s} φ(x_s) ∏_{β} λ(wt x|_β)`. -/
def Rw (x : Blk S B → F) : ℤ := (∏ s, phi (x (.inl s))) * ∏ β, lam (wtP fun p => x (.inr (β, p)))

/-- The block-weighted index `R_σ(E)`. -/
noncomputable def R (E : Submodule F (Blk S B → F)) : ℤ := ∑ x ∈ CSG E, Rw x

/-- **Summation over a doubled code.** A weight that factors over singletons and doubled
blocks, each block satisfying the local identity, sums to `R E`. -/
theorem sum_D (E : Submodule F (Blk S B → F)) (G : B → (P × Fin 2 → F) → ℤ)
    (hG : ∀ β u, ∑ t ∈ Tfin, G β (dbl u t) = lam (wtP u)) :
    ∑ v ∈ CSG (D E), (∏ s, phi (v (.inl s))) * ∏ β, G β (fun q => v (.inr (β, q))) = R E := by
  rw [CSG_D, Finset.sum_image (fun a _ b _ hab => Prod.ext_iff.2 (Φ_inj hab)),
    Finset.sum_product]
  unfold R
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Φ, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.mul_sum,
    ← Finset.prod_univ_sum (fun _ : B => Tfin) (fun β t => G β (dbl (fun p => e (.inr (β, p))) t))]
  unfold Rw
  congr 1
  exact Finset.prod_congr rfl fun β _ => hG β _

/-- The form `dot_S + σ · dot_blocks`. -/
def dotSgn (σ : F) (x y : Blk S B → F) : F :=
  (∑ s, x (.inl s) * y (.inl s)) + σ * ∑ β, ∑ p, x (.inr (β, p)) * y (.inr (β, p))

/-- The same form on doubled coordinates. -/
def dotDbl (σ : F) (v w : Dbl S B → F) : F :=
  (∑ s, v (.inl s) * w (.inl s)) + σ * ∑ β, ∑ q, v (.inr (β, q)) * w (.inr (β, q))

/-- Isotropy for `dotSgn σ`. -/
def Iso (σ : F) (E : Submodule F (Blk S B → F)) : Prop := ∀ x ∈ E, ∀ y ∈ E, dotSgn σ x y = 0

/-- **Isotropy transfer.** Doubling negates the form on the blocks. -/
lemma iso_D {σ : F} {E : Submodule F (Blk S B → F)} (hE : Iso σ E) :
    ∀ v ∈ D E, ∀ w ∈ D E, dotDbl (-σ) v w = 0 := by
  rintro _ ⟨e, he, t, ht, rfl⟩ _ ⟨e', he', t', ht', rfl⟩
  have h := hE e he e' he'
  unfold dotSgn at h
  unfold dotDbl
  simp only [Φ, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_congr rfl fun β _ => block_sum _ _ _ _ (ht β) (ht' β)]
  simp only [Finset.sum_neg_distrib]
  linear_combination h

lemma dotSgn_one (x y : Blk S B → F) : dotSgn 1 x y = dotG x y := by
  simp [dotSgn, dotG, Fintype.sum_sum_type, Fintype.sum_prod_type]

lemma dotDbl_one (v w : Dbl S B → F) : dotDbl 1 v w = dotG v w := by
  simp [dotDbl, dotG, Fintype.sum_sum_type, Fintype.sum_prod_type]

lemma iso_of_selfDual {E : Submodule F (Blk S B → F)} (hE : SelfDualG E) : Iso 1 E := by
  intro x hx y hy
  rw [dotSgn_one]
  exact (hE x).1 hx y hy

/-- The regrouping `S ⊕ ((B × Fin 2) × P) ≃ S ⊕ (B × P × Fin 2)`, `((β,a),(b,s)) ↦ (β,(a,b),s)`. -/
def r₁ (S B : Type*) : Blk S (B × Fin 2) ≃ Dbl S B where
  toFun := Sum.elim Sum.inl (fun q => Sum.inr (q.1.1, (q.1.2, q.2.1), q.2.2))
  invFun := Sum.elim Sum.inl (fun q => Sum.inr ((q.1, q.2.1.1), (q.2.1.2, q.2.2)))
  left_inv := by rintro (s | ⟨⟨β, a⟩, b, s⟩) <;> rfl
  right_inv := by rintro (s | ⟨β, ⟨a, b⟩, s⟩) <;> rfl

/-- Relabel the blocks along `eb`. -/
def blockEquiv (S : Type*) (eb : B' ≃ B) : Blk S B' ≃ Blk S B :=
  Equiv.sumCongr (Equiv.refl S) (Equiv.prodCongr eb (Equiv.refl P))

lemma dotSgn_r₁ (σ : F) (v w : Dbl S B → F) :
    dotSgn σ (fun i => v (r₁ S B i)) (fun i => w (r₁ S B i)) = dotDbl σ v w := by
  simp only [dotSgn, dotDbl, r₁, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_prod_type]

lemma iso_r₁ {σ : F} {E : Submodule F (Blk S B → F)} (hE : Iso σ E) :
    Iso (-σ) (relabel (r₁ S B) (D E)) := by
  intro x hx y hy
  have h := iso_D hE _ (mem_relabel.1 hx) _ (mem_relabel.1 hy)
  rw [← dotSgn_r₁] at h
  simpa using h

lemma dotSgn_block (σ : F) (eb : B' ≃ B) (x y : Blk S B → F) :
    dotSgn σ (fun i => x (blockEquiv S eb i)) (fun i => y (blockEquiv S eb i)) = dotSgn σ x y := by
  simp only [dotSgn, blockEquiv, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
  congr 2
  exact Equiv.sum_comp eb (fun β => ∑ p, x (.inr (β, p)) * y (.inr (β, p)))

lemma iso_block {σ : F} (eb : B' ≃ B) {E : Submodule F (Blk S B → F)} (hE : Iso σ E) :
    Iso σ (relabel (blockEquiv S eb) E) := by
  intro x hx y hy
  have h := hE _ (mem_relabel.1 hx) _ (mem_relabel.1 hy)
  rw [← dotSgn_block σ eb] at h
  simpa using h

lemma R_block (eb : B' ≃ B) (E : Submodule F (Blk S B → F)) :
    R (relabel (blockEquiv S eb) E) = R E := by
  unfold R
  rw [sum_relabel]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Rw, blockEquiv, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
  congr 1
  exact Equiv.prod_comp eb (fun β => lam (wtP fun p => x (.inr (β, p))))

lemma R_r₁ (E : Submodule F (Blk S B → F)) : R (relabel (r₁ S B) (D E)) = R E := by
  rw [← sum_D E (fun _ => refd) (fun _ u => localB u)]
  unfold R
  rw [sum_relabel]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Rw, r₁, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr, Fintype.prod_prod_type]
  rfl

lemma indexG_D (E : Submodule F (Blk S B → F)) : indexG (D E) = R E := by
  unfold indexG
  rw [← sum_D E (fun _ => sgl) (fun _ u => localA u)]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [fG, sgl, Fintype.prod_sum_type, Fintype.prod_prod_type]

end Blocks

/-! ### The engine: partial quadrupling with one refined step-one block -/

section Engine

variable {S B : Type} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]

/-- The step-one blocks other than the refined one `β₀`. -/
abbrev K (β₀ : B × Fin 2) := {x : B × Fin 2 // x ≠ β₀}

/-- After the first doubling, with step-one blocks indexed by `Option K` (`none` = `β₀`). -/
noncomputable def E1 (β₀ : B × Fin 2) (E : Submodule F (Blk S B → F)) :
    Submodule F (Blk S (Option (K β₀)) → F) :=
  relabel (blockEquiv S (Equiv.optionSubtypeNe β₀)) (relabel (r₁ S B) (D E))

/-- The quadrupled code `Q_σ(E)`, of length `|S| + 16|B|`. -/
noncomputable def Qc (β₀ : B × Fin 2) (E : Submodule F (Blk S B → F)) :
    Submodule F (Dbl S (Option (K β₀)) → F) := D (E1 β₀ E)

/-- The singletons of the new state: the old ones and the coordinates of the unrefined
step-one blocks. -/
abbrev S2 (S : Type) (β₀ : B × Fin 2) := S ⊕ (K β₀ × (P × Fin 2))

/-- Regroup `Q_σ(E)` as a two-block code: the refined step-one block splits into two blocks. -/
def r₂ (S : Type) (β₀ : B × Fin 2) : Blk (S2 S β₀) (Fin 2) ≃ Dbl S (Option (K β₀)) where
  toFun := Sum.elim (Sum.elim Sum.inl (fun kq => Sum.inr (some kq.1, kq.2)))
    (fun bp => Sum.inr (none, ((bp.1, bp.2.1), bp.2.2)))
  invFun := Sum.elim (fun s => Sum.inl (Sum.inl s))
    (fun oq => Option.elim oq.1 (Sum.inr (oq.2.1.1, (oq.2.1.2, oq.2.2)))
      (fun k => Sum.inl (Sum.inr (k, oq.2))))
  left_inv := by rintro ((s | ⟨k, q⟩) | ⟨b, s', u⟩) <;> rfl
  right_inv := by rintro (s | ⟨(_ | k), ⟨b, s'⟩, u⟩) <;> rfl

/-- The new two-block state. -/
noncomputable def newState (β₀ : B × Fin 2) (E : Submodule F (Blk S B → F)) :
    Submodule F (Blk (S2 S β₀) (Fin 2) → F) := relabel (r₂ S β₀) (Qc β₀ E)

lemma R_E1 (β₀ : B × Fin 2) (E : Submodule F (Blk S B → F)) : R (E1 β₀ E) = R E := by
  rw [E1, R_block, R_r₁]

lemma iso_E1 (β₀ : B × Fin 2) {E : Submodule F (Blk S B → F)} (hE : SelfDualG E) :
    Iso (-1) (E1 β₀ E) :=
  iso_block _ (iso_r₁ (iso_of_selfDual hE))

lemma card_E1 (β₀ : B × Fin 2) (E : Submodule F (Blk S B → F)) :
    #(CSG (E1 β₀ E)) = #(CSG E) * 9 ^ Fintype.card B := by
  rw [E1, card_relabel, card_relabel, card_D]

lemma card_optionK (β₀ : B × Fin 2) : Fintype.card (Option (K β₀)) = 2 * Fintype.card B := by
  rw [Fintype.card_congr (Equiv.optionSubtypeNe β₀), Fintype.card_prod, Fintype.card_fin,
    mul_comm]

/-- `Q_σ(E)` is self-dual. -/
theorem selfDual_Qc (β₀ : B × Fin 2) {E : Submodule F (Blk S B → F)} (hE : SelfDualG E) :
    SelfDualG (Qc β₀ E) := by
  apply selfDual_of_iso_card
  · intro v hv w hw
    have h := iso_D (iso_E1 β₀ hE) v hv w hw
    rwa [neg_neg, dotDbl_one] at h
  · rw [Qc, card_D, card_E1, card_optionK]
    have hE2 := card_sq_of_selfDual hE
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_optionK] at hE2 ⊢
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9, mul_pow, mul_pow, hE2]
    simp only [← pow_mul, ← pow_add]
    congr 1
    ring

/-- **Main lemma (1).** `Index(Q_σ(E)) = R_σ(E)`. -/
theorem indexG_Qc (β₀ : B × Fin 2) (E : Submodule F (Blk S B → F)) :
    indexG (Qc β₀ E) = R E := by
  rw [Qc, indexG_D, R_E1]

/-- **Main lemma (2)**, with one step-one block refined: the new state has the same `R`. -/
theorem R_newState (β₀ : B × Fin 2) (E : Submodule F (Blk S B → F)) :
    R (newState β₀ E) = R E := by
  have hG : ∀ (o : Option (K β₀)) (u : P → F),
      ∑ t ∈ Tfin, (o.elim refd fun _ => sgl) (dbl u t) = lam (wtP u) := by
    intro o u
    cases o
    · exact localB u
    · exact localA u
  rw [← R_E1 β₀ E, ← sum_D (E1 β₀ E) (fun o => o.elim refd fun _ => sgl) hG]
  unfold R newState Qc
  rw [sum_relabel]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hL : Rw (fun i => w (r₂ S β₀ i)) = ((∏ s, phi (w (.inl s))) *
      ∏ k : K β₀, sgl (fun q => w (.inr (some k, q)))) * refd (fun q => w (.inr (none, q))) := by
    simp only [Rw, r₂, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr, Fintype.prod_sum_type]
    rw [Fintype.prod_prod_type]
    rfl
  rw [hL, Fintype.prod_option]
  simp only [Option.elim]
  ring

/-- A two-block state of length `m` with `R = 24`. -/
def State2 (m : ℕ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (E : Submodule F (Blk S (Fin 2) → F)),
    SelfDualG E ∧ R E = 24 ∧ Fintype.card S + 8 = m

/-- A self-dual code of length `n` and index `24`, on some index type. -/
def CodeExists (n : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (C : Submodule F (ι → F)),
    SelfDualG C ∧ indexG C = 24 ∧ Fintype.card ι = n

/-- **The engine.** A state with `R = 24` gives a code of length `|S| + 16|B|` with index `24`
and a two-block state of the same length with `R = 24`. -/
theorem engine (E : Submodule F (Blk S B → F)) (hE : SelfDualG E) (hR : R E = 24)
    (β₀ : B × Fin 2) :
    CodeExists (Fintype.card S + 16 * Fintype.card B) ∧
      State2 (Fintype.card S + 16 * Fintype.card B) := by
  refine ⟨⟨Dbl S (Option (K β₀)), inferInstance, inferInstance, Qc β₀ E, selfDual_Qc β₀ hE,
      by rw [indexG_Qc, hR], ?_⟩,
    ⟨S2 S β₀, inferInstance, inferInstance, newState β₀ E,
      selfDual_relabel _ (selfDual_Qc β₀ hE), by rw [R_newState, hR], ?_⟩⟩
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_optionK]
    ring
  · have h := card_optionK β₀
    rw [Fintype.card_option] at h
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega

end Engine

theorem state_step {m : ℕ} (h : State2 m) : CodeExists (m + 24) ∧ State2 (m + 24) := by
  obtain ⟨S, _, _, E, hE, hR, hm⟩ := h
  have := engine E hE hR ((0 : Fin 2), (0 : Fin 2))
  have hlen : Fintype.card S + 16 * Fintype.card (Fin 2) = m + 24 := by
    simp only [Fintype.card_fin]; omega
  rwa [hlen] at this

theorem chain {m : ℕ} (h : State2 m) (j : ℕ) :
    State2 (m + 24 * j) ∧ CodeExists (m + 24 * (j + 1)) := by
  induction j with
  | zero => exact ⟨by simpa using h, by simpa using (state_step h).1⟩
  | succ j ih =>
    have h1 := state_step ih.1
    refine ⟨?_, ?_⟩
    · rw [show m + 24 * (j + 1) = m + 24 * j + 24 by ring]
      exact h1.2
    · rw [show m + 24 * (j + 1 + 1) = m + 24 * j + 24 + 24 by ring]
      exact (state_step h1.2).1

/-! ### Base cases from the extended ternary Golay code -/

/-- A generator matrix of the extended ternary Golay code (the one in `paper/index24.tex` and
GJF Example 1.5, with `-1` written as `2`). -/
def golayRow : Fin 6 → Fin 12 → F := ![
  ![1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1], ![0, 1, 0, 0, 0, 0, 2, 0, 1, 2, 2, 1],
  ![0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 2, 2], ![0, 0, 0, 1, 0, 0, 2, 2, 1, 0, 1, 2],
  ![0, 0, 0, 0, 1, 0, 2, 2, 2, 1, 0, 1], ![0, 0, 0, 0, 0, 1, 2, 1, 2, 2, 1, 0]]

/-- Encoding: `a ↦ Σ_r a_r g_r`. -/
def enc (a : Fin 6 → F) : Fin 12 → F := fun i => ∑ r, a r * golayRow r i

/-- The extended ternary Golay code, the span of the rows of `golayRow`. -/
def golay : Submodule F (Fin 12 → F) where
  carrier := Set.range enc
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by funext i; simp [enc, add_mul, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, by funext i; simp [enc]⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    exact ⟨c • a, by funext i; simp [enc, Finset.mul_sum, mul_assoc]⟩

lemma mem_golay {x : Fin 12 → F} : x ∈ golay ↔ ∃ a, enc a = x := Iff.rfl

set_option maxRecDepth 100000 in
/-- The generator matrix is systematic. -/
lemma enc_sys : ∀ a : Fin 6 → F, ∀ r : Fin 6, enc a (Fin.castLE (by norm_num) r) = a r := by
  decide

lemma enc_inj : Function.Injective enc := fun a b h =>
  funext fun r => by rw [← enc_sys a r, ← enc_sys b r, h]

lemma CSG_golay : CSG golay = univ.image enc := by
  ext x
  simp only [mem_CSG, mem_golay, Finset.mem_image, Finset.mem_univ, true_and]

lemma card_golay : #(CSG golay) = 729 := by
  rw [CSG_golay, Finset.card_image_of_injective _ enc_inj, Finset.card_univ, card_F_fun]
  simp

lemma golayRow_orth : ∀ r r' : Fin 6, ∑ i, golayRow r i * golayRow r' i = 0 := by decide

lemma dotG_enc (a b : Fin 6 → F) : dotG (enc a) (enc b) = 0 := by
  unfold dotG enc
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun r' _ => ?_
  calc ∑ i, a r * golayRow r i * (b r' * golayRow r' i)
      = a r * b r' * ∑ i, golayRow r i * golayRow r' i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [golayRow_orth r r', mul_zero]

theorem selfDual_golay : SelfDualG golay := by
  apply selfDual_of_iso_card
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact dotG_enc a b
  · rw [card_golay]
    simp

set_option maxRecDepth 100000 in
/-- `Index(Golay) = 24` (24 even and no odd maximal codewords), by the kernel. -/
theorem index_golay : indexG golay = 24 := by
  unfold indexG
  rw [CSG_golay, Finset.sum_image (fun a _ b _ h => enc_inj h)]
  decide

/-- The block system `σ₂ = {0,1,2,3}, {4,5,6,8}` with singletons `7, 9, 10, 11`. -/
def c₂ : Blk (Fin 4) (Fin 2) → Fin 12 :=
  Sum.elim ![7, 9, 10, 11] (fun q => ![![![0, 1], ![2, 3]], ![![4, 5], ![6, 8]]] q.1 q.2.1 q.2.2)

/-- The block system `σ₁ = {0,1,2,3}` with singletons `4, …, 11`. -/
def c₁ : Blk (Fin 8) (Fin 1) → Fin 12 :=
  Sum.elim ![4, 5, 6, 7, 8, 9, 10, 11] (fun q => ![![0, 1], ![2, 3]] q.2.1 q.2.2)

lemma c₂_bij : Function.Bijective c₂ := by decide
lemma c₁_bij : Function.Bijective c₁ := by decide

noncomputable def e₂ : Blk (Fin 4) (Fin 2) ≃ Fin 12 := Equiv.ofBijective c₂ c₂_bij
noncomputable def e₁ : Blk (Fin 8) (Fin 1) ≃ Fin 12 := Equiv.ofBijective c₁ c₁_bij

set_option maxRecDepth 100000 in
/-- `R_{σ₂}(Golay) = 24`, by the kernel. -/
theorem R_golay₂ : R (relabel e₂ golay) = 24 := by
  unfold R
  rw [sum_relabel, CSG_golay, Finset.sum_image (fun a _ b _ h => enc_inj h)]
  show ∑ a, Rw (fun i => enc a (c₂ i)) = 24
  decide

set_option maxRecDepth 100000 in
/-- `R_{σ₁}(Golay) = 24`, by the kernel. -/
theorem R_golay₁ : R (relabel e₁ golay) = 24 := by
  unfold R
  rw [sum_relabel, CSG_golay, Finset.sum_image (fun a _ b _ h => enc_inj h)]
  show ∑ a, Rw (fun i => enc a (c₁ i)) = 24
  decide

theorem code12 : CodeExists 12 :=
  ⟨Fin 12, inferInstance, inferInstance, golay, selfDual_golay, index_golay, by simp⟩

theorem state12 : State2 12 :=
  ⟨Fin 4, inferInstance, inferInstance, relabel e₂ golay, selfDual_relabel _ selfDual_golay,
    R_golay₂, by simp⟩

theorem code24_state24 : CodeExists 24 ∧ State2 24 := by
  have h := engine (relabel e₁ golay) (selfDual_relabel _ selfDual_golay) R_golay₁
    ((0 : Fin 1), (0 : Fin 2))
  simpa using h

/-! ### The theorem -/

/-- Transport to coordinates `Fin n` and GJF's definitions. -/
theorem gjf_of_codeExists {n : ℕ} (h : CodeExists n) :
    ∃ C : Submodule (ZMod 3) (Fin n → ZMod 3), IsSelfDual C ∧ gjfIndex C = 24 := by
  obtain ⟨ι, _, _, C, hC, hI, rfl⟩ := h
  refine ⟨relabel (Fintype.equivFin ι).symm C, selfDual_relabel _ hC, ?_⟩
  rw [gjfIndex_eq]
  exact (indexG_relabel _ C).trans hI

/-- **Theorem 5.9** (existence half of GJF Conjecture 1.4). For every `k ≥ 1` there is a
self-dual ternary code of length `12k` whose index (#even − #odd maximal codewords) is `24`. -/
theorem exists_selfDual_index24 (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : Submodule (ZMod 3) (Fin (12 * k) → ZMod 3), IsSelfDual C ∧ gjfIndex C = 24 := by
  apply gjf_of_codeExists
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rcases i with _ | i
    · simpa using code24_state24.1
    · have h := (chain code24_state24.2 i).2
      rwa [show 24 + 24 * (i + 1) = 12 * (2 * (i + 1 + 1)) by ring] at h
  · rcases j with _ | j
    · simpa using code12
    · have h := (chain state12 j).2
      rwa [show 12 + 24 * (j + 1) = 12 * (2 * (j + 1) + 1) by ring] at h

end GJF.Ex

namespace GJF

/-- **GJF Conjecture 1.4, both halves.** Every self-dual ternary code of positive length has
index divisible by `24`, and for every `k ≥ 1` some self-dual ternary code of length `12k` has
index exactly `24`. -/
theorem conjecture_1_4 :
    (∀ (n : ℕ) (C : Submodule (ZMod 3) (Fin n → ZMod 3)), IsSelfDual C → 0 < n →
      (24 : ℤ) ∣ gjfIndex C) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ C : Submodule (ZMod 3) (Fin (12 * k) → ZMod 3),
      IsSelfDual C ∧ gjfIndex C = 24) :=
  ⟨fun _ C hC hn => index_dvd_24 C hC hn, Ex.exists_selfDual_index24⟩

end GJF
