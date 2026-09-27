import GJF.Chain

/-!
# Twined counts along the chains (notes/blueprint/chains-and-seeds.md Lemma 2.3)

Let `h` be group data of order 3 that acts as a pure permutation with identity local maps
(`PureL`), and let `ψ : B' × Fin 3 ≃ B` list the `h`-orbits of blocks (`OrbS`: `h ψ(b', i) =
ψ(b', i + 1)`). The twined counts are

* `Th h C = Σ_{c ∈ C, hc = c} f(c)` (the count in GJF Thm 5.6), and
* `Rh h ψ E = Σ_{x ∈ E, hx = x} ∏_s φ(x_s) ∏_{b'} λ(wt x|_{ψ(b', 0)})` (one weight per block orbit).

* `twined_sum_D`: the twined form of `sum_D`. On `h`-fixed vectors of the doubled code the
  tetracode vectors are constant on orbits, so the sum over them factors over block orbits.
* `Th_Qt`: `T_h(Q_σ(E)) = R^h_σ(E)`; `Rh_NSt`: `R^h` of the new state equals `R^h_σ(E)`.
* `Th_relabel`: `T_h` is invariant under relabelling.
-/

open Finset

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Ex

local notation "F" => ZMod 3

/-- The twined count `T_h(C) = Σ_{c ∈ C^h} f(c)`. -/
noncomputable def Th {X : Type} [Fintype X] [DecidableEq X] (h : SP X) (C : Submodule F (X → F)) :
    ℤ :=
  ∑ x ∈ (CSG C).filter (fun x => h.act x = x), fG x

/-- An orbit structure for a permutation of order 3 without fixed points. -/
def OrbS {B B' : Type} (π : Equiv.Perm B) (ψ : B' × Fin 3 ≃ B) : Prop :=
  ∀ b' i, π (ψ (b', i)) = ψ (b', i + 1)

lemma OrbS.const {B B' α : Type} {π : Equiv.Perm B} {ψ : B' × Fin 3 ≃ B} (hψ : OrbS π ψ)
    (f : B → α) (hf : ∀ β, f (π β) = f β) (b' : B') (i : Fin 3) : f (ψ (b', i)) = f (ψ (b', 0)) := by
  fin_cases i
  · rfl
  · show f (ψ (b', 0 + 1)) = _
    rw [← hψ, hf]
  · show f (ψ (b', 1 + 1)) = _
    rw [← hψ, hf, show (1 : Fin 3) = 0 + 1 from rfl, ← hψ, hf]

lemma OrbS.symm_fst {B B' : Type} {π : Equiv.Perm B} {ψ : B' × Fin 3 ≃ B} (hψ : OrbS π ψ)
    (β : B) : ψ.symm (π β) = ((ψ.symm β).1, (ψ.symm β).2 + 1) := by
  rw [Equiv.symm_apply_eq, ← hψ, Prod.mk.eta, Equiv.apply_symm_apply]

lemma OrbS.ne {B B' : Type} {π : Equiv.Perm B} {ψ : B' × Fin 3 ≃ B} (hψ : OrbS π ψ) (β : B) :
    π β ≠ β := by
  intro h
  have h2 : (ψ.symm β).2 = (ψ.symm β).2 + 1 := by
    have := congrArg Prod.snd (hψ.symm_fst β)
    rw [h] at this
    exact this
  revert h2
  generalize (ψ.symm β).2 = i
  revert i
  decide

/-- The orbit structure on `B × Fin 2` induced by one on `B`. -/
def orbProd {B B' : Type} (ψ : B' × Fin 3 ≃ B) : (B' × Fin 2) × Fin 3 ≃ B × Fin 2 where
  toFun x := (ψ (x.1.1, x.2), x.1.2)
  invFun y := (((ψ.symm y.1).1, y.2), (ψ.symm y.1).2)
  left_inv x := by simp
  right_inv y := by simp

@[simp] lemma orbProd_apply {B B' : Type} (ψ : B' × Fin 3 ≃ B) (b' : B') (a : Fin 2) (i : Fin 3) :
    orbProd ψ ((b', a), i) = (ψ (b', i), a) := rfl

lemma phi_cube : ∀ a : F, phi a * phi a * phi a = phi a := by decide

lemma sgl_cube (v : P × Fin 2 → F) : sgl v * sgl v * sgl v = sgl v := by
  unfold sgl
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun q _ => phi_cube _

namespace SM

variable {S B : Type} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]

/-- A permutation with identity local maps and no signs. -/
def PureL (h : SM S B) : Prop := h.gS.Pure ∧ ∀ β, h.μ β = lone

lemma PureL.toSP_perm {h : SM S B} (hp : h.PureL) (β : B) (p : P) :
    h.toSP.perm (.inr (β, p)) = .inr (h.π β, p) := by
  rw [toSP_perm_inr, hp.2, toSP_lone]; rfl

lemma PureL.toSP_sgn {h : SM S B} (hp : h.PureL) (i : Blk S B) : h.toSP.sgn i = 1 := by
  rcases i with s | ⟨β, p⟩
  · exact hp.1 s
  · rw [toSP_sgn_inr, hp.2, toSP_lone]; rfl

lemma PureL.fixed {h : SM S B} (hp : h.PureL) {x : Blk S B → F} (hx : h.toSP.act x = x) (β : B)
    (p : P) : x (.inr (h.π β, p)) = x (.inr (β, p)) := by
  have := SP.act_perm h.toSP x (.inr (β, p))
  rwa [hx, hp.toSP_perm, hp.toSP_sgn, one_mul] at this

lemma PureL.tAct {h : SM S B} (hp : h.PureL) (t : B → P → F) (β : B) :
    h.tAct t β = t (h.π.symm β) := by
  funext p
  simp only [SM.tAct, hp.2, toSP_lone, SP.act_one]

lemma PureL.st1 {h : SM S B} (hp : h.PureL) : (SM.step1 h).PureL :=
  ⟨hp.1, fun x => by simp only [SM.step1, hp.2, stepK_lone, S_zero]⟩

lemma PureL.st1_π {h : SM S B} (hp : h.PureL) (β : B) (a : Fin 2) :
    (SM.step1 h).π (β, a) = (h.π β, a) := by
  rw [SM.step1_π, hp.2, pairP_lone]; rfl

lemma OrbS.st1 {h : SM S B} (hp : h.PureL) {B' : Type} {ψ : B' × Fin 3 ≃ B} (hψ : OrbS h.π ψ) :
    OrbS (SM.step1 h).π (orbProd ψ) := by
  rintro ⟨b', a⟩ i
  show (SM.step1 h).π (ψ (b', i), a) = (ψ (b', i + 1), a)
  rw [hp.st1_π, hψ]

end SM

section Twined

variable {S B B' : Type} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
  [Fintype B'] [DecidableEq B']

/-- `R^h_σ(E)` with the orbit representatives `ψ(b', 0)`. -/
noncomputable def Rh (h : SM S B) (ψ : B' × Fin 3 ≃ B) (E : Submodule F (Blk S B → F)) : ℤ :=
  ∑ x ∈ (CSG E).filter (fun x => h.toSP.act x = x),
    (∏ s, phi (x (.inl s))) * ∏ b', lam (wtP fun p => x (.inr (ψ (b', 0), p)))

/-- **The twined summation over a doubled code.** -/
theorem twined_sum_D (E : Submodule F (Blk S B → F)) {h : SM S B} (hp : h.PureL)
    {ψ : B' × Fin 3 ≃ B} (hψ : OrbS h.π ψ) (G : B' → Fin 3 → (P × Fin 2 → F) → ℤ)
    (hG : ∀ b' u, ∑ t ∈ Tfin, ∏ i, G b' i (dbl u t) = lam (wtP u)) :
    ∑ v ∈ (CSG (D E)).filter (fun v => h.extD.act v = v),
      (∏ s, phi (v (.inl s))) * ∏ b', ∏ i, G b' i (fun q => v (.inr (ψ (b', i), q))) =
    ∑ e ∈ (CSG E).filter (fun e => h.toSP.act e = e),
      (∏ s, phi (e (.inl s))) * ∏ b', lam (wtP fun p => e (.inr (ψ (b', 0), p))) := by
  have key : ∀ e t, h.extD.act (Φ e t) = Φ e t ↔ h.toSP.act e = e ∧ h.tAct t = t := fun e t => by
    rw [SM.extD_Φ]
    exact ⟨fun hh => Φ_inj hh, fun hh => by rw [hh.1, hh.2]⟩
  rw [CSG_D, Finset.filter_image, Finset.sum_image (fun a _ b _ hab => Prod.ext_iff.2 (Φ_inj hab)),
    Finset.sum_filter, Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e he => ?_
  by_cases hefix : h.toSP.act e = e
  swap
  · rw [if_neg hefix]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rw [key]
    exact fun hh => hefix hh.1
  rw [if_pos hefix]
  simp only [key, hefix, true_and]
  rw [← Finset.sum_filter]
  simp only [Φ, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.mul_sum]
  congr 1
  -- the blocks of `e` are constant on orbits
  have heb : ∀ b' i, (fun p => e (.inr (ψ (b', i), p))) = fun p => e (.inr (ψ (b', 0), p)) :=
    fun b' i => hψ.const (fun β => fun p => e (.inr (β, p)))
      (fun β => funext fun p => hp.fixed hefix β p) b' i
  -- fixed tetracode vectors are constant on orbits
  have htfix : ∀ t : B → P → F, h.tAct t = t → ∀ β, t (h.π β) = t β := fun t ht β => by
    have := congrFun ht (h.π β)
    rw [hp.tAct, Equiv.symm_apply_apply] at this
    exact this.symm
  rw [show (∏ b', lam (wtP fun p => e (.inr (ψ (b', 0), p)))) =
      ∏ b', ∑ τ ∈ Tfin, ∏ i, G b' i (dbl (fun p => e (.inr (ψ (b', 0), p))) τ) from
      Finset.prod_congr rfl fun b' _ => (hG b' _).symm, Finset.prod_univ_sum]
  refine Finset.sum_nbij' (fun t => fun b' => t (ψ (b', 0))) (fun τ => fun β => τ (ψ.symm β).1)
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at ht ⊢
    exact fun b' => ht.1 _
  · intro τ hτ
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hτ ⊢
    refine ⟨fun β => hτ _, ?_⟩
    funext β
    rw [hp.tAct]
    have := hψ.symm_fst (h.π.symm β)
    rw [Equiv.apply_symm_apply] at this
    rw [this]
  · intro t ht
    simp only [Finset.mem_filter] at ht
    funext β
    have := hψ.const t (htfix t ht.2) (ψ.symm β).1 (ψ.symm β).2
    rw [Prod.mk.eta, Equiv.apply_symm_apply] at this
    exact this.symm
  · intro τ _
    funext b'
    simp
  · intro t ht
    simp only [Finset.mem_filter] at ht
    refine Finset.prod_congr rfl fun b' _ => Finset.prod_congr rfl fun i _ => ?_
    have ht' := hψ.const t (htfix t ht.2) b' i
    congr 1
    funext q
    rw [ht', ← heb b' i]

lemma sum_relabel_fix {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {M : Type*} [AddCommMonoid M] (e : Y ≃ X) (C : Submodule F (X → F)) (g : SP X)
    (W : (Y → F) → M) :
    ∑ y ∈ (CSG (relabel e C)).filter (fun y => (SP.pull e g).act y = y), W y =
      ∑ z ∈ (CSG C).filter (fun z => g.act z = z), W (fun i => z (e i)) := by
  rw [Finset.sum_filter, Finset.sum_filter, sum_relabel]
  refine Finset.sum_congr rfl fun z _ => ?_
  have : (SP.pull e g).act (fun i => z (e i)) = (fun i => z (e i)) ↔ g.act z = z := by
    rw [SP.pull_act]
    simp only [Equiv.apply_symm_apply]
    constructor
    · intro hh
      funext k
      have := congrFun hh (e.symm k)
      simpa using this
    · intro hh
      rw [hh]
  simp only [this]

/-- `T_h` is invariant under relabelling. -/
lemma Th_relabel {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (e : Y ≃ X)
    (C : Submodule F (X → F)) (g : SP X) : Th (SP.pull e g) (relabel e C) = Th g C := by
  unfold Th
  rw [sum_relabel_fix]
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold fG
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

/-- **Middle step:** `R^h` after the first doubling. -/
theorem Rh_E1t (E : Submodule F (Blk S B → F)) {h : SM S B} (hp : h.PureL) {ψ : B' × Fin 3 ≃ B}
    (hψ : OrbS h.π ψ) : Rh (SM.step1 h) (orbProd ψ) (E1t E) = Rh h ψ E := by
  conv_rhs => unfold Rh
  rw [← twined_sum_D E hp hψ (fun _ i => if i = 0 then refd else fun _ => 1) (fun b' u => by
    simp only [Fin.prod_univ_three, Fin.isValue, ↓reduceIte, one_ne_zero, mul_one,
      show (2 : Fin 3) ≠ 0 by decide]
    exact localB u)]
  unfold Rh E1t
  rw [← SM.pull_r₁, sum_relabel_fix]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Fin.prod_univ_three, Fin.isValue, ↓reduceIte, one_ne_zero, mul_one,
    show (2 : Fin 3) ≠ 0 by decide, Fintype.prod_prod_type, orbProd_apply]
  rfl

/-- **`T_h(Q_σ(E)) = R^h_σ(E)`.** -/
theorem Th_Qt (E : Submodule F (Blk S B → F)) {h : SM S B} (hp : h.PureL) {ψ : B' × Fin 3 ≃ B}
    (hψ : OrbS h.π ψ) : Th (SM.step1 h).extD (Qt E) = Rh h ψ E := by
  rw [← Rh_E1t E hp hψ, Rh]
  have h1 := twined_sum_D (E1t E) hp.st1 (SM.OrbS.st1 hp hψ) (fun _ _ => sgl) (fun b' u => by
    simp only [Fin.prod_univ_three, sgl_cube]; exact localA u)
  unfold Th Qt
  rw [← h1]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold fG
  rw [Fintype.prod_sum_type]
  congr 1
  rw [Fintype.prod_prod_type, ← Fintype.prod_equiv (orbProd ψ)
    (fun x => sgl fun q => v (.inr (orbProd ψ x, q))) (fun β => ∏ q, phi (v (.inr (β, q))))
    (fun x => rfl), Fintype.prod_prod_type]

lemma prod_three_ite {M : Type*} [CommMonoid M] (a : M) :
    ∀ j : Fin 3, (if j = 0 then a else 1) * (if j + 1 = 0 then a else 1) *
      (if j + 1 + 1 = 0 then a else 1) = a := by
  intro j
  fin_cases j <;> simp

lemma prod_rep {R' Rr : Type} [Fintype R'] [DecidableEq R'] [Fintype Rr] [DecidableEq Rr]
    (ψR : R' × Fin 3 ≃ Rr) (f : Rr → ℤ) :
    ∏ r, (if (ψR.symm r).2 = 0 then f r else 1) = ∏ r', f (ψR (r', 0)) := by
  rw [← Fintype.prod_equiv ψR (fun x => if x.2 = 0 then f (ψR x) else 1) _ (fun x => by simp),
    Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun r' _ => ?_
  simp

variable {Rr Uu R' : Type} [Fintype Rr] [DecidableEq Rr] [Fintype Uu] [DecidableEq Uu]
  [Fintype R'] [DecidableEq R']

lemma SM.PureL.newSM {sp : B × Fin 2 ≃ Rr ⊕ Uu} {h : SM S B} (hp : h.PureL) (πR : Equiv.Perm Rr)
    (πU : Equiv.Perm Uu) : (SM.newSM sp h πR πU).PureL := by
  refine ⟨?_, fun x => ?_⟩
  · rintro (s | ⟨u, p, s'⟩)
    · exact hp.1 s
    · show (lsp ((SM.step1 h).μ _)).sgn p = 1
      rw [hp.st1.2, toSP_lone]; rfl
  · show A (stepK (h.μ _) _) = lone
    rw [hp.2, stepK_lone, A_zero]

lemma SM.OrbS.newSM {sp : B × Fin 2 ≃ Rr ⊕ Uu} (h : SM S B) (πR : Equiv.Perm Rr)
    (πU : Equiv.Perm Uu) {ψR : R' × Fin 3 ≃ Rr} (hψR : OrbS πR ψR) :
    OrbS (SM.newSM sp h πR πU).π (orbProd ψR) := by
  rintro ⟨r', s⟩ i
  show (πR (ψR (r', i)), s) = (ψR (r', i + 1), s)
  rw [hψR]

/-- **`R^h` of the new state equals `R^h_σ(E)`.** -/
theorem Rh_NSt (sp : B × Fin 2 ≃ Rr ⊕ Uu) (E : Submodule F (Blk S B → F)) {h : SM S B}
    (hp : h.PureL) {ψ : B' × Fin 3 ≃ B} (hψ : OrbS h.π ψ) {πR : Equiv.Perm Rr}
    {πU : Equiv.Perm Uu} (hc : SM.Compat sp h πR πU) {ψR : R' × Fin 3 ≃ Rr} (hψR : OrbS πR ψR) :
    Rh (SM.newSM sp h πR πU) (orbProd ψR) (NSt sp E) = Rh h ψ E := by
  rw [← Rh_E1t E hp hψ]
  conv_rhs => unfold Rh
  let Kf : B × Fin 2 → (P × Fin 2 → F) → ℤ := fun x =>
    (sp x).elim (fun r => if (ψR.symm r).2 = 0 then refdT else fun _ => 1) (fun _ => sgl)
  have hψ1 := SM.OrbS.st1 hp hψ
  have hG : ∀ b₁ u, ∑ t ∈ Tfin, ∏ i, Kf (orbProd ψ (b₁, i)) (dbl u t) = lam (wtP u) := by
    intro b₁ u
    have e1 : sp (orbProd ψ (b₁, 1)) = Sum.map πR πU (sp (orbProd ψ (b₁, 0))) := by
      rw [show (1 : Fin 3) = 0 + 1 from rfl, ← hψ1, hc]
    have e2 : sp (orbProd ψ (b₁, 2)) = Sum.map πR πU (sp (orbProd ψ (b₁, 1))) := by
      rw [show (2 : Fin 3) = 1 + 1 from rfl, ← hψ1, hc]
    rw [e1] at e2
    simp only [Fin.prod_univ_three, Kf, e1, e2]
    generalize sp (orbProd ψ (b₁, 0)) = y
    rcases y with r | u'
    · simp only [Sum.map_inl, Sum.elim_inl, hψR.symm_fst]
      have ht : ∀ t, ((if (ψR.symm r).2 = 0 then refdT else fun _ => 1) (dbl u t) *
          (if (ψR.symm r).2 + 1 = 0 then refdT else fun _ => 1) (dbl u t) *
          (if (ψR.symm r).2 + 1 + 1 = 0 then refdT else fun _ => (1 : ℤ)) (dbl u t)) =
          refdT (dbl u t) := fun t => by
        rw [apply_ite (fun f : (P × Fin 2 → F) → ℤ => f (dbl u t)),
          apply_ite (fun f : (P × Fin 2 → F) → ℤ => f (dbl u t)),
          apply_ite (fun f : (P × Fin 2 → F) → ℤ => f (dbl u t))]
        exact prod_three_ite _ _
      rw [Finset.sum_congr rfl fun t _ => ht t]
      exact localBt u
    · simp only [Sum.map_inr, Sum.elim_inr, sgl_cube]
      exact localA u
  rw [← twined_sum_D (E1t E) hp.st1 hψ1 (fun b₁ i => Kf (orbProd ψ (b₁, i))) hG]
  unfold Rh NSt Qt
  rw [← SM.pull_rt hc, sum_relabel_fix]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hL : (∏ s, phi (v (SM.rt S sp (.inl s)))) = (∏ s, phi (v (.inl s))) *
      ∏ u : Uu, sgl (fun q => v (.inr (sp.symm (.inr u), q))) := by
    simp only [sgl, Fintype.prod_sum_type, Fintype.prod_prod_type]
    rfl
  have hB : (∏ b', lam (wtP fun p => v (SM.rt S sp (.inr (orbProd ψR (b', 0), p))))) =
      ∏ r', refdT (fun q => v (.inr (sp.symm (.inl (ψR (r', 0))), q))) := by
    simp only [Fintype.prod_prod_type]
    rfl
  have hR : (∏ b₁, ∏ i, Kf (orbProd ψ (b₁, i)) (fun q => v (.inr (orbProd ψ (b₁, i), q)))) =
      (∏ r, (if (ψR.symm r).2 = 0 then refdT (fun q => v (.inr (sp.symm (.inl r), q))) else 1)) *
        ∏ u : Uu, sgl (fun q => v (.inr (sp.symm (.inr u), q))) := by
    rw [← Fintype.prod_prod_type (f := fun x : (B' × Fin 2) × Fin 3 =>
      Kf (orbProd ψ x) (fun q => v (.inr (orbProd ψ x, q)))),
      Fintype.prod_equiv (orbProd ψ) _ (fun β => Kf β (fun q => v (.inr (β, q)))) (fun _ => rfl),
      Fintype.prod_equiv sp (fun β => Kf β (fun q => v (.inr (β, q))))
        (fun y => Kf (sp.symm y) (fun q => v (.inr (sp.symm y, q)))) (fun x => by simp),
      Fintype.prod_sum_type]
    congr 1
    · refine Finset.prod_congr rfl fun r _ => ?_
      simp only [Kf, Equiv.apply_symm_apply, Sum.elim_inl]
      split_ifs <;> rfl
    · refine Finset.prod_congr rfl fun u _ => ?_
      simp only [Kf, Equiv.apply_symm_apply, Sum.elim_inr]
  rw [hL, hB, hR, prod_rep ψR (fun r => refdT (fun q => v (.inr (sp.symm (.inl r), q))))]
  ring

/-! ### Fixed points and powers -/

lemma FPF_st1_extD {h : SM S B} (hp : h.PureL) (hS : h.gS.FPF) {ψ : B' × Fin 3 ≃ B}
    (hψ : OrbS h.π ψ) : (SM.step1 h).extD.FPF := by
  apply SM.FPF_extD (g := SM.step1 h) hS
  rintro ⟨β, a⟩ heq
  rw [hp.st1_π] at heq
  exact hψ.ne β (congrArg Prod.fst heq)

lemma FPF_newSM_gS {sp : B × Fin 2 ≃ Rr ⊕ Uu} {h : SM S B} (hp : h.PureL) (hS : h.gS.FPF)
    {ψ : B' × Fin 3 ≃ B} (hψ : OrbS h.π ψ) {πR : Equiv.Perm Rr} {πU : Equiv.Perm Uu}
    (hc : SM.Compat sp h πR πU) : (SM.newSM sp h πR πU).gS.FPF := by
  rintro (s | ⟨u, q⟩) heq
  · exact hS s (Sum.inl_injective heq)
  · have hu : πU u = u := congrArg Prod.fst (Sum.inr_injective heq)
    have := hc.inr u
    rw [hu] at this
    obtain ⟨β, a⟩ := sp.symm (.inr u)
    exact (SM.OrbS.st1 hp hψ).ne _ this

lemma OrbS.prodCongr {O O' : Type} {πO : Equiv.Perm O} {ψO : O' × Fin 3 ≃ O} (h : OrbS πO ψO) :
    OrbS (Equiv.prodCongr πO (1 : Equiv.Perm (Fin 2))) (orbProd ψO) := by
  rintro ⟨o', a⟩ i
  show (πO (ψO (o', i)), a) = (ψO (o', i + 1), a)
  rw [h]

end Twined

namespace SM

variable {S B : Type} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]

lemma toSP_pow (g : SM S B) (m : ℕ) : (g ^ m).toSP = g.toSP ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, toSP_one]
  | succ m ih => rw [pow_succ, pow_succ, toSP_mul, ih]

lemma extD_pow (g : SM S B) (m : ℕ) : (g ^ m).extD = g.extD ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, extD_one]
  | succ m ih => rw [pow_succ, pow_succ, extD_mul, ih]

lemma step1_pow (g : SM S B) (m : ℕ) : step1 (g ^ m) = step1 g ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, step1_one]
  | succ m ih => rw [pow_succ, pow_succ, step1_mul, ih]

end SM

lemma SP.pull_pow {X Y : Type} (e : Y ≃ X) (g : SP X) (m : ℕ) : SP.pull e (g ^ m) = SP.pull e g ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, SP.pull_one]
  | succ m ih => rw [pow_succ, pow_succ, SP.pull_mul, ih]

lemma Unif.pow {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    {g : SM S (O × Fin 2)} {π : Equiv.Perm O} (hg : Unif g π) (m : ℕ) : Unif (g ^ m) (π ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; exact Unif.one
  | succ m ih => rw [pow_succ, pow_succ]; exact ih.mul hg

lemma nxt_pow {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    {g : SM S (O × Fin 2)} {π : Equiv.Perm O} (hg : Unif g π) (m : ℕ) :
    nxt (g ^ m) (π ^ m) = nxt g π ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pow_zero, nxt_one]
  | succ m ih => rw [pow_succ, pow_succ, pow_succ, nxt_mul hg, ih]

end GJF.Ex
