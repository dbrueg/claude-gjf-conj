import GJF.LocalMaps

/-!
# Equivariant partial quadrupling

Group data on a code with a block system (`Blk S B = S ⊕ (B × P)`): a signed permutation of the
singletons, a permutation of the blocks and a local map in `LM` on each block (`SM S B`).

* `SM.extD`: the extension to the doubled code (`Dbl S B`), new coordinates following their
  partners with the same sign; `Inv_D`: it preserves `D E` when `g` preserves `E` (every local map
  preserves the tetracode).
* `step1`: the group data on the step-one blocks, `pull_r₁`: it is the transport of `extD`.
* `rt`, `newSM`, `pull_rt`: the refinement of a set of step-one blocks (`sp : B × Fin 2 ≃ Rr ⊕ Uu`,
  refined `R`, unrefined `U`) with the transposed split, and the group data on the new state.
* All of these are monoid homomorphisms, so relations between generators are inherited.
-/

open Finset

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Ex

local notation "F" => ZMod 3

lemma lmul_snd : ∀ m : LM, (lmul lneg m).2 = m.2 := by decide

lemma stepK_lneg : ∀ (m : LM) (a : Fin 2), stepK (lmul lneg m) a = 2 + stepK m a := by decide

lemma stepK_lone : ∀ a : Fin 2, stepK lone a = 0 := by decide

lemma pairP_lone : pairP lone.2 = 1 := rfl

/-- Group data on `Blk S B`. -/
@[ext]
structure SM (S B : Type*) where
  gS : SP S
  π : Equiv.Perm B
  μ : B → LM

namespace SM

variable {S B Rr Uu : Type*} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]

instance [DecidableEq (SP S)] [Fintype B] [DecidableEq B] : DecidableEq (SM S B) := fun g h =>
  decidable_of_iff (g.gS = h.gS ∧ g.π = h.π ∧ g.μ = h.μ) (by rw [SM.ext_iff])

/-- The signed permutation of `Blk S B`. -/
def toSP (g : SM S B) : SP (Blk S B) := SP.sum g.gS (SP.blk g.π (fun β => lsp (g.μ β)))

instance : Mul (SM S B) := ⟨fun g h => ⟨g.gS * h.gS, g.π * h.π, fun β => lmul (g.μ (h.π β)) (h.μ β)⟩⟩
instance : One (SM S B) := ⟨⟨1, 1, fun _ => lone⟩⟩
instance : Neg (SM S B) := ⟨fun g => ⟨-g.gS, g.π, fun β => lmul lneg (g.μ β)⟩⟩

@[simp] lemma mul_gS (g h : SM S B) : (g * h).gS = g.gS * h.gS := rfl
@[simp] lemma mul_π (g h : SM S B) : (g * h).π = g.π * h.π := rfl
@[simp] lemma mul_μ (g h : SM S B) (β : B) : (g * h).μ β = lmul (g.μ (h.π β)) (h.μ β) := rfl
@[simp] lemma one_gS : (1 : SM S B).gS = 1 := rfl
@[simp] lemma one_π : (1 : SM S B).π = 1 := rfl
@[simp] lemma one_μ (β : B) : (1 : SM S B).μ β = lone := rfl
@[simp] lemma neg_gS (g : SM S B) : (-g).gS = -g.gS := rfl
@[simp] lemma neg_π (g : SM S B) : (-g).π = g.π := rfl
@[simp] lemma neg_μ (g : SM S B) (β : B) : (-g).μ β = lmul lneg (g.μ β) := rfl

instance : Monoid (SM S B) where
  mul_assoc a b c := SM.ext (mul_assoc _ _ _) (mul_assoc _ _ _) (funext fun _ => lmul_assoc _ _ _)
  one_mul a := SM.ext (one_mul _) (one_mul _) (funext fun _ => lone_lmul _)
  mul_one a := SM.ext (mul_one _) (mul_one _) (funext fun _ => lmul_lone _)

lemma toSP_mul (g h : SM S B) : (g * h).toSP = g.toSP * h.toSP := by
  simp only [toSP, ← SP.sum_mul, SP.blk_mul, mul_gS, mul_π, mul_μ, GJF.Ex.toSP_mul]

lemma toSP_one : (1 : SM S B).toSP = 1 := by
  simp only [toSP, one_gS, one_π, one_μ, toSP_lone, SP.blk_one, SP.sum_one]

lemma toSP_neg (g : SM S B) : (-g).toSP = -g.toSP := by
  simp only [toSP, neg_gS, neg_π, neg_μ, GJF.Ex.toSP_mul, toSP_lneg, SP.neg_mul, one_mul,
    SP.blk_neg, SP.sum_neg]

@[simp] lemma toSP_perm_inl (g : SM S B) (s : S) : g.toSP.perm (.inl s) = .inl (g.gS.perm s) := rfl
@[simp] lemma toSP_perm_inr (g : SM S B) (β : B) (p : P) :
    g.toSP.perm (.inr (β, p)) = .inr (g.π β, (lsp (g.μ β)).perm p) := rfl
@[simp] lemma toSP_sgn_inl (g : SM S B) (s : S) : g.toSP.sgn (.inl s) = g.gS.sgn s := rfl
@[simp] lemma toSP_sgn_inr (g : SM S B) (β : B) (p : P) :
    g.toSP.sgn (.inr (β, p)) = (lsp (g.μ β)).sgn p := rfl

/-! ### Doubling -/

/-- The extension to `Dbl S B`: `z*` follows `z` with the same sign. -/
def extD (g : SM S B) : SP (Dbl S B) :=
  SP.sum g.gS (SP.blk g.π (fun β => SP.prodR (lsp (g.μ β)) (Fin 2)))

@[simp] lemma extD_perm_inl (g : SM S B) (s : S) : g.extD.perm (.inl s) = .inl (g.gS.perm s) := rfl
@[simp] lemma extD_perm_inr (g : SM S B) (β : B) (p : P) (s : Fin 2) :
    g.extD.perm (.inr (β, p, s)) = .inr (g.π β, (lsp (g.μ β)).perm p, s) := rfl
@[simp] lemma extD_sgn_inl (g : SM S B) (s : S) : g.extD.sgn (.inl s) = g.gS.sgn s := rfl
@[simp] lemma extD_sgn_inr (g : SM S B) (β : B) (p : P) (s : Fin 2) :
    g.extD.sgn (.inr (β, p, s)) = (lsp (g.μ β)).sgn p := rfl

lemma extD_mul (g h : SM S B) : (g * h).extD = g.extD * h.extD := by
  simp only [extD, ← SP.sum_mul, SP.blk_mul, mul_gS, mul_π, mul_μ, GJF.Ex.toSP_mul, SP.prodR_mul]

lemma extD_one : (1 : SM S B).extD = 1 := by
  simp only [extD, one_gS, one_π, one_μ, toSP_lone, SP.prodR_one, SP.blk_one, SP.sum_one]

lemma extD_neg (g : SM S B) : (-g).extD = -g.extD := by
  simp only [extD, neg_gS, neg_π, neg_μ, GJF.Ex.toSP_mul, toSP_lneg, SP.neg_mul, one_mul,
    SP.prodR_neg, SP.blk_neg, SP.sum_neg]

/-- The tetracode vectors transported by `g`. -/
def tAct (g : SM S B) (t : B → P → F) : B → P → F :=
  fun β' p' => (lsp (g.μ (g.π.symm β'))).act (t (g.π.symm β')) p'

lemma tAct_apply (g : SM S B) (t : B → P → F) (β : B) (p : P) :
    g.tAct t (g.π β) ((lsp (g.μ β)).perm p) = (lsp (g.μ β)).sgn p * t β p := by
  simp [tAct]

lemma extD_Φ (g : SM S B) (e : Blk S B → F) (t : B → P → F) :
    g.extD.act (Φ e t) = Φ (g.toSP.act e) (g.tAct t) := by
  funext j
  obtain ⟨i, rfl⟩ := g.extD.perm.surjective j
  rw [SP.act_perm]
  rcases i with s | ⟨β, p, s⟩
  · simp only [extD_sgn_inl, extD_perm_inl, Φ, Sum.elim_inl]
    rw [show Sum.inl (g.gS.perm s) = g.toSP.perm (.inl s) from rfl, SP.act_perm]
    rfl
  · simp only [extD_sgn_inr, extD_perm_inr, Φ, Sum.elim_inr, dbl]
    rw [show (Sum.inr (g.π β, (lsp (g.μ β)).perm p) : Blk S B) = g.toSP.perm (.inr (β, p)) from rfl,
      SP.act_perm, tAct_apply]
    simp only [toSP_sgn_inr]
    split_ifs <;> ring

lemma tAct_inT (g : SM S B) {t : B → P → F} (ht : ∀ β, inT (t β)) (β' : B) : inT (g.tAct t β') :=
  tet _ _ (ht _)

/-- **Invariance of the doubled code.** -/
lemma Inv_D {g : SM S B} {E : Submodule F (Blk S B → F)} (hE : g.toSP.Inv E) :
    g.extD.Inv (D E) := by
  rintro _ ⟨e, he, t, ht, rfl⟩
  rw [extD_Φ]
  exact ⟨_, hE e he, _, tAct_inT g ht, rfl⟩

lemma FPF_extD {g : SM S B} (hS : g.gS.FPF) (hB : ∀ β, g.π β ≠ β) : g.extD.FPF := by
  rintro (s | ⟨β, p, s⟩) h
  · exact hS s (Sum.inl_injective h)
  · exact hB β (congrArg Prod.fst (Sum.inr_injective h))

lemma FPF_toSP {g : SM S B} (hS : g.gS.FPF) (hB : ∀ β, g.π β ≠ β) : g.toSP.FPF := by
  rintro (s | ⟨β, p⟩) h
  · exact hS s (Sum.inl_injective h)
  · exact hB β (congrArg Prod.fst (Sum.inr_injective h))

/-! ### Step one -/

/-- The group data on the step-one blocks `(β, a)` (labels `(b, s)` as in `r₁`). -/
def step1 (g : SM S B) : SM S (B × Fin 2) :=
  ⟨g.gS, Equiv.prodShear g.π (fun β => pairP (g.μ β).2), fun x => GJF.Ex.S (stepK (g.μ x.1) x.2)⟩

@[simp] lemma step1_π (g : SM S B) (β : B) (a : Fin 2) :
    (step1 g).π (β, a) = (g.π β, pairP (g.μ β).2 a) := rfl

lemma pull_r₁ (g : SM S B) : SP.pull (r₁ S B) g.extD = (step1 g).toSP := by
  ext i
  · rcases i with s | ⟨⟨β, a⟩, b, s⟩
    · rfl
    · simp only [SP.pull, Equiv.trans_apply, toSP_perm_inr, step1, S_perm]
      rfl
  · rcases i with s | ⟨⟨β, a⟩, b, s⟩
    · rfl
    · simp only [SP.pull, toSP_sgn_inr, step1, S_sgn]
      rfl

lemma step1_mul (g h : SM S B) : step1 (g * h) = step1 g * step1 h := by
  refine SM.ext rfl ?_ ?_
  · ext ⟨β, a⟩ <;>
      simp [step1, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.prodShear_apply, pairP_mul]
  · funext ⟨β, a⟩
    simp only [step1, mul_μ, mul_π, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.prodShear_apply, stepK_mul, S_add]

lemma step1_one : step1 (1 : SM S B) = 1 := by
  refine SM.ext rfl ?_ ?_
  · ext ⟨β, a⟩ <;> simp [step1, pairP_lone]
  · funext ⟨β, a⟩; simp [step1, stepK_lone, S_zero]

lemma step1_neg (g : SM S B) : step1 (-g) = -step1 g := by
  refine SM.ext rfl ?_ ?_
  · ext ⟨β, a⟩ <;> simp [step1, lmul_snd]
  · funext ⟨β, a⟩
    simp only [step1, neg_μ, stepK_lneg, S_add, S_two]

/-! ### Refinement with the transposed split -/

/-- The new state after refining the step-one blocks in `R` (`sp : B × Fin 2 ≃ Rr ⊕ Uu`): singletons
`S ⊕ (Uu × (P × Fin 2))`, blocks `R × Fin 2`. Block `(r, s)` consists of the coordinates `((b, s), u)`
of the doubled step-one block `r`, position `(u, c)` at `b = ord u c` (order `x, y, y**, x**`). -/
def rt (S : Type*) (sp : B × Fin 2 ≃ Rr ⊕ Uu) :
    Blk (S ⊕ (Uu × (P × Fin 2))) (Rr × Fin 2) ≃ Dbl S (B × Fin 2) where
  toFun := Sum.elim (Sum.elim Sum.inl (fun uq => Sum.inr (sp.symm (.inr uq.1), uq.2)))
    (fun x => Sum.inr (sp.symm (.inl x.1.1), ((ord x.2.1 x.2.2, x.1.2), x.2.1)))
  invFun := Sum.elim (fun s => Sum.inl (Sum.inl s))
    (fun y => (sp y.1).elim (fun r => Sum.inr ((r, y.2.1.2), (y.2.2, ord y.2.2 y.2.1.1)))
      (fun u => Sum.inl (Sum.inr (u, y.2))))
  left_inv := by
    rintro ((s | ⟨u, q⟩) | ⟨⟨r, s⟩, u', c⟩)
    · rfl
    · simp
    · simp [ord_ord]
  right_inv := by
    rintro (s | ⟨x, ⟨b, s⟩, u⟩)
    · rfl
    · rcases h : sp x with r | u0
      · have hx : sp.symm (.inl r) = x := by rw [← h, Equiv.symm_apply_apply]
        simp [h, hx, ord_ord]
      · have hx : sp.symm (.inr u0) = x := by rw [← h, Equiv.symm_apply_apply]
        simp [h, hx]

/-- The group data on the new state, given the induced permutations `πR`, `πU` of the refined and
unrefined step-one blocks. -/
def newSM (sp : B × Fin 2 ≃ Rr ⊕ Uu) (g : SM S B) (πR : Equiv.Perm Rr) (πU : Equiv.Perm Uu) :
    SM (S ⊕ (Uu × (P × Fin 2))) (Rr × Fin 2) :=
  ⟨SP.sum g.gS (SP.blk πU (fun u => SP.prodR (lsp ((step1 g).μ (sp.symm (.inr u)))) (Fin 2))),
   Equiv.prodCongr πR (Equiv.refl _),
   fun x => A (stepK (g.μ (sp.symm (.inl x.1)).1) (sp.symm (.inl x.1)).2)⟩

/-- `πR`, `πU` are the permutations induced by `g` on the refined and unrefined step-one blocks. -/
def Compat (sp : B × Fin 2 ≃ Rr ⊕ Uu) (g : SM S B) (πR : Equiv.Perm Rr) (πU : Equiv.Perm Uu) : Prop :=
  ∀ x, sp ((step1 g).π x) = Sum.map πR πU (sp x)

lemma Compat.inl {sp : B × Fin 2 ≃ Rr ⊕ Uu} {g : SM S B} {πR πU} (hc : Compat sp g πR πU) (r : Rr) :
    (step1 g).π (sp.symm (.inl r)) = sp.symm (.inl (πR r)) := by
  rw [Equiv.eq_symm_apply, hc, Equiv.apply_symm_apply]; rfl

lemma Compat.inr {sp : B × Fin 2 ≃ Rr ⊕ Uu} {g : SM S B} {πR πU} (hc : Compat sp g πR πU) (u : Uu) :
    (step1 g).π (sp.symm (.inr u)) = sp.symm (.inr (πU u)) := by
  rw [Equiv.eq_symm_apply, hc, Equiv.apply_symm_apply]; rfl

lemma _root_.GJF.Ex.SP.pull_eq {X Y : Type*} {e : Y ≃ X} {g : SP X} {h : SP Y}
    (hp : ∀ i, g.perm (e i) = e (h.perm i)) (hs : ∀ i, g.sgn (e i) = h.sgn i) : SP.pull e g = h := by
  ext i
  · simp only [SP.pull, Equiv.trans_apply]; rw [hp, Equiv.symm_apply_apply]
  · exact hs i

lemma pull_rt {sp : B × Fin 2 ≃ Rr ⊕ Uu} {g : SM S B} {πR πU} (hc : Compat sp g πR πU) :
    SP.pull (rt S sp) (step1 g).extD = (newSM sp g πR πU).toSP := by
  apply SP.pull_eq
  · rintro ((s | ⟨u, p, s'⟩) | ⟨⟨r, s⟩, u', c⟩)
    · rfl
    · show Sum.inr ((step1 g).π (sp.symm (.inr u)), _) = _
      rw [hc.inr]; rfl
    · show Sum.inr ((step1 g).π (sp.symm (.inl r)), _) = _
      rw [hc.inl]
      simp only [step1, SP.prodR_perm, S_perm, newSM, toSP_perm_inr, A_perm, rt, Equiv.coe_fn_mk,
        Sum.elim_inr, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, ord_ord]
  · rintro ((s | ⟨u, p, s'⟩) | ⟨⟨r, s⟩, u', c⟩)
    · rfl
    · rfl
    · show (lsp (GJF.Ex.S _)).sgn (_, _) = _
      simp only [S_sgn, newSM, toSP_sgn_inr, A_sgn]

lemma newSM_mul {sp : B × Fin 2 ≃ Rr ⊕ Uu} {g h : SM S B} {πRg πUg πRh πUh}
    (hh : Compat sp h πRh πUh) :
    newSM sp (g * h) (πRg * πRh) (πUg * πUh) = newSM sp g πRg πUg * newSM sp h πRh πUh := by
  refine SM.ext ?_ ?_ ?_
  · simp only [newSM, mul_gS, ← SP.sum_mul, SP.blk_mul]
    congr 2
    funext u
    rw [← hh.inr, ← SP.prodR_mul, ← GJF.Ex.toSP_mul, step1_mul]
    rfl
  · ext ⟨r, s⟩ <;> rfl
  · funext ⟨r, s⟩
    simp only [newSM, mul_μ, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
    rw [← hh.inl, ← A_add]
    simp only [step1_π, mul_μ, stepK_mul]
    rfl

lemma Compat.mul {sp : B × Fin 2 ≃ Rr ⊕ Uu} {g h : SM S B} {πRg πUg πRh πUh}
    (hg : Compat sp g πRg πUg) (hh : Compat sp h πRh πUh) :
    Compat sp (g * h) (πRg * πRh) (πUg * πUh) := by
  intro x
  rw [step1_mul, mul_π, Equiv.Perm.coe_mul, Function.comp_apply, hg, hh]
  rcases sp x with r | u <;> rfl

lemma newSM_one (sp : B × Fin 2 ≃ Rr ⊕ Uu) : newSM sp (1 : SM S B) 1 1 = 1 := by
  refine SM.ext ?_ ?_ ?_
  · simp only [newSM, one_gS, step1_one, one_μ, toSP_lone, SP.prodR_one, SP.blk_one, SP.sum_one]
  · ext ⟨r, s⟩ <;> rfl
  · funext ⟨r, s⟩; simp only [newSM, one_μ, stepK_lone, A_zero]

lemma Compat.one (sp : B × Fin 2 ≃ Rr ⊕ Uu) : Compat sp (1 : SM S B) 1 1 := by
  intro x; rw [step1_one]; show sp x = _; rcases sp x with r | u <;> rfl

lemma newSM_neg {sp : B × Fin 2 ≃ Rr ⊕ Uu} (g : SM S B) (πR πU) :
    newSM sp (-g) πR πU = -newSM sp g πR πU := by
  refine SM.ext ?_ ?_ ?_
  · simp only [newSM, neg_gS, step1_neg, neg_μ, GJF.Ex.toSP_mul, toSP_lneg, SP.neg_mul, one_mul,
      SP.prodR_neg, SP.blk_neg, SP.sum_neg]
  · rfl
  · funext ⟨r, s⟩; simp only [newSM, neg_μ, stepK_lneg, A_add, A_two]

lemma Compat.neg {sp : B × Fin 2 ≃ Rr ⊕ Uu} {g : SM S B} {πR πU} (hg : Compat sp g πR πU) :
    Compat sp (-g) πR πU := by
  intro x; rw [step1_neg, neg_π]; exact hg x

end SM

/-! ### The code-level engine -/

section CodeEngine

variable {S B Rr Uu : Type} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
  [Fintype Rr] [DecidableEq Rr] [Fintype Uu] [DecidableEq Uu]

/-- After the first doubling, on the step-one blocks. -/
noncomputable def E1t (E : Submodule F (Blk S B → F)) : Submodule F (Blk S (B × Fin 2) → F) :=
  relabel (r₁ S B) (D E)

/-- The quadrupled code `Q_σ(E)`, of length `|S| + 16|B|`. -/
noncomputable def Qt (E : Submodule F (Blk S B → F)) : Submodule F (Dbl S (B × Fin 2) → F) :=
  D (E1t E)

/-- The new state after refining `R` with the transposed split. -/
noncomputable def NSt (sp : B × Fin 2 ≃ Rr ⊕ Uu) (E : Submodule F (Blk S B → F)) :
    Submodule F (Blk (S ⊕ (Uu × (P × Fin 2))) (Rr × Fin 2) → F) :=
  relabel (SM.rt S sp) (Qt E)

lemma card_Qt_type : Fintype.card (Dbl S (B × Fin 2)) = Fintype.card S + 16 * Fintype.card B := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; ring

theorem selfDual_Qt {E : Submodule F (Blk S B → F)} (hE : SelfDualG E) : SelfDualG (Qt E) := by
  apply selfDual_of_iso_card
  · intro v hv w hw
    have h := iso_D (iso_r₁ (iso_of_selfDual hE)) v hv w hw
    rwa [neg_neg, dotDbl_one] at h
  · rw [Qt, card_D, E1t, card_relabel, card_D]
    have hE2 := card_sq_of_selfDual hE
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hE2 ⊢
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9, mul_pow, mul_pow, hE2]
    simp only [← pow_mul, ← pow_add]
    congr 1
    ring

theorem indexG_Qt (E : Submodule F (Blk S B → F)) : indexG (Qt E) = R E := by
  rw [Qt, indexG_D, E1t, R_r₁]

theorem R_NSt (sp : B × Fin 2 ≃ Rr ⊕ Uu) (E : Submodule F (Blk S B → F)) : R (NSt sp E) = R E := by
  have hG : ∀ (x : B × Fin 2) (u : P → F),
      ∑ t ∈ Tfin, ((sp x).elim (fun _ => refdT) (fun _ => sgl)) (dbl u t) = lam (wtP u) := by
    intro x u
    rcases sp x with r | u'
    · exact localBt u
    · exact localA u
  have h1 : R (E1t E) = R E := R_r₁ E
  rw [← h1, ← sum_D (E1t E) (fun x => (sp x).elim (fun _ => refdT) (fun _ => sgl)) hG]
  unfold R NSt Qt
  rw [sum_relabel]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hL : Rw (fun i => w (SM.rt S sp i)) = ((∏ s, phi (w (.inl s))) *
      ∏ u : Uu, sgl (fun q => w (.inr (sp.symm (.inr u), q)))) *
      ∏ r : Rr, refdT (fun q => w (.inr (sp.symm (.inl r), q))) := by
    simp only [Rw, sgl, Fintype.prod_sum_type, Fintype.prod_prod_type]
    rfl
  rw [hL, Fintype.prod_equiv sp (fun x => ((sp x).elim (fun _ => refdT) (fun _ => sgl))
      (fun q => w (.inr (x, q)))) (fun y => (y.elim (fun _ => refdT) (fun _ => sgl))
      (fun q => w (.inr (sp.symm y, q)))) (fun x => by simp), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

theorem Inv_Qt {g : SM S B} {E : Submodule F (Blk S B → F)} (hE : g.toSP.Inv E) :
    (SM.step1 g).extD.Inv (Qt E) := by
  apply SM.Inv_D
  rw [← SM.pull_r₁]
  exact (SM.Inv_D hE).pull _

theorem Inv_NSt {sp : B × Fin 2 ≃ Rr ⊕ Uu} {g : SM S B} {πR πU} (hc : SM.Compat sp g πR πU)
    {E : Submodule F (Blk S B → F)} (hE : g.toSP.Inv E) :
    (SM.newSM sp g πR πU).toSP.Inv (NSt sp E) := by
  rw [← SM.pull_rt hc]
  exact (Inv_Qt hE).pull _

end CodeEngine

end GJF.Ex
