import GJF.Chain

/-!
# The J-chain (Main Question, `gcd(k, 24) = 4`)

`J ∈ Aut(Golay)` with `J² = -1` (a signed fixed-point-free involution of the coordinates). The
block `{0, 1, 2, 3}`, with pairs `(0, 1)` and `(3, 2)`, is `J`-stable and `J` acts on it by the
local map `A 3`. Equivariant partial quadrupling then gives, for every even `k ≥ 2`, a self-dual
code of length `12k` with index `24` and an automorphism `J` with `J² = -1`.
-/

open Finset

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Ex

local notation "F" => ZMod 3

namespace JChain

/-- The permutation of `J` on the Golay coordinates: `(0 1)(2 3)…(10 11)`. -/
def jf : Fin 12 → Fin 12 := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10]

lemma jf_invol : ∀ i, jf (jf i) = i := by decide

/-- `J` on `𝔽₃^12`: `J e_i = s_i e_{jf i}`. -/
def Jfin : SP (Fin 12) :=
  ⟨⟨jf, jf, jf_invol, jf_invol⟩, ![2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1], by decide⟩

lemma act_enc (g : SP (Fin 12)) (a : Fin 6 → F) :
    g.act (enc a) = ∑ r, a r • g.act (golayRow r) := by
  have h : enc a = ∑ r, a r • golayRow r := by
    funext i; simp [enc, Finset.sum_apply]
  rw [h]
  induction (Finset.univ : Finset (Fin 6)) using Finset.induction_on with
  | empty => simp [SP.act_zero]
  | insert r s hr ih => rw [Finset.sum_insert hr, Finset.sum_insert hr, SP.act_add, SP.act_smul, ih]

set_option maxRecDepth 100000 in
/-- `J` maps every generator to the codeword with the same information part. -/
lemma Jfin_rows : ∀ r : Fin 6,
    Jfin.act (golayRow r) = enc (fun r' => Jfin.act (golayRow r) (Fin.castLE (by norm_num) r')) := by
  decide

lemma Jfin_inv : Jfin.Inv golay := by
  rintro _ ⟨a, rfl⟩
  rw [act_enc]
  refine golay.sum_mem fun r _ => golay.smul_mem _ ?_
  rw [Jfin_rows r]
  exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
lemma Jfin_sq : Jfin * Jfin = -1 := by decide

/-- The block `{0, 1, 2, 3}` with pairs `(0, 1)`, `(3, 2)`, and singletons `4, …, 11`. -/
def cJ : Blk (Fin 8) (Fin 1) → Fin 12 :=
  Sum.elim ![4, 5, 6, 7, 8, 9, 10, 11] (fun q => ![![0, 1], ![3, 2]] q.2.1 q.2.2)

lemma cJ_bij : Function.Bijective cJ := by decide

noncomputable def eJ : Blk (Fin 8) (Fin 1) ≃ Fin 12 := Equiv.ofBijective cJ cJ_bij

/-- The seed state. -/
noncomputable def E0 : Submodule F (Blk (Fin 8) (Fin 1) → F) := relabel eJ golay

set_option maxRecDepth 100000 in
theorem R_E0 : R E0 = 24 := by
  unfold R E0
  rw [sum_relabel, CSG_golay, Finset.sum_image (fun a _ b _ h => enc_inj h)]
  show ∑ a, Rw (fun i => enc a (cJ i)) = 24
  decide

/-- `J` on the singletons `4, …, 11`. -/
def Js : SP (Fin 8) :=
  ⟨⟨![1, 0, 3, 2, 5, 4, 7, 6], ![1, 0, 3, 2, 5, 4, 7, 6], by decide, by decide⟩,
    ![1, 2, 2, 1, 1, 2, 2, 1], by decide⟩

/-- The seed group data: `J` acts on the block by `A 3`. -/
def Jg : SM (Fin 8) (Fin 1) := ⟨Js, 1, fun _ => (3, false)⟩

set_option maxRecDepth 100000 in
lemma Jg_toSP_c : ∀ i, cJ (Jg.toSP.perm i) = Jfin.perm (cJ i) ∧ Jg.toSP.sgn i = Jfin.sgn (cJ i) := by
  decide

lemma Jg_toSP : Jg.toSP = SP.pull eJ Jfin := by
  symm
  apply SP.pull_eq
  · intro i
    simp only [eJ, Equiv.ofBijective_apply]
    exact ((Jg_toSP_c i).1).symm
  · intro i
    exact ((Jg_toSP_c i).2).symm

lemma Jg_inv : Jg.toSP.Inv E0 := by rw [Jg_toSP]; exact Jfin_inv.pull _

set_option maxRecDepth 100000 in
lemma Jg_sq : Jg * Jg = -1 := by decide

/-- Stage 0 refines the step-one block `(0, 0)`. -/
def sp0 : Fin 1 × Fin 2 ≃ Fin 1 ⊕ Fin 1 where
  toFun x := if x.2 = 0 then .inl 0 else .inr 0
  invFun y := y.elim (fun _ => (0, 0)) (fun _ => (0, 1))
  left_inv := by decide
  right_inv := by decide

lemma Jg_compat : SM.Compat sp0 Jg 1 1 := by unfold SM.Compat; decide

/-- The relation `J² = -1` on a uniform state. -/
def QJ {S : Type} [Fintype S] [DecidableEq S] (_ : Submodule F (Blk S (Fin 1 × Fin 2) → F))
    (gens : Unit → SM S (Fin 1 × Fin 2)) : Prop := gens () * gens () = -1

/-- The relation `J² = -1` on a code. -/
def QJ' {X : Type} [Fintype X] [DecidableEq X] (_ : Submodule F (X → F)) (gens : Unit → SP X) :
    Prop := gens () * gens () = -1

lemma sq_extD {S B : Type} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    {g : SM S B} (h : g * g = -1) : (SM.step1 g).extD * (SM.step1 g).extD = -1 := by
  rw [← SM.extD_mul, ← SM.step1_mul, h, SM.step1_neg, SM.step1_one, SM.extD_neg, SM.extD_one]

theorem j_state : GCode Unit QJ' 24 ∧ UState (Fin 1) Unit (fun _ => 1) QJ 24 := by
  have h := stage0 (Q := QJ) (Q' := QJ') E0 (selfDual_relabel _ selfDual_golay) R_E0 (fun _ => Jg)
    (fun _ => Jg_inv) sp0 (fun _ => 1) (fun _ => 1) (fun _ => Jg_compat) ?_ ?_
  · simpa using h
  · show SM.newSM sp0 Jg 1 1 * SM.newSM sp0 Jg 1 1 = -1
    rw [← SM.newSM_mul Jg_compat, Jg_sq, SM.newSM_neg, mul_one, SM.newSM_one]
  · exact sq_extD Jg_sq

theorem j_codes (j : ℕ) : GCode Unit QJ' (24 * (j + 1)) := by
  rcases j with _ | j
  · simpa using j_state.1
  · have h := ustate_chain (Q := QJ) (Q' := QJ') ?_ ?_ j_state.2 j
    · simpa [show 24 + 24 * (j + 1) = 24 * (j + 1 + 1) by ring] using h
    · intro S _ _ E gens _ hu hq
      show nxt (gens ()) 1 * nxt (gens ()) 1 = -1
      rw [← nxt_mul (hu ()), hq, one_mul, nxt_negOne]
    · intro S _ _ E gens _ _ hq
      exact sq_extD hq

/-- **The J-chain.** For every even `k ≥ 2` there is a self-dual ternary code of length `12k` with
index `24` and a signed permutation `J ∈ Aut(C)` with `J² = -1`. -/
lemma QJ'_pull {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (e : Y ≃ X)
    (C : Submodule F (X → F)) (gens : Unit → SP X) (hq : QJ' C gens) :
    QJ' (relabel e C) (fun i => SP.pull e (gens i)) := by
  show SP.pull e (gens ()) * SP.pull e (gens ()) = -1
  rw [← SP.pull_mul, hq, SP.pull_neg, SP.pull_one]

theorem exists_J (k : ℕ) (hk : 2 ≤ k) (heven : Even k) :
    ∃ (C : Submodule F (Fin (12 * k) → F)) (J : SP (Fin (12 * k))),
      IsSelfDual C ∧ gjfIndex C = 24 ∧ J.Inv C ∧ J * J = -1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * (j + 1) := by
    obtain ⟨m, hm⟩ := heven; exact ⟨m - 1, by omega⟩
  obtain ⟨C, gens, hC, hI, hinv, hq⟩ := GCode.toFin (Q' := QJ') QJ'_pull (j_codes j)
  rw [show 12 * (2 * (j + 1)) = 24 * (j + 1) by ring]
  exact ⟨C, gens (), hC, hI, hinv (), hq⟩

end JChain

end GJF.Ex
