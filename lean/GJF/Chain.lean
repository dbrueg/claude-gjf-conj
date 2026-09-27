import GJF.Equivariant

/-!
# Uniform equivariant chains

From its second stage on, every chain of the Main Question has blocks `O × Fin 2` and generators
whose block permutation is `πO × id` with pair-keeping local maps. The refined step-one blocks are
`((o, 0), 0)` (`spO`), so the next state again has blocks `O × Fin 2`, and each step adds `24 |O|`
to the length.

* `Unif g πO`: `g` has this form; `nxt g πO`: the group data on the next state.
* `nxt_mul`, `nxt_one`, `nxt_neg`: relations between generators are inherited.
* `UState`: a uniform state with an arbitrary invariant `Q` of the generators; `ustate_step`,
  `ustate_chain`: the induction.
-/

open Finset

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Ex

local notation "F" => ZMod 3

/-- `(s, a) ≠ (0, 0)` as an element of `Fin 3`. -/
def code3 (s a : Fin 2) : Fin 3 := if s = 0 then 0 else if a = 0 then 1 else 2

/-- The inverse of `code3`. -/
def decode3 (c : Fin 3) : Fin 2 × Fin 2 := if c = 0 then (0, 1) else if c = 1 then (1, 0) else (1, 1)

/-- The standard refinement: refine the step-one blocks `((o, 0), 0)`. -/
def spO (O : Type*) : (O × Fin 2) × Fin 2 ≃ O ⊕ (O × Fin 3) where
  toFun x := if x.1.2 = 0 ∧ x.2 = 0 then .inl x.1.1 else .inr (x.1.1, code3 x.1.2 x.2)
  invFun y := y.elim (fun o => ((o, 0), 0)) (fun oc => ((oc.1, (decode3 oc.2).1), (decode3 oc.2).2))
  left_inv := by
    rintro ⟨⟨o, s⟩, a⟩
    fin_cases s <;> fin_cases a <;> rfl
  right_inv := by
    rintro (o | ⟨o, c⟩)
    · rfl
    · fin_cases c <;> rfl

variable {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- Uniform group data: block permutation `πO × id`, pair-keeping local maps. -/
def Unif (g : SM S (O × Fin 2)) (πO : Equiv.Perm O) : Prop :=
  g.π = Equiv.prodCongr πO 1 ∧ ∀ β, (g.μ β).2 = false

lemma lmul_snd_false : ∀ a b : LM, a.2 = false → b.2 = false → (lmul a b).2 = false := by decide

lemma Unif.mul {g h : SM S (O × Fin 2)} {πg πh} (hg : Unif g πg) (hh : Unif h πh) :
    Unif (g * h) (πg * πh) := by
  refine ⟨?_, fun β => lmul_snd_false _ _ (hg.2 _) (hh.2 _)⟩
  rw [SM.mul_π, hg.1, hh.1]; ext ⟨o, s⟩ <;> rfl

lemma Unif.one : Unif (1 : SM S (O × Fin 2)) 1 := ⟨by ext ⟨o, s⟩ <;> rfl, fun _ => rfl⟩

lemma Unif.neg {g : SM S (O × Fin 2)} {π} (hg : Unif g π) : Unif (-g) π :=
  ⟨hg.1, fun β => by simp only [SM.neg_μ, lmul_snd, hg.2]⟩

lemma Unif.compat {g : SM S (O × Fin 2)} {πO} (hg : Unif g πO) :
    SM.Compat (spO O) g πO (Equiv.prodCongr πO 1) := by
  rintro ⟨⟨o, s⟩, a⟩
  have h1 : (SM.step1 g).π ((o, s), a) = ((πO o, s), a) := by
    rw [SM.step1_π, hg.1, hg.2]; rfl
  rw [h1]
  fin_cases s <;> fin_cases a <;> rfl

/-- The group data on the next state. -/
def nxt (g : SM S (O × Fin 2)) (πO : Equiv.Perm O) :
    SM (S ⊕ ((O × Fin 3) × (P × Fin 2))) (O × Fin 2) :=
  SM.newSM (spO O) g πO (Equiv.prodCongr πO 1)

lemma nxt_unif (g : SM S (O × Fin 2)) (πO : Equiv.Perm O) : Unif (nxt g πO) πO :=
  ⟨rfl, fun _ => rfl⟩

lemma nxt_mul {g h : SM S (O × Fin 2)} {πg πh} (hh : Unif h πh) :
    nxt (g * h) (πg * πh) = nxt g πg * nxt h πh := by
  rw [nxt, show Equiv.prodCongr (πg * πh) (1 : Equiv.Perm (Fin 3)) =
    Equiv.prodCongr πg 1 * Equiv.prodCongr πh 1 by ext ⟨o, c⟩ <;> rfl]
  exact SM.newSM_mul hh.compat

lemma nxt_one : nxt (1 : SM S (O × Fin 2)) 1 = 1 := by
  rw [nxt, show Equiv.prodCongr (1 : Equiv.Perm O) (1 : Equiv.Perm (Fin 3)) = 1 by
    ext ⟨o, c⟩ <;> rfl]
  exact SM.newSM_one _

lemma nxt_neg (g : SM S (O × Fin 2)) (π : Equiv.Perm O) : nxt (-g) π = -nxt g π :=
  SM.newSM_neg g _ _

lemma nxt_negOne : nxt (-1 : SM S (O × Fin 2)) 1 = -1 := by rw [nxt_neg, nxt_one]

lemma card_nxt_S : Fintype.card (S ⊕ ((O × Fin 3) × (P × Fin 2))) =
    Fintype.card S + 24 * Fintype.card O := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; ring

/-- A uniform state of length `n` with `R = 24` and generators `gens i` (block permutations
`πO i`), satisfying an invariant `Q`. -/
def UState (O ι : Type) [Fintype O] [DecidableEq O] (πO : ι → Equiv.Perm O)
    (Q : ∀ {S : Type} [Fintype S] [DecidableEq S], Submodule F (Blk S (O × Fin 2) → F) →
      (ι → SM S (O × Fin 2)) → Prop) (n : ℕ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (E : Submodule F (Blk S (O × Fin 2) → F))
    (gens : ι → SM S (O × Fin 2)),
    SelfDualG E ∧ R E = 24 ∧ Fintype.card S + 8 * Fintype.card O = n ∧
      (∀ i, Unif (gens i) (πO i)) ∧ (∀ i, (gens i).toSP.Inv E) ∧ Q E gens

/-- A self-dual code of length `n`, index 24, with generators in `Aut(C)` satisfying `Q'`. -/
def GCode (ι : Type) (Q' : ∀ {X : Type} [Fintype X] [DecidableEq X], Submodule F (X → F) →
    (ι → SP X) → Prop) (n : ℕ) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (C : Submodule F (X → F)) (gens : ι → SP X),
    SelfDualG C ∧ indexG C = 24 ∧ Fintype.card X = n ∧ (∀ i, (gens i).Inv C) ∧ Q' C gens

/-- **One uniform step**: a code of length `n + 24|O|` and the next uniform state. -/
theorem ustate_step {ι : Type} {πO : ι → Equiv.Perm O}
    {Q : ∀ {S : Type} [Fintype S] [DecidableEq S], Submodule F (Blk S (O × Fin 2) → F) →
      (ι → SM S (O × Fin 2)) → Prop}
    {Q' : ∀ {X : Type} [Fintype X] [DecidableEq X], Submodule F (X → F) → (ι → SP X) → Prop}
    (hQ : ∀ {S : Type} [Fintype S] [DecidableEq S] (E : Submodule F (Blk S (O × Fin 2) → F))
      (gens : ι → SM S (O × Fin 2)), SelfDualG E → (∀ i, Unif (gens i) (πO i)) → Q E gens →
      Q (NSt (spO O) E) (fun i => nxt (gens i) (πO i)))
    (hQ' : ∀ {S : Type} [Fintype S] [DecidableEq S] (E : Submodule F (Blk S (O × Fin 2) → F))
      (gens : ι → SM S (O × Fin 2)), SelfDualG E → (∀ i, Unif (gens i) (πO i)) → Q E gens →
      Q' (Qt E) (fun i => (SM.step1 (gens i)).extD))
    {n : ℕ} (h : UState O ι πO Q n) :
    GCode ι Q' (n + 24 * Fintype.card O) ∧ UState O ι πO Q (n + 24 * Fintype.card O) := by
  obtain ⟨S, _, _, E, gens, hE, hR, hn, hu, hinv, hq⟩ := h
  refine ⟨⟨_, inferInstance, inferInstance, Qt E, fun i => (SM.step1 (gens i)).extD, selfDual_Qt hE,
      by rw [indexG_Qt, hR], ?_, fun i => Inv_Qt (hinv i), hQ' E gens hE hu hq⟩,
    ⟨_, inferInstance, inferInstance, NSt (spO O) E, fun i => nxt (gens i) (πO i),
      selfDual_relabel _ (selfDual_Qt hE), by rw [R_NSt, hR], ?_, fun i => nxt_unif _ _,
      fun i => Inv_NSt (hu i).compat (hinv i), hQ E gens hE hu hq⟩⟩
  · rw [card_Qt_type, Fintype.card_prod, Fintype.card_fin]; omega
  · rw [card_nxt_S]; omega

theorem ustate_chain {ι : Type} {πO : ι → Equiv.Perm O}
    {Q : ∀ {S : Type} [Fintype S] [DecidableEq S], Submodule F (Blk S (O × Fin 2) → F) →
      (ι → SM S (O × Fin 2)) → Prop}
    {Q' : ∀ {X : Type} [Fintype X] [DecidableEq X], Submodule F (X → F) → (ι → SP X) → Prop}
    (hQ : ∀ {S : Type} [Fintype S] [DecidableEq S] (E : Submodule F (Blk S (O × Fin 2) → F))
      (gens : ι → SM S (O × Fin 2)), SelfDualG E → (∀ i, Unif (gens i) (πO i)) → Q E gens →
      Q (NSt (spO O) E) (fun i => nxt (gens i) (πO i)))
    (hQ' : ∀ {S : Type} [Fintype S] [DecidableEq S] (E : Submodule F (Blk S (O × Fin 2) → F))
      (gens : ι → SM S (O × Fin 2)), SelfDualG E → (∀ i, Unif (gens i) (πO i)) → Q E gens →
      Q' (Qt E) (fun i => (SM.step1 (gens i)).extD))
    {n : ℕ} (h : UState O ι πO Q n) (j : ℕ) :
    GCode ι Q' (n + 24 * Fintype.card O * (j + 1)) := by
  induction j generalizing n with
  | zero => simpa using (ustate_step hQ hQ' h).1
  | succ j ih =>
    have := ih (ustate_step hQ hQ' h).2
    rwa [show n + 24 * Fintype.card O + 24 * Fintype.card O * (j + 1) =
      n + 24 * Fintype.card O * (j + 1 + 1) by ring] at this

end GJF.Ex

namespace GJF.Ex

local notation "F" => ZMod 3

/-- **The first step** from a seed state with an arbitrary block system `B`, refining the step-one
blocks `O` of `sp : B × Fin 2 ≃ O ⊕ U`: a code of length `|S| + 16|B|` and a uniform state. -/
theorem stage0 {S B O U ι : Type} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O] [Fintype U] [DecidableEq U]
    {Q : ∀ {S : Type} [Fintype S] [DecidableEq S], Submodule F (Blk S (O × Fin 2) → F) →
      (ι → SM S (O × Fin 2)) → Prop}
    {Q' : ∀ {X : Type} [Fintype X] [DecidableEq X], Submodule F (X → F) → (ι → SP X) → Prop}
    (E : Submodule F (Blk S B → F)) (hE : SelfDualG E) (hR : R E = 24) (gens : ι → SM S B)
    (hinv : ∀ i, (gens i).toSP.Inv E) (sp : B × Fin 2 ≃ O ⊕ U) (πO : ι → Equiv.Perm O)
    (πU : ι → Equiv.Perm U) (hc : ∀ i, SM.Compat sp (gens i) (πO i) (πU i))
    (hQ0 : Q (NSt sp E) (fun i => SM.newSM sp (gens i) (πO i) (πU i)))
    (hQ'0 : Q' (Qt E) (fun i => (SM.step1 (gens i)).extD)) :
    GCode ι Q' (Fintype.card S + 16 * Fintype.card B) ∧
      UState O ι πO Q (Fintype.card S + 16 * Fintype.card B) := by
  have hcard : Fintype.card O + Fintype.card U = 2 * Fintype.card B := by
    have := Fintype.card_congr sp
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum] at this; omega
  refine ⟨⟨_, inferInstance, inferInstance, Qt E, fun i => (SM.step1 (gens i)).extD,
      selfDual_Qt hE, by rw [indexG_Qt, hR], card_Qt_type, fun i => Inv_Qt (hinv i), hQ'0⟩,
    ⟨_, inferInstance, inferInstance, NSt sp E, fun i => SM.newSM sp (gens i) (πO i) (πU i),
      selfDual_relabel _ (selfDual_Qt hE), by rw [R_NSt, hR], ?_, fun i => ⟨rfl, fun _ => rfl⟩,
      fun i => Inv_NSt (hc i) (hinv i), hQ0⟩⟩
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

/-- Transport a `GCode` to coordinates `Fin n`. -/
theorem GCode.toFin {ι : Type}
    {Q' : ∀ {X : Type} [Fintype X] [DecidableEq X], Submodule F (X → F) → (ι → SP X) → Prop}
    (hQ' : ∀ {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (e : Y ≃ X)
      (C : Submodule F (X → F)) (gens : ι → SP X), Q' C gens →
      Q' (relabel e C) (fun i => SP.pull e (gens i)))
    {n : ℕ} (h : GCode ι Q' n) :
    ∃ (C : Submodule F (Fin n → F)) (gens : ι → SP (Fin n)), IsSelfDual C ∧ gjfIndex C = 24 ∧
      (∀ i, (gens i).Inv C) ∧ Q' C gens := by
  obtain ⟨X, _, _, C, gens, hC, hI, rfl, hinv, hq⟩ := h
  refine ⟨relabel (Fintype.equivFin X).symm C, fun i => SP.pull (Fintype.equivFin X).symm (gens i),
    selfDual_relabel _ hC, ?_, fun i => (hinv i).pull _, hQ' _ C gens hq⟩
  rw [gjfIndex_eq]
  exact (indexG_relabel _ C).trans hI

end GJF.Ex
