import GJF.Chain
import GJF.Eval

/-!
# The Q₈-chain (Main Question, `gcd(k, 24) = 8`)

The seed is `ternary60/codes/q8chain_len24.txt` (length 24), with `J, K` acting on each group of
four coordinates as `J = (0 1)(2 3)` with signs `(+,-,+,-)` and `K = (0 2)(1 3)` with signs
`(+,-,-,+)` (so `J² = K² = -1`, `KJ = -JK`). The blocks `(8, 9 | 11, 10)` and `(12, 13 | 15, 14)`
are `Q₈`-stable; `J` acts on each by `A 1` and `K` by `B 1` (`K` swaps the pairs). The data are
printed by `ternary60/theory/lean_seed_data.py q8`.

* `R_EQ`: `R_σ(E) = 24`, by the verified evaluator over `2^12` candidates.
* `exists_Q8`: for every `k ≡ 0 mod 4`, `k ≥ 4`, a self-dual code of length `12k` with index 24
  and `J, K ∈ Aut(C)` with the `Q₈` relations.
-/

open Finset

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Ex

local notation "F" => ZMod 3

namespace Q8Chain

open Eval

/-- The generator matrix, row-reduced on the information set `infoQ` (bitmask pairs). -/
def rowsQ : List (ℕ × ℕ) := [(2106369, 4247808), (18434, 9482752), (1052676, 8447232),
  (6320136, 35328), (9478672, 4218112), (2098208, 12647168), (7352640, 52736), (10512256, 1087488),
  (8470528, 5257728), (169216, 14688256), (3442688, 4215296), (2621696, 9495552)]

/-- The seed code. -/
def EQ : Submodule F (Fin 24 → F) := codeS 24 rowsQ

def infoQ : Fin rowsQ.length → Fin 24 := ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19]

set_option maxRecDepth 100000 in
lemma sysQ : Sys infoQ := by unfold Sys; decide

set_option maxRecDepth 100000 in
lemma orthQ : ∀ r r', ∑ i, gen 24 rowsQ r i * gen 24 rowsQ r' i = 0 := by decide

theorem selfDual_EQ : SelfDualG EQ := selfDual_codeS sysQ orthQ rfl

/-- The blocks `(8, 9 | 11, 10)`, `(12, 13 | 15, 14)` and the 16 singletons. -/
def cQ : Blk (Fin 16) (Fin 2) → Fin 24 :=
  Sum.elim ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23]
    (fun q => ![![![8, 9], ![11, 10]], ![![12, 13], ![15, 14]]] q.1 q.2.1 q.2.2)

lemma cQ_bij : Function.Bijective cQ := by decide

noncomputable def eQ : Blk (Fin 16) (Fin 2) ≃ Fin 24 := Equiv.ofBijective cQ cQ_bij

/-- The seed state. -/
noncomputable def E0 : Submodule F (Blk (Fin 16) (Fin 2) → F) := relabel eQ EQ

def sLQ : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23]

def bLQ : List (ℕ × ℕ × ℕ × ℕ) := [(8, 9, 11, 10), (12, 13, 15, 14)]

def treeQ : List FStep := [.row 2106369 4247808, .chkS 0, .row 18434 9482752, .chkS 1,
  .row 1052676 8447232, .chkS 2, .row 6320136 35328, .chkS 3, .row 9478672 4218112, .chkS 4,
  .row 2098208 12647168, .chkS 5, .row 7352640 52736, .chkS 6, .row 10512256 1087488, .chkS 7,
  .row 8470528 5257728, .chkS 16, .row 169216 14688256, .chkS 17, .row 3442688 4215296, .chkS 18,
  .row 2621696 9495552, .chkS 19]

theorem fast_Q : fastT (WtF sLQ bLQ) treeQ 0 0 = 24 := by decide +kernel

theorem R_E0 : R E0 = 24 := by
  rw [E0, eQ, EQ, R_seed 24 rowsQ cQ cQ_bij (Equiv.refl _) sysQ (by decide) sLQ bLQ (by decide) (by decide) treeQ
    rfl (by decide)]
  exact fast_Q

/-! ### The group -/

def jp : Fin 24 → Fin 24 := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18,
  21, 20, 23, 22]
def kp : Fin 24 → Fin 24 := ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17,
  22, 23, 20, 21]

/-- `J` on the 24 coordinates. -/
def Jf : SP (Fin 24) := ⟨⟨jp, jp, by decide, by decide⟩, ![1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2,
  1, 2, 1, 2, 1, 2, 1, 2, 1, 2], by decide⟩

/-- `K` on the 24 coordinates. -/
def Kf : SP (Fin 24) := ⟨⟨kp, kp, by decide, by decide⟩, ![1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2,
  2, 1, 1, 2, 2, 1, 1, 2, 2, 1], by decide⟩

set_option maxRecDepth 100000 in
theorem Jf_inv : Jf.Inv EQ := Inv_codeS (info := infoQ) Jf (by decide)

set_option maxRecDepth 100000 in
theorem Kf_inv : Kf.Inv EQ := Inv_codeS (info := infoQ) Kf (by decide)

def jsp : Fin 16 → Fin 16 := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]
def ksp : Fin 16 → Fin 16 := ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13]

/-- The seed group data: `J` acts on both blocks by `A 1`, `K` by `B 1`. -/
def Jg : SM (Fin 16) (Fin 2) :=
  ⟨⟨⟨jsp, jsp, by decide, by decide⟩, ![1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2], by decide⟩,
    1, fun _ => (1, false)⟩

def Kg : SM (Fin 16) (Fin 2) :=
  ⟨⟨⟨ksp, ksp, by decide, by decide⟩, ![1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1], by decide⟩,
    1, fun _ => (1, true)⟩

set_option maxRecDepth 100000 in
lemma Jg_c : ∀ i, cQ (Jg.toSP.perm i) = Jf.perm (cQ i) ∧ Jg.toSP.sgn i = Jf.sgn (cQ i) := by
  decide

set_option maxRecDepth 100000 in
lemma Kg_c : ∀ i, cQ (Kg.toSP.perm i) = Kf.perm (cQ i) ∧ Kg.toSP.sgn i = Kf.sgn (cQ i) := by
  decide

lemma toSP_of_c {g : SM (Fin 16) (Fin 2)} {f : SP (Fin 24)}
    (h : ∀ i, cQ (g.toSP.perm i) = f.perm (cQ i) ∧ g.toSP.sgn i = f.sgn (cQ i)) :
    g.toSP = SP.pull eQ f := by
  symm
  apply SP.pull_eq
  · intro i
    simp only [eQ, Equiv.ofBijective_apply]
    exact ((h i).1).symm
  · intro i
    exact ((h i).2).symm

lemma Jg_inv : Jg.toSP.Inv E0 := by rw [toSP_of_c Jg_c]; exact Jf_inv.pull _
lemma Kg_inv : Kg.toSP.Inv E0 := by rw [toSP_of_c Kg_c]; exact Kf_inv.pull _

set_option maxRecDepth 100000 in
lemma Jg_sq : Jg * Jg = -1 := by decide

set_option maxRecDepth 100000 in
lemma Kg_sq : Kg * Kg = -1 := by decide

set_option maxRecDepth 100000 in
lemma KJ : Kg * Jg = -(Jg * Kg) := by decide

/-! ### The chain -/

/-- Generators indexed by `Fin 2`: `0 ↦ J`, `1 ↦ K`. -/
def gensQ : Fin 2 → SM (Fin 16) (Fin 2) := ![Jg, Kg]

/-- The block permutations of the uniform states (`O = Fin 2`, the two step-one blocks of the
refined orbit): `J` fixes both, `K` swaps them. -/
def πQ : Fin 2 → Equiv.Perm (Fin 2) := ![1, Equiv.swap 0 1]

/-- Stage 0 refines the step-one blocks `(0, a)`; the step-one blocks `(1, a)` become singletons. -/
def sp0 : Fin 2 × Fin 2 ≃ Fin 2 ⊕ Fin 2 where
  toFun x := if x.1 = 0 then .inl x.2 else .inr x.2
  invFun y := y.elim (fun a => (0, a)) (fun a => (1, a))
  left_inv := by decide
  right_inv := by decide

lemma compat : ∀ i, SM.Compat sp0 (gensQ i) (πQ i) (πQ i) := by
  intro i; fin_cases i <;> (unfold SM.Compat; decide)

/-- The `Q₈` relations. -/
def Rel {M : Type} [Monoid M] [Neg M] (g : Fin 2 → M) : Prop :=
  g 0 * g 0 = -1 ∧ g 1 * g 1 = -1 ∧ g 1 * g 0 = -(g 0 * g 1)

def QS {S : Type} [Fintype S] [DecidableEq S] (_ : Submodule F (Blk S (Fin 2 × Fin 2) → F))
    (gens : Fin 2 → SM S (Fin 2 × Fin 2)) : Prop := Rel gens

def QC {X : Type} [Fintype X] [DecidableEq X] (_ : Submodule F (X → F)) (gens : Fin 2 → SP X) :
    Prop := Rel gens

/-- Relations are inherited by any map compatible with products, `1` and negation. -/
lemma Rel.map {M N : Type} [Monoid M] [Neg M] [Monoid N] [Neg N] {g : Fin 2 → M} (f : M → N)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hone : f 1 = 1) (hneg : ∀ a, f (-a) = -f a)
    (h : Rel g) : Rel (fun i => f (g i)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmul, h1, hneg, hone]
  · rw [← hmul, h2, hneg, hone]
  · rw [← hmul, h3, hneg, hmul]

lemma rel_extD {S B : Type} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    {g : Fin 2 → SM S B} (h : Rel g) : Rel (fun i => (SM.step1 (g i)).extD) :=
  Rel.map (fun x => (SM.step1 x).extD) (fun a b => by rw [SM.step1_mul, SM.extD_mul])
    (by rw [SM.step1_one, SM.extD_one]) (fun a => by rw [SM.step1_neg, SM.extD_neg]) h

lemma rel_nxt {S : Type} [Fintype S] [DecidableEq S] {g : Fin 2 → SM S (Fin 2 × Fin 2)}
    (hu : ∀ i, Unif (g i) (πQ i)) (h : Rel g) : Rel (fun i => nxt (g i) (πQ i)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : (πQ 0 : Equiv.Perm (Fin 2)) = 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · show nxt (g 0) (πQ 0) * nxt (g 0) (πQ 0) = -1
    rw [← nxt_mul (hu 0), h1, e1, one_mul, nxt_negOne]
  · show nxt (g 1) (πQ 1) * nxt (g 1) (πQ 1) = -1
    rw [← nxt_mul (hu 1), h2,
      show πQ 1 * πQ 1 = 1 from Equiv.swap_mul_self 0 1, nxt_negOne]
  · show nxt (g 1) (πQ 1) * nxt (g 0) (πQ 0) = -(nxt (g 0) (πQ 0) * nxt (g 1) (πQ 1))
    rw [← nxt_mul (hu 0), ← nxt_mul (hu 1), h3, nxt_neg, e1, one_mul, mul_one]

lemma compatJ : SM.Compat sp0 Jg 1 1 := compat 0
lemma compatK : SM.Compat sp0 Kg (Equiv.swap 0 1) (Equiv.swap 0 1) := compat 1

lemma relS : Rel gensQ := ⟨Jg_sq, Kg_sq, KJ⟩

theorem q_state : GCode (Fin 2) QC 48 ∧ UState (Fin 2) (Fin 2) πQ QS 48 := by
  have h := stage0 (Q := QS) (Q' := QC) E0 (selfDual_relabel _ selfDual_EQ) R_E0 gensQ
    (fun i => by fin_cases i; exacts [Jg_inv, Kg_inv]) sp0 πQ πQ compat ?_ ?_
  · simpa using h
  · show Rel fun i => SM.newSM sp0 (gensQ i) (πQ i) (πQ i)
    refine ⟨?_, ?_, ?_⟩
    · show SM.newSM sp0 Jg 1 1 * SM.newSM sp0 Jg 1 1 = -1
      rw [← SM.newSM_mul compatJ, Jg_sq, SM.newSM_neg, mul_one, SM.newSM_one]
    · show SM.newSM sp0 Kg (Equiv.swap 0 1) (Equiv.swap 0 1) *
        SM.newSM sp0 Kg (Equiv.swap 0 1) (Equiv.swap 0 1) = -1
      rw [← SM.newSM_mul compatK, Kg_sq, SM.newSM_neg, Equiv.swap_mul_self, SM.newSM_one]
    · show SM.newSM sp0 Kg (Equiv.swap 0 1) (Equiv.swap 0 1) * SM.newSM sp0 Jg 1 1 =
        -(SM.newSM sp0 Jg 1 1 * SM.newSM sp0 Kg (Equiv.swap 0 1) (Equiv.swap 0 1))
      rw [← SM.newSM_mul compatJ, ← SM.newSM_mul compatK, KJ, SM.newSM_neg, mul_one,
        one_mul]
  · exact rel_extD relS

theorem q_codes (j : ℕ) : GCode (Fin 2) QC (48 * (j + 1)) := by
  rcases j with _ | j
  · simpa using q_state.1
  · have h := ustate_chain (Q := QS) (Q' := QC) ?_ ?_ q_state.2 j
    · simpa [show 48 + 48 * (j + 1) = 48 * (j + 1 + 1) by ring] using h
    · intro S _ _ E gens _ hu hq
      exact rel_nxt hu hq
    · intro S _ _ E gens _ _ hq
      exact rel_extD hq

lemma QC_pull {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (e : Y ≃ X)
    (C : Submodule F (X → F)) (gens : Fin 2 → SP X) (hq : QC C gens) :
    QC (relabel e C) (fun i => SP.pull e (gens i)) :=
  Rel.map (SP.pull e) (SP.pull_mul e) (SP.pull_one e) (SP.pull_neg e) hq

/-- **The Q₈-chain.** For every `k ≡ 0 mod 4`, `k ≥ 4`, there is a self-dual ternary code of length
`12k` with index `24` and signed permutations `J, K ∈ Aut(C)` with `J² = K² = -1`, `KJ = -JK`. -/
theorem exists_Q8 (k : ℕ) (hk : 4 ≤ k) (h4 : 4 ∣ k) :
    ∃ (C : Submodule F (Fin (12 * k) → F)) (J K : SP (Fin (12 * k))),
      IsSelfDual C ∧ gjfIndex C = 24 ∧ J.Inv C ∧ K.Inv C ∧
        J * J = -1 ∧ K * K = -1 ∧ K * J = -(J * K) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 4 * (j + 1) := by
    obtain ⟨m, hm⟩ := h4; exact ⟨m - 1, by omega⟩
  obtain ⟨C, gens, hC, hI, hinv, h1, h2, h3⟩ := GCode.toFin (Q' := QC) QC_pull (q_codes j)
  rw [show 12 * (4 * (j + 1)) = 48 * (j + 1) by ring]
  exact ⟨C, gens 0, gens 1, hC, hI, hinv 0, hinv 1, h1, h2, h3⟩

end Q8Chain

end GJF.Ex
