import GJF.Eval
import GJF.Twined

/-!
# Seed certificates for twined counts

Glue between the evaluator (`Eval.lean`) and the twined counts (`Twined.lean`): the twined count
`R^h` of a seed state, and `T_h` and the index of a seed code, as values of fast trees.
-/

open Finset

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Ex

local notation "F" => ZMod 3

namespace Eval

variable {n : ℕ}

/-- **`R^h` of a seed state** as a fast tree over the fixed codewords. -/
theorem Rh_seed {a b' : ℕ} {B B' : Type} [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    {rows : List (ℕ × ℕ)} (c : Blk (Fin a) B → Fin n)
    (hc : Function.Bijective c) (h : SM (Fin a) B) (hf : SP (Fin n))
    (hh : h.toSP = SP.pull (Equiv.ofBijective c hc) hf) (ψ : B' × Fin 3 ≃ B) (eB' : Fin b' ≃ B')
    {frows : List (ℕ × ℕ)} {J : Fin frows.length → Fin n} (hsysF : Sys (n := n) (rows := frows) J)
    (hmem : ∀ j, gen n frows j ∈ codeS n rows) (hfix : ∀ j, hf.act (gen n frows j) = gen n frows j)
    (L : Fin rows.length → List ((Fin n ⊕ Fin frows.length) × F))
    (hL : ∀ r r', ((L r).map fun cl => cl.2 * fixForm hf J cl.1 r').sum = if r = r' then 1 else 0)
    (hbits : ∀ r ∈ frows, r.1 < 2 ^ n ∧ r.2 < 2 ^ n) (sL : List ℕ) (bL : List (ℕ × ℕ × ℕ × ℕ))
    (hsL : sListOf c = sL) (hbL : (List.ofFn fun j => blockOf c (ψ (eB' j, 0))) = bL)
    (st : List FStep) (hst : rowsOf st = frows) (hv : fvalid sL bL st = true) :
    Rh h ψ (relabel (Equiv.ofBijective c hc) (codeS n rows)) = fastT (WtF sL bL) st 0 0 := by
  unfold Rh
  rw [hh, sum_relabel_fix, fixed_sum hf hsysF hmem hfix (comp_of_cert hf J L hL),
    ← sum_encS_fast hbits sL bL st hst hv]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← hsL, ← hbL, ← weight_eq_Wt c eB' (fun β' => ψ (β', 0))]
  rfl

lemma fG_eq_Wt (sL : List ℕ) (hsL : (List.ofFn fun i : Fin n => (i : ℕ)) = sL) (x : Fin n → F) :
    fG x = Wt sL [] (ext x) := by
  unfold fG Wt
  have he : ∀ j : Fin n, ext x j.val = x j := fun j => by simp [ext, j.isLt]
  rw [← hsL, List.map_ofFn, List.prod_ofFn]
  simp [he]

/-- **`T_h` of a seed code** as a fast tree over the fixed codewords. -/
theorem Th_seed {rows : List (ℕ × ℕ)} (hf : SP (Fin n))
    {frows : List (ℕ × ℕ)} {J : Fin frows.length → Fin n} (hsysF : Sys (n := n) (rows := frows) J)
    (hmem : ∀ j, gen n frows j ∈ codeS n rows) (hfix : ∀ j, hf.act (gen n frows j) = gen n frows j)
    (L : Fin rows.length → List ((Fin n ⊕ Fin frows.length) × F))
    (hL : ∀ r r', ((L r).map fun cl => cl.2 * fixForm hf J cl.1 r').sum = if r = r' then 1 else 0)
    (hbits : ∀ r ∈ frows, r.1 < 2 ^ n ∧ r.2 < 2 ^ n) (sL : List ℕ)
    (hsL : (List.ofFn fun i : Fin n => (i : ℕ)) = sL)
    (st : List FStep) (hst : rowsOf st = frows) (hv : fvalid sL [] st = true) :
    Th hf (codeS n rows) = fastT (WtF sL []) st 0 0 := by
  unfold Th
  rw [fixed_sum hf hsysF hmem hfix (comp_of_cert hf J L hL), ← sum_encS_fast hbits sL [] st hst hv]
  exact Finset.sum_congr rfl fun β _ => fG_eq_Wt sL hsL _

/-- **The index of a seed code** as a fast tree. -/
theorem indexG_seed {rows : List (ℕ × ℕ)} {info : Fin rows.length → Fin n} (hsys : Sys info)
    (hbits : ∀ r ∈ rows, r.1 < 2 ^ n ∧ r.2 < 2 ^ n) (sL : List ℕ)
    (hsL : (List.ofFn fun i : Fin n => (i : ℕ)) = sL)
    (st : List FStep) (hst : rowsOf st = rows) (hv : fvalid sL [] st = true) :
    indexG (codeS n rows) = fastT (WtF sL []) st 0 0 := by
  unfold indexG
  rw [CSG_codeS, Finset.sum_image (fun a _ b _ h => encS_inj hsys h),
    ← sum_encS_fast hbits sL [] st hst hv]
  exact Finset.sum_congr rfl fun β _ => fG_eq_Wt sL hsL _

/-- A seed generator in `SM` form agrees with the signed permutation `f` of the coordinates. -/
lemma toSP_of_c {a : ℕ} {B : Type} [Fintype B] [DecidableEq B] {c : Blk (Fin a) B → Fin n}
    (hc : Function.Bijective c) {g : SM (Fin a) B} {f : SP (Fin n)}
    (h : ∀ i, c (g.toSP.perm i) = f.perm (c i) ∧ g.toSP.sgn i = f.sgn (c i)) :
    g.toSP = SP.pull (Equiv.ofBijective c hc) f := by
  symm
  apply SP.pull_eq
  · intro i
    simp only [Equiv.ofBijective_apply]
    exact ((h i).1).symm
  · intro i
    exact ((h i).2).symm

end Eval

namespace SM

variable {S B Rr Uu : Type} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
  [Fintype Rr] [DecidableEq Rr] [Fintype Uu] [DecidableEq Uu]

lemma Compat.pow {sp : B × Fin 2 ≃ Rr ⊕ Uu} {g : SM S B} {πR πU} (hc : Compat sp g πR πU)
    (m : ℕ) : Compat sp (g ^ m) (πR ^ m) (πU ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pow_zero]; exact Compat.one sp
  | succ m ih => rw [pow_succ, pow_succ, pow_succ]; exact ih.mul hc

lemma newSM_pow {sp : B × Fin 2 ≃ Rr ⊕ Uu} {g : SM S B} {πR πU} (hc : Compat sp g πR πU)
    (m : ℕ) : newSM sp (g ^ m) (πR ^ m) (πU ^ m) = newSM sp g πR πU ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pow_zero, pow_zero, newSM_one]
  | succ m ih => rw [pow_succ, pow_succ, pow_succ, pow_succ, newSM_mul hc, ih]

end SM

end GJF.Ex
