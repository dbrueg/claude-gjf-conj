import GJF.Divisibility

/-!
# Sanity checks for `GJF.Divisibility`

The hypotheses of `GJF.index_dvd_24` are satisfiable at positive length: the tetracode
(length 4) is self-dual, checked by `decide`. At length 0 the theorem fails (see the examples at the
end of `GJF.Divisibility`), which is why it assumes `0 < n`.
-/

namespace GJF.Sanity

open GJF

/-- The tetracode, as the kernel of two dot products. -/
def t1 : Word 4 := ![1, 1, 1, 0]
def t2 : Word 4 := ![0, 1, 2, 1]

lemma dot_add_right' (x y z : Word 4) : dot x (y + z) = dot x y + dot x z := by
  rw [dot_comm, dot_add_left, dot_comm y, dot_comm z]

def tetra : Submodule (ZMod 3) (Word 4) where
  carrier := {x | dot x t1 = 0 ∧ dot x t2 = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, dot_add_left] at *
    exact ⟨by rw [ha.1, hb.1, add_zero], by rw [ha.2, hb.2, add_zero]⟩
  zero_mem' := by simp [dot]
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq] at *
    constructor <;> simp [dot, mul_assoc, ← Finset.mul_sum] at * <;> simp [*]

set_option maxRecDepth 100000 in
/-- The tetracode is self-dual. -/
theorem tetra_selfDual : IsSelfDual tetra := by
  intro x
  show (dot x t1 = 0 ∧ dot x t2 = 0) ↔ ∀ c, (dot c t1 = 0 ∧ dot c t2 = 0) → dot x c = 0
  revert x
  decide

end GJF.Sanity
