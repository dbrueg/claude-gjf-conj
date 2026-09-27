import GJF.SPerm

/-!
# The local maps on a block

A block has positions `P = Fin 2 × Fin 2`, paired by the first component. Every local map that
occurs in the chains of the Main Question lies in one group `LM` of order 8 (a regular `Q₈` inside
the automorphism group of the tetracode `Tfin`), notes/blueprint/chains-and-seeds.md Lemma 2.7:

* `A r` keeps both pairs and rotates them by `J₊^r` and `J₊^(-r)`;
* `B r` swaps the pairs, by `J₊^r` (pair 0 → 1) and `-J₊^(-r)` (pair 1 → 0),

where `J₊ : e₀ ↦ e₁, e₁ ↦ -e₀` is the rotation of a pair. Everything here is a finite check.

* `toSP_mul`: `lsp` is a homomorphism; `tet`: every element preserves the tetracode.
* `stepK`, `S`: the local map of a step-one block (after the first doubling).
* `A (stepK μ a)`: the local map of a refined block (transposed split, order `x, y, y**, x**`).
* `localBt`: Lemma B for the transposed refinement split.
-/

open Finset

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Ex

local notation "F" => ZMod 3

/-! ### Rotations of a pair -/

/-- The permutation part of `J₊^k` on a pair. -/
def rotPerm (k : ZMod 4) : Equiv.Perm (Fin 2) := if k.val % 2 = 0 then 1 else Equiv.swap 0 1

/-- The signs of `J₊^k` (`J₊ : e₀ ↦ e₁, e₁ ↦ -e₀`), indexed by the source label. -/
def rotSgn (k : ZMod 4) (b : Fin 2) : F :=
  if k = 0 then 1 else if k = 2 then 2 else if k = 1 then (if b = 0 then 1 else 2)
  else (if b = 0 then 2 else 1)

lemma rotSgn_sq : ∀ k b, rotSgn k b * rotSgn k b = 1 := by decide

/-- `J₊^k` as a signed permutation of a pair. -/
def rot (k : ZMod 4) : SP (Fin 2) := ⟨rotPerm k, rotSgn k, rotSgn_sq k⟩

/-! ### The group `LM` -/

/-- `(r, false) = A r`, `(r, true) = B r`. -/
abbrev LM := ZMod 4 × Bool

/-- The pair permutation of a local map. -/
def pairP (f : Bool) : Equiv.Perm (Fin 2) := if f then Equiv.swap 0 1 else 1

/-- The rotation applied to pair `a`. -/
def kk (r : ZMod 4) (f : Bool) (a : Fin 2) : ZMod 4 :=
  if a = 0 then r else if f then 2 - r else -r

/-- The signed permutation of the four positions. -/
def lsp (m : LM) : SP P := SP.blk (pairP m.2) (fun a => rot (kk m.1 m.2 a))

/-- The group law (checked against `lsp` in `toSP_mul`). -/
def lmul : LM → LM → LM
  | (r, false), (s, false) => (r + s, false)
  | (r, false), (s, true) => (s - r, true)
  | (r, true), (s, false) => (r + s, true)
  | (r, true), (s, true) => (2 - r + s, false)

instance : Mul LM := ⟨lmul⟩

/-- The identity `A 0` and the negation `A 2`. -/
def lone : LM := (0, false)
def lneg : LM := (2, false)

set_option maxRecDepth 100000 in
lemma toSP_mul : ∀ m n : LM, lsp (lmul m n) = lsp m * lsp n := by decide

set_option maxRecDepth 100000 in
lemma toSP_lone : lsp lone = 1 := by decide

set_option maxRecDepth 100000 in
lemma toSP_lneg : lsp lneg = -1 := by decide

lemma lmul_assoc : ∀ a b c : LM, lmul (lmul a b) c = lmul a (lmul b c) := by decide
lemma lone_lmul : ∀ a : LM, lmul lone a = a := by decide
lemma lmul_lone : ∀ a : LM, lmul a lone = a := by decide
lemma lneg_lmul : ∀ a : LM, lmul lneg a = lmul a lneg := by decide

set_option maxRecDepth 100000 in
/-- Every local map preserves the tetracode. -/
theorem tet : ∀ (m : LM) (t : P → F), inT t → inT ((lsp m).act t) := by decide

lemma toSP_perm_fst (m : LM) (a b : Fin 2) : ((lsp m).perm (a, b)).1 = pairP m.2 a := rfl

lemma toSP_perm_snd (m : LM) (a b : Fin 2) :
    ((lsp m).perm (a, b)).2 = rotPerm (kk m.1 m.2 a) b := rfl

lemma toSP_sgn (m : LM) (a b : Fin 2) : (lsp m).sgn (a, b) = rotSgn (kk m.1 m.2 a) b := rfl

/-! ### Step-one blocks -/

/-- The rotation of pair `a` of `m`. -/
def stepK (m : LM) (a : Fin 2) : ZMod 4 := kk m.1 m.2 a

/-- The local map of a step-one block whose pair map is `J₊^k`: `(b, s) ↦ (J₊^k b, s)`. -/
def S (k : ZMod 4) : LM :=
  if k = 0 then (0, false) else if k = 1 then (0, true) else if k = 2 then (2, false) else (2, true)

set_option maxRecDepth 100000 in
lemma S_perm : ∀ (k : ZMod 4) (b s : Fin 2), (lsp (S k)).perm (b, s) = (rotPerm k b, s) := by
  decide

set_option maxRecDepth 100000 in
lemma S_sgn : ∀ (k : ZMod 4) (b s : Fin 2), (lsp (S k)).sgn (b, s) = rotSgn k b := by decide

lemma S_add : ∀ k l : ZMod 4, S (k + l) = lmul (S k) (S l) := by decide

lemma S_zero : S 0 = lone := by decide

lemma S_two : S 2 = lneg := by decide

lemma stepK_mul : ∀ (m n : LM) (a : Fin 2),
    stepK (lmul m n) a = stepK m (pairP n.2 a) + stepK n a := by decide

lemma pairP_mul : ∀ (m n : LM) (a : Fin 2), pairP (lmul m n).2 a = pairP m.2 (pairP n.2 a) := by
  decide

/-! ### Refined blocks (transposed split) -/

/-- The label `b ∈ Fin 2` of the step-one pair behind position `(u, c)` of a refined block, in the
order `x, y, y**, x**`: `c` on the first pair, `1 - c` on the second. -/
def ord (u c : Fin 2) : Fin 2 := if u = 0 then c else 1 - c

lemma ord_ord : ∀ u c : Fin 2, ord u (ord u c) = c := by decide

/-- The local map of a refined block over a step-one pair map `J₊^k`. -/
def A (k : ZMod 4) : LM := (k, false)

lemma A_add : ∀ k l : ZMod 4, A (k + l) = lmul (A k) (A l) := by decide

lemma A_zero : A 0 = lone := rfl

lemma A_two : A 2 = lneg := rfl

set_option maxRecDepth 100000 in
lemma A_perm : ∀ (k : ZMod 4) (u c : Fin 2),
    (lsp (A k)).perm (u, c) = (u, ord u (rotPerm k (ord u c))) := by decide

set_option maxRecDepth 100000 in
lemma A_sgn : ∀ (k : ZMod 4) (u c : Fin 2), (lsp (A k)).sgn (u, c) = rotSgn k (ord u c) := by
  decide

/-- The transposed refinement of a doubled step-one block `v` (positions `((b, s), u)`): the two
new blocks are `{((b, s), u)}_{b,u}` for `s = 0, 1`, with position `(u, c)` at `b = ord u c`. -/
def refdT (v : P × Fin 2 → F) : ℤ :=
  ∏ s : Fin 2, lam (#(univ.filter fun q : Fin 2 × Fin 2 => v ((ord q.1 q.2, s), q.1) ≠ 0))

set_option maxRecDepth 100000 in
/-- **Lemma B** for the transposed split, checked by the kernel for all `u`. -/
theorem localBt : ∀ u : P → F, ∑ t ∈ Tfin, refdT (dbl u t) = lam (wtP u) := by decide

end GJF.Ex
