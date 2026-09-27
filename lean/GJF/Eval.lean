import GJF.SPerm

/-!
# A verified bit-sliced evaluator for seed sums

Seed facts such as `R_σ(E) = 24` for a code of dimension 12 to 18 are sums over `3^12` to
`3^18` codewords, too many for `decide` on `Fin n → ZMod 3`. This file gives a kernel-fast
evaluator and proves it sound.

* Words are pairs of bitmasks `(m₁, m₂)` (bit `i` of `m₁`: value 1, of `m₂`: value 2); `decN`
  decodes them. `addP` adds two words with bit operations (`decN_addP`).
* An evaluation tree (`FStep`) runs through the generator rows (three branches each) and prunes
  with checks at information coordinates (`chkS`: a singleton must be nonzero; `chkB`: a block must
  have weight 1 or 4). `fastT` evaluates it with kernel-accelerated `Nat` operations only.
* `fastT_eq_sum`: if the checks are admissible (`fvalid`, a `Bool` the kernel decides), the tree
  equals the full sum `Σ_a W(Σ_r a_r g_r)` of the weight `Wt` over all coefficient vectors
  (notes/blueprint/chains-and-seeds.md Lemma 2.5).
* `SeedCode`: the code spanned by bitmask rows, systematic on given coordinates; `R_seed`
  turns a block-weighted index `R` into a `fastT` value.
-/

open Finset

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Ex

local notation "F" => ZMod 3

namespace Eval

/-! ### Bitmask words -/

/-- Decode a bitmask pair. -/
def decN (m : ℕ × ℕ) : ℕ → F := fun i =>
  if m.1.testBit i then 1 else if m.2.testBit i then 2 else 0

/-- No bit is set in both masks. -/
def Valid (m : ℕ × ℕ) : Prop := Nat.land m.1 m.2 = 0

lemma Valid.bit {m : ℕ × ℕ} (h : Valid m) (i : ℕ) : ¬(m.1.testBit i = true ∧ m.2.testBit i = true) := by
  intro ⟨h1, h2⟩
  have := Nat.testBit_land m.1 m.2 i
  unfold Valid at h
  rw [show Nat.land m.1 m.2 = m.1 &&& m.2 from rfl] at h
  rw [h, Nat.zero_testBit, h1, h2] at this
  simp at this

lemma Valid.of_bit {m : ℕ × ℕ} (h : ∀ i, ¬(m.1.testBit i = true ∧ m.2.testBit i = true)) :
    Valid m := by
  unfold Valid
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show Nat.land m.1 m.2 = m.1 &&& m.2 from rfl, Nat.testBit_land, Nat.zero_testBit]
  have := h i
  revert this
  cases m.1.testBit i <;> cases m.2.testBit i <;> simp

/-- One output mask of the addition: `x₁ ∧ ¬y` or `y₁ ∧ ¬x` or `x₂ ∧ y₂`. -/
def r1f (x1 x2 y1 y2 : ℕ) : ℕ :=
  Nat.lor (Nat.lor (Nat.xor x1 (Nat.land x1 (Nat.lor y1 y2))) (Nat.xor y1 (Nat.land y1 (Nat.lor x1 x2))))
    (Nat.land x2 y2)

/-- Addition of words. -/
def addP (x y : ℕ × ℕ) : ℕ × ℕ := (r1f x.1 x.2 y.1 y.2, r1f x.2 x.1 y.2 y.1)

lemma testBit_r1f (x1 x2 y1 y2 i : ℕ) : (r1f x1 x2 y1 y2).testBit i =
    ((x1.testBit i && !(y1.testBit i || y2.testBit i)) ||
      (y1.testBit i && !(x1.testBit i || x2.testBit i)) || (x2.testBit i && y2.testBit i)) := by
  simp only [r1f, show ∀ a b : ℕ, Nat.lor a b = a ||| b from fun _ _ => rfl,
    show ∀ a b : ℕ, Nat.land a b = a &&& b from fun _ _ => rfl,
    show ∀ a b : ℕ, Nat.xor a b = a ^^^ b from fun _ _ => rfl,
    Nat.testBit_lor, Nat.testBit_land, Nat.testBit_xor]
  cases x1.testBit i <;> cases x2.testBit i <;> cases y1.testBit i <;> cases y2.testBit i <;> rfl

/-- The value of a bit pair. -/
def bval (b1 b2 : Bool) : F := if b1 then 1 else if b2 then 2 else 0

lemma add_bits : ∀ b1 b2 c1 c2 : Bool, ¬(b1 = true ∧ b2 = true) → ¬(c1 = true ∧ c2 = true) →
    bval ((b1 && !(c1 || c2)) || (c1 && !(b1 || b2)) || (b2 && c2))
        ((b2 && !(c2 || c1)) || (c2 && !(b2 || b1)) || (b1 && c1)) = bval b1 b2 + bval c1 c2 ∧
      ¬(((b1 && !(c1 || c2)) || (c1 && !(b1 || b2)) || (b2 && c2)) = true ∧
        ((b2 && !(c2 || c1)) || (c2 && !(b2 || b1)) || (b1 && c1)) = true) := by
  decide

lemma decN_apply (m : ℕ × ℕ) (i : ℕ) : decN m i = bval (m.1.testBit i) (m.2.testBit i) := rfl

lemma decN_addP {x y : ℕ × ℕ} (hx : Valid x) (hy : Valid y) :
    decN (addP x y) = decN x + decN y ∧ Valid (addP x y) := by
  have key := fun i => add_bits (x.1.testBit i) (x.2.testBit i) (y.1.testBit i) (y.2.testBit i)
    (hx.bit i) (hy.bit i)
  refine ⟨funext fun i => ?_, Valid.of_bit fun i => ?_⟩
  · rw [Pi.add_apply, decN_apply, decN_apply, decN_apply, addP, testBit_r1f, testBit_r1f]
    exact (key i).1
  · rw [addP, testBit_r1f, testBit_r1f]
    exact (key i).2

lemma decN_swap {x : ℕ × ℕ} (hx : Valid x) : decN (x.2, x.1) = -decN x := by
  funext i
  rw [Pi.neg_apply, decN_apply, decN_apply]
  have := hx.bit i
  revert this
  cases x.1.testBit i <;> cases x.2.testBit i <;> decide

lemma Valid.swap {x : ℕ × ℕ} (hx : Valid x) : Valid (x.2, x.1) :=
  Valid.of_bit fun i ⟨h1, h2⟩ => hx.bit i ⟨h2, h1⟩

lemma valid_zero : Valid (0, 0) := rfl

lemma decN_zero : decN (0, 0) = 0 := by
  funext i; simp [decN]

lemma decN_ne_zero_iff (m : ℕ × ℕ) (i : ℕ) : decN m i ≠ 0 ↔ (Nat.lor m.1 m.2).testBit i = true := by
  rw [decN_apply, show Nat.lor m.1 m.2 = m.1 ||| m.2 from rfl, Nat.testBit_lor]
  cases m.1.testBit i <;> cases m.2.testBit i <;> decide

/-! ### The weight -/

/-- The number of nonzero entries among four coordinates. -/
def cnt4 (y : ℕ → F) (b : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  (if y b.1 ≠ 0 then 1 else 0) + (if y b.2.1 ≠ 0 then 1 else 0) + (if y b.2.2.1 ≠ 0 then 1 else 0) +
    (if y b.2.2.2 ≠ 0 then 1 else 0)

/-- The block-weighted weight with singletons `sL` and blocks `bL`. -/
def Wt (sL : List ℕ) (bL : List (ℕ × ℕ × ℕ × ℕ)) (y : ℕ → F) : ℤ :=
  (sL.map fun i => phi (y i)).prod * (bL.map fun b => lam (cnt4 y b)).prod

lemma Wt_eq_zero_of_sgl {sL : List ℕ} {bL : List (ℕ × ℕ × ℕ × ℕ)} {i : ℕ} (hi : i ∈ sL)
    {y : ℕ → F} (hy : y i = 0) : Wt sL bL y = 0 := by
  unfold Wt
  rw [List.prod_eq_zero (List.mem_map.2 ⟨i, hi, by simp [hy, phi]⟩), zero_mul]

lemma Wt_eq_zero_of_blk {sL : List ℕ} {bL : List (ℕ × ℕ × ℕ × ℕ)} {b : ℕ × ℕ × ℕ × ℕ}
    (hb : b ∈ bL) {y : ℕ → F} (hy : lam (cnt4 y b) = 0) : Wt sL bL y = 0 := by
  unfold Wt
  rw [List.prod_eq_zero (List.mem_map.2 ⟨b, hb, hy⟩), mul_zero]

/-! ### Kernel-fast versions -/

/-- `testBit` with accelerated operations only. -/
def tb (m i : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

lemma tb_eq (m i : ℕ) : tb m i = m.testBit i := by
  unfold tb
  rw [show Nat.land (Nat.shiftRight m i) 1 = (m >>> i) &&& 1 from rfl, Nat.and_one_is_mod,
    Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (m >>> i) with h | h <;> rw [h] <;> rfl

/-- `∏ φ` over the coordinates `l`. -/
def phiF (m1 m2 : ℕ) (l : List ℕ) : ℤ :=
  List.rec (motive := fun _ => ℤ) 1
    (fun i _ ih => cond (tb m1 i) (Int.neg ih) (cond (tb m2 i) ih 0)) l

/-- The number of nonzero entries of a block (`o` = the support mask). -/
def cntF (o : ℕ) (b : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (cond (tb o b.1) 1 0) (cond (tb o b.2.1) 1 0))
      (cond (tb o b.2.2.1) 1 0)) (cond (tb o b.2.2.2) 1 0)

/-- `λ` of a count. -/
def lamC (c : ℕ) : ℤ := cond (Nat.beq c 4) 1 (cond (Nat.beq c 1) (-2) 0)

/-- `λ` of a block. -/
def lamF (o : ℕ) (b : ℕ × ℕ × ℕ × ℕ) : ℤ := lamC (cntF o b)

/-- `∏ λ` over the blocks `l`. -/
def lamsF (o : ℕ) (l : List (ℕ × ℕ × ℕ × ℕ)) : ℤ :=
  List.rec (motive := fun _ => ℤ) 1 (fun b _ ih => Int.mul (lamF o b) ih) l

/-- The fast weight. -/
def WtF (sL : List ℕ) (bL : List (ℕ × ℕ × ℕ × ℕ)) (m1 m2 : ℕ) : ℤ :=
  Int.mul (phiF m1 m2 sL) (lamsF (Nat.lor m1 m2) bL)

lemma phiF_eq (m : ℕ × ℕ) (l : List ℕ) : phiF m.1 m.2 l = (l.map fun i => phi (decN m i)).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    show cond (tb m.1 i) (Int.neg (phiF m.1 m.2 l)) (cond (tb m.2 i) (phiF m.1 m.2 l) 0) = _
    rw [List.map_cons, List.prod_cons, ← ih, tb_eq, tb_eq, decN_apply]
    cases m.1.testBit i <;> cases m.2.testBit i <;> simp [bval, phi] <;> rfl

lemma cond_one_zero (b : Bool) : cond b (1 : ℕ) 0 = if b = true then 1 else 0 := by cases b <;> rfl

lemma lam_cond (c : ℕ) : lamC c = lam c := by
  unfold lam lamC
  by_cases h4 : c = 4
  · subst h4; rfl
  · by_cases h1 : c = 1
    · subst h1; rfl
    · rw [if_neg h4, if_neg h1]
      have e4 : Nat.beq c 4 = false := by
        cases h : Nat.beq c 4
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) h4
      have e1 : Nat.beq c 1 = false := by
        cases h : Nat.beq c 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) h1
      rw [e4, e1]; rfl

lemma cntF_eq (m : ℕ × ℕ) (b : ℕ × ℕ × ℕ × ℕ) : cntF (Nat.lor m.1 m.2) b = cnt4 (decN m) b := by
  unfold cntF cnt4
  simp only [tb_eq, ← decN_ne_zero_iff, cond_one_zero,
    show ∀ a b : ℕ, Nat.add a b = a + b from fun _ _ => rfl]

lemma lamF_eq (m : ℕ × ℕ) (b : ℕ × ℕ × ℕ × ℕ) : lamF (Nat.lor m.1 m.2) b = lam (cnt4 (decN m) b) := by
  unfold lamF
  rw [lam_cond, cntF_eq]

lemma lamsF_eq (m : ℕ × ℕ) (l : List (ℕ × ℕ × ℕ × ℕ)) :
    lamsF (Nat.lor m.1 m.2) l = (l.map fun b => lam (cnt4 (decN m) b)).prod := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    show Int.mul (lamF _ b) (lamsF _ l) = _
    rw [List.map_cons, List.prod_cons, ← ih, lamF_eq]; rfl

lemma WtF_eq (sL : List ℕ) (bL : List (ℕ × ℕ × ℕ × ℕ)) (m : ℕ × ℕ) :
    WtF sL bL m.1 m.2 = Wt sL bL (decN m) := by
  unfold WtF Wt
  rw [← phiF_eq, ← lamsF_eq]; rfl

/-! ### Evaluation trees -/

/-- A step of an evaluation tree: a generator row (three branches), or a check that a singleton
is nonzero (`chkS`) or that a block has weight 1 or 4 (`chkB`). -/
inductive FStep
  | row (r1 r2 : ℕ)
  | chkS (i : ℕ)
  | chkB (b : ℕ × ℕ × ℕ × ℕ)

/-- The kernel-fast evaluation of a tree with leaf weight `w`. -/
noncomputable def fastT (w : ℕ → ℕ → ℤ) (st : List FStep) : ℕ → ℕ → ℤ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℤ) w
    (fun s _ ih a b => FStep.rec (motive := fun _ => ℤ)
      (fun r1 r2 => Int.add (Int.add (ih a b) (ih (r1f a b r1 r2) (r1f b a r2 r1)))
        (ih (r1f a b r2 r1) (r1f b a r1 r2)))
      (fun i => cond (tb (Nat.lor a b) i) (ih a b) 0)
      (fun bb => (fun c => cond (Nat.beq c 4) (ih a b) (cond (Nat.beq c 1) (ih a b) 0))
        (cntF (Nat.lor a b) bb)) s) st

/-- The rows of a tree. -/
def rowsOf : List FStep → List (ℕ × ℕ)
  | [] => []
  | .row r1 r2 :: st => (r1, r2) :: rowsOf st
  | .chkS _ :: st => rowsOf st
  | .chkB _ :: st => rowsOf st

/-- Admissibility of a tree: rows are valid words; a check refers to a singleton or block of the
weight, and all later rows vanish on its coordinates. -/
def fvalid (sL : List ℕ) (bL : List (ℕ × ℕ × ℕ × ℕ)) : List FStep → Bool
  | [] => true
  | .row r1 r2 :: st => Nat.beq (Nat.land r1 r2) 0 && fvalid sL bL st
  | .chkS i :: st => sL.elem i && (rowsOf st).all (fun r => !(Nat.lor r.1 r.2).testBit i) &&
      fvalid sL bL st
  | .chkB b :: st => bL.elem b && (rowsOf st).all (fun r => !((Nat.lor r.1 r.2).testBit b.1 ||
      (Nat.lor r.1 r.2).testBit b.2.1 || (Nat.lor r.1 r.2).testBit b.2.2.1 ||
      (Nat.lor r.1 r.2).testBit b.2.2.2)) && fvalid sL bL st

/-- The full sum over all coefficient vectors (reference semantics). -/
def fullS (W : (ℕ → F) → ℤ) : List (ℕ → F) → (ℕ → F) → ℤ
  | [], v => W v
  | r :: rs, v => fullS W rs v + fullS W rs (v + r) + fullS W rs (v - r)

lemma fullS_zero (W : (ℕ → F) → ℤ) (I : List ℕ) :
    ∀ (rows : List (ℕ → F)) (v : ℕ → F), (∀ r ∈ rows, ∀ i ∈ I, r i = 0) →
      (∀ y : ℕ → F, (∀ i ∈ I, y i = v i) → W y = 0) → fullS W rows v = 0 := by
  intro rows
  induction rows with
  | nil => intro v _ hW; exact hW v fun _ _ => rfl
  | cons r rs ih =>
    intro v hr hW
    have hr' : ∀ r' ∈ rs, ∀ i ∈ I, r' i = 0 := fun r' h => hr r' (List.mem_cons_of_mem _ h)
    have h0 : ∀ i ∈ I, r i = 0 := hr r List.mem_cons_self
    simp only [fullS]
    rw [ih v hr' hW, ih (v + r) hr' (fun y hy => hW y fun i hi => by
        rw [hy i hi, Pi.add_apply, h0 i hi, add_zero]),
      ih (v - r) hr' (fun y hy => hW y fun i hi => by rw [hy i hi, Pi.sub_apply, h0 i hi, sub_zero])]
    simp

lemma mem_rowsOf_valid {sL bL} : ∀ (st : List FStep), fvalid sL bL st = true →
    ∀ r ∈ rowsOf st, Valid r := by
  intro st
  induction st with
  | nil => intro _ r hr; simp [rowsOf] at hr
  | cons s st ih =>
    intro h r hr
    cases s with
    | row r1 r2 =>
      simp only [fvalid, Bool.and_eq_true] at h
      simp only [rowsOf, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact Nat.eq_of_beq_eq_true h.1
      · exact ih h.2 r hr
    | chkS i =>
      simp only [fvalid, Bool.and_eq_true] at h
      exact ih h.2 r hr
    | chkB b =>
      simp only [fvalid, Bool.and_eq_true] at h
      exact ih h.2 r hr

/-- **Soundness of the fast evaluator.** -/
theorem fastT_eq (sL : List ℕ) (bL : List (ℕ × ℕ × ℕ × ℕ)) :
    ∀ (st : List FStep) (m : ℕ × ℕ), fvalid sL bL st = true → Valid m →
      fastT (WtF sL bL) st m.1 m.2 = fullS (Wt sL bL) ((rowsOf st).map decN) (decN m) := by
  intro st
  induction st with
  | nil => intro m _ _; exact WtF_eq sL bL m
  | cons s st ih =>
    intro m h hm
    cases s with
    | row r1 r2 =>
      simp only [fvalid, Bool.and_eq_true] at h
      have hr : Valid (r1, r2) := Nat.eq_of_beq_eq_true h.1
      have e1 := decN_addP hm hr
      have e2 := decN_addP hm hr.swap
      show Int.add (Int.add (fastT _ st m.1 m.2) (fastT _ st (addP m (r1, r2)).1 (addP m (r1, r2)).2))
          (fastT _ st (addP m (r2, r1)).1 (addP m (r2, r1)).2) = _
      rw [ih m h.2 hm, ih _ h.2 e1.2, ih _ h.2 e2.2, e1.1, e2.1, decN_swap hr, ← sub_eq_add_neg]
      rfl
    | chkS i =>
      simp only [fvalid, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨⟨hi, hrows⟩, hst⟩ := h
      show cond (tb (Nat.lor m.1 m.2) i) (fastT _ st m.1 m.2) 0 = _
      rw [tb_eq]
      simp only [rowsOf]
      cases hb : (Nat.lor m.1 m.2).testBit i
      · symm
        apply fullS_zero _ [i]
        · intro r hr j hj
          simp only [List.mem_singleton] at hj
          subst hj
          obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
          by_contra hne
          have := (decN_ne_zero_iff r' j).1 hne
          have h2 := hrows r' hr'
          rw [this] at h2
          simp at h2
        · intro y hy
          have hy' := hy i (List.mem_singleton_self i)
          apply Wt_eq_zero_of_sgl (List.elem_iff.1 hi)
          rw [hy']
          by_contra hne
          have := (decN_ne_zero_iff m i).1 hne
          rw [hb] at this
          simp at this
      · exact ih m hst hm
    | chkB b =>
      simp only [fvalid, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨⟨hb, hrows⟩, hst⟩ := h
      show (fun c => cond (Nat.beq c 4) (fastT _ st m.1 m.2)
        (cond (Nat.beq c 1) (fastT _ st m.1 m.2) 0)) (cntF (Nat.lor m.1 m.2) b) = _
      simp only [rowsOf]
      rw [cntF_eq]
      by_cases hc : cnt4 (decN m) b = 4 ∨ cnt4 (decN m) b = 1
      · rcases hc with hc | hc <;> rw [hc] <;> exact ih m hst hm
      · push Not at hc
        have e4 : Nat.beq (cnt4 (decN m) b) 4 = false := by
          cases h' : Nat.beq (cnt4 (decN m) b) 4
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h') hc.1
        have e1 : Nat.beq (cnt4 (decN m) b) 1 = false := by
          cases h' : Nat.beq (cnt4 (decN m) b) 1
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h') hc.2
        simp only [e4, e1, Bool.cond_false]
        symm
        apply fullS_zero _ [b.1, b.2.1, b.2.2.1, b.2.2.2]
        · intro r hr j hj
          obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
          have h2 := hrows r' hr'
          simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true'] at h2
          by_contra hne
          have hne := (decN_ne_zero_iff r' j).1 hne
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl | rfl | rfl <;> simp_all
        · intro y hy
          apply Wt_eq_zero_of_blk (List.elem_iff.1 hb)
          have : cnt4 y b = cnt4 (decN m) b := by
            unfold cnt4
            rw [hy _ (by simp), hy _ (by simp), hy _ (by simp), hy _ (by simp)]
          rw [this]
          unfold lam
          simp [hc.1, hc.2]

/-! ### The full sum as a sum over coefficient vectors -/

lemma sum_F {M : Type*} [AddCommMonoid M] (f : F → M) : ∑ c, f c = f 0 + f 1 + f 2 := by
  rw [show (univ : Finset F) = {0, 1, 2} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

theorem fullS_eq_sum (W : (ℕ → F) → ℤ) :
    ∀ (k : ℕ) (g : Fin k → ℕ → F) (v : ℕ → F),
      fullS W (List.ofFn g) v = ∑ a : Fin k → F, W (v + ∑ i, a i • g i) := by
  intro k
  induction k with
  | zero => intro g v; simp [fullS]
  | succ k ih =>
    intro g v
    rw [List.ofFn_succ, fullS, ih, ih, ih]
    rw [← (Fin.consEquiv fun _ => F).sum_comp, Fintype.sum_prod_type, sum_F]
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_smul,
      one_smul, zero_add]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun a _ => by rw [add_assoc]
    · exact Finset.sum_congr rfl fun a _ => by
        rw [show (2 : F) • g 0 = -g 0 by
          funext j; simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
          generalize g 0 j = x; revert x; decide]
        rw [← add_assoc, ← sub_eq_add_neg]

/-! ### Seed codes given by bitmask rows -/

section Seed

variable (n : ℕ) (rows : List (ℕ × ℕ))

/-- The generator rows on `Fin n`. -/
def gen (r : Fin rows.length) : Fin n → F := fun j => decN rows[r] j

/-- Encoding. -/
def encS (a : Fin rows.length → F) : Fin n → F := fun j => ∑ r, a r * gen n rows r j

/-- The code spanned by the rows. -/
def codeS : Submodule F (Fin n → F) where
  carrier := Set.range (encS n rows)
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by funext i; simp [encS, add_mul, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, by funext i; simp [encS]⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    exact ⟨c • a, by funext i; simp [encS, Finset.mul_sum, mul_assoc]⟩

variable {n rows}

lemma mem_codeS {x : Fin n → F} : x ∈ codeS n rows ↔ ∃ a, encS n rows a = x := Iff.rfl

/-- The rows are systematic on the coordinates `info`. -/
def Sys (info : Fin rows.length → Fin n) : Prop := ∀ r j, gen n rows r (info j) = if r = j then 1 else 0

lemma encS_sys {info : Fin rows.length → Fin n} (h : Sys info) (a : Fin rows.length → F)
    (j : Fin rows.length) : encS n rows a (info j) = a j := by
  unfold encS
  unfold Sys at h
  simp [h]

lemma encS_inj {info : Fin rows.length → Fin n} (h : Sys info) : Function.Injective (encS n rows) :=
  fun a b hab => funext fun j => by rw [← encS_sys h a j, ← encS_sys h b j, hab]

lemma CSG_codeS : CSG (codeS n rows) = univ.image (encS n rows) := by
  ext x
  simp only [mem_CSG, mem_codeS, Finset.mem_image, Finset.mem_univ, true_and]

lemma card_codeS {info : Fin rows.length → Fin n} (h : Sys info) :
    #(CSG (codeS n rows)) = 3 ^ rows.length := by
  rw [CSG_codeS, Finset.card_image_of_injective _ (encS_inj h), Finset.card_univ, card_F_fun]
  simp

lemma dotG_encS (horth : ∀ r r', ∑ i, gen n rows r i * gen n rows r' i = 0)
    (a b : Fin rows.length → F) : dotG (encS n rows a) (encS n rows b) = 0 := by
  unfold dotG encS
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun r' _ => ?_
  calc ∑ i, a r * gen n rows r i * (b r' * gen n rows r' i)
      = a r * b r' * ∑ i, gen n rows r i * gen n rows r' i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [horth r r', mul_zero]

/-- Self-duality from orthogonal systematic rows with `n = 2k`. -/
theorem selfDual_codeS {info : Fin rows.length → Fin n} (h : Sys info)
    (horth : ∀ r r', ∑ i, gen n rows r i * gen n rows r' i = 0) (hn : n = 2 * rows.length) :
    SelfDualG (codeS n rows) := by
  apply selfDual_of_iso_card
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact dotG_encS horth a b
  · rw [card_codeS h, Fintype.card_fin, hn, ← pow_mul, mul_comm]

/-- Membership through the information coordinates. -/
lemma mem_codeS_of_sys {info : Fin rows.length → Fin n} {x : Fin n → F}
    (hx : ∀ i, x i = ∑ r, x (info r) * gen n rows r i) : x ∈ codeS n rows :=
  ⟨fun r => x (info r), funext fun i => (hx i).symm⟩

lemma act_encS (g : SP (Fin n)) (a : Fin rows.length → F) :
    g.act (encS n rows a) = ∑ r, a r • g.act (gen n rows r) := by
  have h : encS n rows a = ∑ r, a r • gen n rows r := by
    funext i; simp [encS, Finset.sum_apply]
  rw [h]
  induction (Finset.univ : Finset (Fin rows.length)) using Finset.induction_on with
  | empty => simp [SP.act_zero]
  | insert r s hr ih => rw [Finset.sum_insert hr, Finset.sum_insert hr, SP.act_add, SP.act_smul, ih]

/-- A signed permutation preserves a seed code if it maps every row into it (checked through the
information coordinates). -/
theorem Inv_codeS {info : Fin rows.length → Fin n} (g : SP (Fin n))
    (h : ∀ r i, g.act (gen n rows r) i = ∑ r', g.act (gen n rows r) (info r') * gen n rows r' i) :
    g.Inv (codeS n rows) := by
  rintro _ ⟨a, rfl⟩
  rw [act_encS]
  exact (codeS n rows).sum_mem fun r _ => (codeS n rows).smul_mem _ (mem_codeS_of_sys (h r))

/-- Extension by zero. -/
def ext (x : Fin n → F) : ℕ → F := fun i => if h : i < n then x ⟨i, h⟩ else 0

lemma ext_encS (hbits : ∀ r ∈ rows, r.1 < 2 ^ n ∧ r.2 < 2 ^ n) (a : Fin rows.length → F) :
    ext (encS n rows a) = ∑ r, a r • decN rows[r] := by
  funext i
  simp only [ext, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rfl
  · symm
    refine Finset.sum_eq_zero fun r _ => ?_
    have hb := hbits rows[r] (List.getElem_mem _)
    have h1 : rows[r].1.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb.1 (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have h2 : rows[r].2.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb.2 (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [Fin.getElem_fin] at h1 h2
    simp [decN, h1, h2]

lemma wtP_eq : ∀ u : P → F, wtP u = (if u (0, 0) ≠ 0 then 1 else 0) + (if u (0, 1) ≠ 0 then 1 else 0) +
    (if u (1, 0) ≠ 0 then 1 else 0) + (if u (1, 1) ≠ 0 then 1 else 0) := by decide

/-- The singleton coordinates of a placement `c`. -/
def sListOf {a b : ℕ} (c : Blk (Fin a) (Fin b) → Fin n) : List ℕ := List.ofFn fun s => (c (.inl s)).val

/-- The blocks of a placement `c`, in the order `(0,0), (0,1), (1,0), (1,1)`. -/
def bListOf {a b : ℕ} (c : Blk (Fin a) (Fin b) → Fin n) : List (ℕ × ℕ × ℕ × ℕ) :=
  List.ofFn fun β => ((c (.inr (β, (0, 0)))).val, (c (.inr (β, (0, 1)))).val,
    (c (.inr (β, (1, 0)))).val, (c (.inr (β, (1, 1)))).val)

lemma Rw_eq_Wt {a b : ℕ} (c : Blk (Fin a) (Fin b) → Fin n) (x : Fin n → F) :
    Rw (fun i => x (c i)) = Wt (sListOf c) (bListOf c) (ext x) := by
  unfold Rw Wt sListOf bListOf
  have he : ∀ j : Fin n, ext x j.val = x j := fun j => by simp [ext, j.isLt]
  rw [List.map_ofFn, List.prod_ofFn, List.map_ofFn, List.prod_ofFn]
  congr 1
  · exact Finset.prod_congr rfl fun s _ => by simp only [Function.comp_apply, he]
  · refine Finset.prod_congr rfl fun β _ => ?_
    simp only [Function.comp_apply, cnt4, he, wtP_eq]

variable (n rows) in
/-- **The seed formula.** `R` of a seed code equals the value of an admissible fast tree. -/
theorem R_seed {a b : ℕ} (c : Blk (Fin a) (Fin b) → Fin n) (hc : Function.Bijective c)
    {info : Fin rows.length → Fin n} (hsys : Sys info)
    (hbits : ∀ r ∈ rows, r.1 < 2 ^ n ∧ r.2 < 2 ^ n) (sL : List ℕ) (bL : List (ℕ × ℕ × ℕ × ℕ))
    (hsL : sListOf c = sL) (hbL : bListOf c = bL) (st : List FStep) (hst : rowsOf st = rows)
    (hv : fvalid sL bL st = true) :
    R (relabel (Equiv.ofBijective c hc) (codeS n rows)) = fastT (WtF sL bL) st 0 0 := by
  unfold R
  rw [sum_relabel, CSG_codeS, Finset.sum_image (fun a _ b _ h => encS_inj hsys h)]
  rw [show (0 : ℕ) = ((0, 0) : ℕ × ℕ).1 from rfl, fastT_eq sL bL st (0, 0) hv valid_zero, decN_zero,
    hst, show rows.map decN = List.ofFn (fun r : Fin rows.length => decN rows[r]) from
      (List.ofFn_getElem_eq_map rows decN).symm, fullS_eq_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [zero_add, ← ext_encS hbits, ← hsL, ← hbL, ← Rw_eq_Wt]
  rfl

end Seed

end Eval

end GJF.Ex
