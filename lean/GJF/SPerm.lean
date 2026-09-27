import GJF.Existence

/-!
# Signed permutations

A signed permutation `g` of a type `X` acts on `𝔽₃^X` by `e_i ↦ sgn(i) · e_{perm i}`, i.e.
`(g • x)(perm i) = sgn i · x i`. These are the monomial maps `2^X : S_X` of GJF.

* `SP X`: the signed permutations, with composition (`g * h` = first `h`, then `g`), `1` and
  negation; `act` is a monoid action by linear maps.
* `Inv g C`: `g` maps the code `C` into itself (so `g ∈ Aut(C)`).
* Constructions used by the chains: `pull` (transport along an equivalence, compatible with
  `relabel`), `sum`, `prodR` (act on the first factor of `X × T`), `blk` (a block permutation with a
  local signed permutation on each block).
-/

open Finset

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Ex

local notation "F" => ZMod 3

/-- A signed permutation of `X`: `e_i ↦ sgn i · e_{perm i}`, with `sgn i = ±1`. -/
@[ext]
structure SP (X : Type*) where
  perm : Equiv.Perm X
  sgn : X → F
  sgn_sq : ∀ i, sgn i * sgn i = 1

namespace SP

variable {X Y Z : Type*}

lemma sgn_ne_zero (g : SP X) (i : X) : g.sgn i ≠ 0 := by
  intro h; have := g.sgn_sq i; rw [h, zero_mul] at this; exact zero_ne_one this

/-- The action on words: `(g • x)(perm i) = sgn i · x i`. -/
def act (g : SP X) (x : X → F) : X → F := fun j => g.sgn (g.perm.symm j) * x (g.perm.symm j)

@[simp] lemma act_perm (g : SP X) (x : X → F) (i : X) : g.act x (g.perm i) = g.sgn i * x i := by
  simp [act]

lemma act_add (g : SP X) (x y : X → F) : g.act (x + y) = g.act x + g.act y := by
  funext j; simp [act, mul_add]

lemma act_smul (g : SP X) (c : F) (x : X → F) : g.act (c • x) = c • g.act x := by
  funext j; simp [act]; ring

lemma act_zero (g : SP X) : g.act 0 = 0 := by funext j; simp [act]

lemma act_neg_word (g : SP X) (x : X → F) : g.act (-x) = -g.act x := by funext j; simp [act]

/-- Composition: first `h`, then `g`. -/
def mul (g h : SP X) : SP X where
  perm := h.perm.trans g.perm
  sgn i := h.sgn i * g.sgn (h.perm i)
  sgn_sq i := by
    calc h.sgn i * g.sgn (h.perm i) * (h.sgn i * g.sgn (h.perm i))
        = (h.sgn i * h.sgn i) * (g.sgn (h.perm i) * g.sgn (h.perm i)) := by ring
      _ = 1 := by rw [h.sgn_sq, g.sgn_sq, one_mul]

/-- The identity. -/
def one : SP X := ⟨Equiv.refl X, fun _ => 1, fun _ => by simp⟩

/-- Negation `x ↦ -x`, composed with `g`. -/
def neg (g : SP X) : SP X := ⟨g.perm, fun i => -g.sgn i, fun i => by rw [neg_mul_neg, g.sgn_sq]⟩

instance : Mul (SP X) := ⟨mul⟩
instance : One (SP X) := ⟨one⟩
instance : Neg (SP X) := ⟨neg⟩

@[simp] lemma mul_perm (g h : SP X) : (g * h).perm = h.perm.trans g.perm := rfl
@[simp] lemma mul_sgn (g h : SP X) (i : X) : (g * h).sgn i = h.sgn i * g.sgn (h.perm i) := rfl
@[simp] lemma one_perm : (1 : SP X).perm = Equiv.refl X := rfl
@[simp] lemma one_sgn (i : X) : (1 : SP X).sgn i = 1 := rfl
@[simp] lemma neg_perm (g : SP X) : (-g).perm = g.perm := rfl
@[simp] lemma neg_sgn (g : SP X) (i : X) : (-g).sgn i = -g.sgn i := rfl

instance : Monoid (SP X) where
  mul_assoc a b c := by ext i <;> simp [mul_assoc]
  one_mul a := by ext i <;> simp
  mul_one a := by ext i <;> simp

lemma act_mul (g h : SP X) (x : X → F) : (g * h).act x = g.act (h.act x) := by
  funext j
  obtain ⟨i, rfl⟩ := (h.perm.trans g.perm).surjective j
  have : (g * h).act x ((h.perm.trans g.perm) i) = h.sgn i * g.sgn (h.perm i) * x i :=
    act_perm (g * h) x i
  rw [this]
  simp only [Equiv.trans_apply, act_perm]
  ring

lemma act_one (x : X → F) : (1 : SP X).act x = x := by funext j; simp [act]

lemma act_neg (g : SP X) (x : X → F) : (-g).act x = -g.act x := by
  funext j; simp [act]

lemma neg_mul (g h : SP X) : -g * h = -(g * h) := by ext i <;> simp

lemma mul_neg (g h : SP X) : g * -h = -(g * h) := by ext i <;> simp

lemma neg_neg (g : SP X) : - -g = g := by ext i <;> simp

instance [Fintype X] [DecidableEq X] : DecidableEq (SP X) := fun g h =>
  decidable_of_iff (g.perm = h.perm ∧ g.sgn = h.sgn) (by rw [SP.ext_iff])

/-- `g` maps `C` into itself. -/
def Inv (g : SP X) (C : Submodule F (X → F)) : Prop := ∀ x ∈ C, g.act x ∈ C

lemma Inv.mul {g h : SP X} {C : Submodule F (X → F)} (hg : g.Inv C) (hh : h.Inv C) :
    (g * h).Inv C := fun x hx => by rw [act_mul]; exact hg _ (hh x hx)

lemma Inv.one (C : Submodule F (X → F)) : (1 : SP X).Inv C := fun x hx => by rwa [act_one]

lemma Inv.neg {g : SP X} {C : Submodule F (X → F)} (hg : g.Inv C) : (-g).Inv C := fun x hx => by
  rw [act_neg]; exact C.neg_mem (hg x hx)

/-- No fixed coordinate. -/
def FPF (g : SP X) : Prop := ∀ i, g.perm i ≠ i

/-- A pure permutation: all signs `+1`. -/
def Pure (g : SP X) : Prop := ∀ i, g.sgn i = 1

/-! ### Transport along an equivalence -/

/-- Transport `g` on `κ` to `ι` along `e : ι ≃ κ` (compatible with `relabel e`). -/
def pull (e : Y ≃ X) (g : SP X) : SP Y where
  perm := e.trans (g.perm.trans e.symm)
  sgn i := g.sgn (e i)
  sgn_sq i := g.sgn_sq (e i)

lemma pull_act (e : Y ≃ X) (g : SP X) (y : Y → F) :
    (pull e g).act y = fun i => g.act (fun k => y (e.symm k)) (e i) := by
  funext i
  simp [act, pull]

lemma pull_mul (e : Y ≃ X) (g h : SP X) : pull e (g * h) = pull e g * pull e h := by
  ext i <;> simp [pull]

lemma pull_one (e : Y ≃ X) : pull e (1 : SP X) = 1 := by ext i <;> simp [pull]

lemma pull_neg (e : Y ≃ X) (g : SP X) : pull e (-g) = -pull e g := by ext i <;> simp [pull]

lemma Inv.pull [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] {g : SP X} {C : Submodule F (X → F)} (hg : g.Inv C) (e : Y ≃ X) :
    (pull e g).Inv (relabel e C) := by
  intro y hy
  rw [mem_relabel] at hy ⊢
  rw [pull_act]
  simpa using hg _ hy

lemma FPF.pull {g : SP X} (hg : g.FPF) (e : Y ≃ X) : (pull e g).FPF := by
  intro i h
  apply hg (e i)
  have := congrArg e h
  simpa [SP.pull] using this

lemma Pure.pull {g : SP X} (hg : g.Pure) (e : Y ≃ X) : (pull e g).Pure := fun i => hg (e i)

/-! ### Sums and products -/

/-- `g ⊕ h` on `X ⊕ Y`. -/
def sum (g : SP X) (h : SP Y) : SP (X ⊕ Y) where
  perm := Equiv.sumCongr g.perm h.perm
  sgn := Sum.elim g.sgn h.sgn
  sgn_sq i := by cases i <;> simp [g.sgn_sq, h.sgn_sq]

lemma sum_mul (g g' : SP X) (h h' : SP Y) : sum (g * g') (h * h') = sum g h * sum g' h' := by
  ext i
  · cases i <;> rfl
  · cases i <;> rfl

lemma sum_one : sum (1 : SP X) (1 : SP Y) = 1 := by
  ext i
  · cases i <;> rfl
  · cases i <;> rfl

lemma sum_neg (g : SP X) (h : SP Y) : sum (-g) (-h) = -sum g h := by
  ext i
  · cases i <;> rfl
  · cases i <;> rfl

/-- `g` on the first factor of `X × T`. -/
def prodR (g : SP X) (T : Type*) : SP (X × T) where
  perm := Equiv.prodCongr g.perm (Equiv.refl T)
  sgn p := g.sgn p.1
  sgn_sq p := g.sgn_sq p.1

@[simp] lemma prodR_perm (g : SP X) (T : Type*) (x : X) (t : T) :
    (prodR g T).perm (x, t) = (g.perm x, t) := rfl

@[simp] lemma prodR_sgn (g : SP X) (T : Type*) (x : X) (t : T) :
    (prodR g T).sgn (x, t) = g.sgn x := rfl

lemma prodR_mul (g h : SP X) (T : Type*) : prodR (g * h) T = prodR g T * prodR h T := by
  ext i <;> rfl

lemma prodR_one (T : Type*) : prodR (1 : SP X) T = 1 := by ext i <;> rfl

lemma prodR_neg (g : SP X) (T : Type*) : prodR (-g) T = -prodR g T := by ext i <;> rfl

/-- A block permutation `π` of `B` with a local signed permutation `μ β` on each block
(`(β, q) ↦ (π β, μ_β q)`). -/
def blk {B Q : Type*} (π : Equiv.Perm B) (μ : B → SP Q) : SP (B × Q) where
  perm := Equiv.prodShear π (fun β => (μ β).perm)
  sgn p := (μ p.1).sgn p.2
  sgn_sq p := (μ p.1).sgn_sq p.2

@[simp] lemma blk_perm {B Q : Type*} (π : Equiv.Perm B) (μ : B → SP Q) (β : B) (q : Q) :
    (blk π μ).perm (β, q) = (π β, (μ β).perm q) := rfl

@[simp] lemma blk_sgn {B Q : Type*} (π : Equiv.Perm B) (μ : B → SP Q) (β : B) (q : Q) :
    (blk π μ).sgn (β, q) = (μ β).sgn q := rfl

lemma blk_mul {B Q : Type*} (π π' : Equiv.Perm B) (μ μ' : B → SP Q) :
    blk π μ * blk π' μ' = blk (π * π') (fun β => μ (π' β) * μ' β) := by
  ext ⟨β, q⟩ <;> rfl

lemma blk_one {B Q : Type*} : blk (1 : Equiv.Perm B) (fun _ => (1 : SP Q)) = 1 := by
  ext ⟨β, q⟩ <;> rfl

lemma blk_neg {B Q : Type*} (π : Equiv.Perm B) (μ : B → SP Q) :
    blk π (fun β => -μ β) = -blk π μ := by
  ext ⟨β, q⟩ <;> rfl

end SP

end GJF.Ex
