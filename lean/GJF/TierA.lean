import GJF.ChainJ
import GJF.ChainQ8
import GJF.ChainZ12
import GJF.ChainQ8Z3

/-!
# Tier A: the code-level Main Question (notes/blueprint/README.md §4)

For every `k ≥ 1` there is a self-dual ternary code `C` of length `12k` with index 24 and a group of
signed permutations in `Aut(C)` satisfying the hypotheses `MQcode(k)` of
notes/blueprint/chains-and-seeds.md §1.7, with `m = gcd(k, 24)`:

* `m ∈ {1, 2}`: nothing more;
* `m = 4`: `J ∈ Aut(C)` with `J² = -1`;
* `m ∈ {3, 6, 12}`: `g ∈ Aut(C)` with `g^m = 1`, `g^(m/2) = -1` for even `m`, and `h = g^(m/3)`
  without fixed coordinate and with `T_h(C) = 0`;
* `m = 8`: `J, K ∈ Aut(C)` with `J² = K² = -1`, `KJ = -JK`;
* `m = 24`: `J, K, h ∈ Aut(C)` with these relations, `h³ = 1`, `hJ = Jh`, `hK = Kh`, `h` without
  fixed coordinate and `T_h(C) = 0`.

The case `m = 24` uses the one seed value not checked by the kernel, `R_σ(E₇₂) = 24`, as the
hypothesis `Q8Z3.E72Hyp`. Everything else is proved from the definitions, with the standard axioms.
-/

open Finset

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Ex

local notation "F" => ZMod 3

/-- The group-theoretic part of `MQcode(k)` for `m = gcd(k, 24)`, on a code of length `n`. -/
def MQ (n m : ℕ) (C : Submodule F (Fin n → F)) : Prop :=
  (m = 4 → ∃ J : SP (Fin n), J.Inv C ∧ J * J = -1) ∧
  ((m = 3 ∨ m = 6 ∨ m = 12) → ∃ g : SP (Fin n), g.Inv C ∧ g ^ m = 1 ∧
      (Even m → g ^ (m / 2) = -1) ∧ (g ^ (m / 3)).FPF ∧ Th (g ^ (m / 3)) C = 0) ∧
  (m = 8 → ∃ J K : SP (Fin n), J.Inv C ∧ K.Inv C ∧ J * J = -1 ∧ K * K = -1 ∧ K * J = -(J * K)) ∧
  (m = 24 → ∃ J K h : SP (Fin n), J.Inv C ∧ K.Inv C ∧ h.Inv C ∧ J * J = -1 ∧ K * K = -1 ∧
      K * J = -(J * K) ∧ h ^ 3 = 1 ∧ h * J = J * h ∧ h * K = K * h ∧ h.FPF ∧ Th h C = 0)

/-- **`MQcode(k)`**: a self-dual code of length `12k`, index 24, with the group data for
`gcd(k, 24)`. -/
def MQcode (k : ℕ) : Prop :=
  ∃ C : Submodule F (Fin (12 * k) → F), IsSelfDual C ∧ gjfIndex C = 24 ∧ MQ (12 * k) (Nat.gcd k 24) C

lemma SP.neg_one_sq {X : Type} : (-1 : SP X) * -1 = 1 := by
  rw [SP.neg_mul, SP.mul_neg, SP.neg_neg, one_mul]

lemma SP.Inv.pow {X : Type} {g : SP X} {C : Submodule F (X → F)} (hg : g.Inv C) (m : ℕ) :
    (g ^ m).Inv C := by
  induction m with
  | zero => rw [pow_zero]; exact SP.Inv.one C
  | succ m ih => rw [pow_succ]; exact ih.mul hg

lemma SP.neg_one_pow_two {X : Type} : (-1 : SP X) ^ 2 = 1 := by
  rw [sq, SP.neg_one_sq]

/-- **Tier A.** Given `R_σ(E₇₂) = 24`, `MQcode(k)` holds for every `k ≥ 1`. -/
theorem tierA (hE : Q8Z3.E72Hyp) (k : ℕ) (hk : 1 ≤ k) : MQcode k := by
  have hdiv : Nat.gcd k 24 ∣ k := Nat.gcd_dvd_left _ _
  have hm : Nat.gcd k 24 ∈ Nat.divisors 24 :=
    Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, by norm_num⟩
  rw [show Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} by decide] at hm
  unfold MQcode
  generalize Nat.gcd k 24 = m at hm hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  -- the cyclic cases share one construction
  have hcyc : 3 ∣ k → ∃ (C : Submodule F (Fin (12 * k) → F)) (g : SP (Fin (12 * k))),
      IsSelfDual C ∧ gjfIndex C = 24 ∧ g.Inv C ∧ g ^ 6 = -1 ∧ (g ^ 4).FPF ∧ Th (g ^ 4) C = 0 :=
    fun h3 => Z12.exists_Z12 k h3 (by omega)
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨C, hC, hI⟩ := exists_selfDual_index24 k hk
    exact ⟨C, hC, hI, by simp [MQ]⟩
  · obtain ⟨C, hC, hI⟩ := exists_selfDual_index24 k hk
    exact ⟨C, hC, hI, by simp [MQ]⟩
  · -- m = 3: x = g⁴
    obtain ⟨C, g, hC, hI, hg, h6, hF, hT⟩ := hcyc hdiv
    refine ⟨C, hC, hI, by simp, fun _ => ⟨g ^ 4, ?_, ?_, ?_, ?_, ?_⟩, by simp, by simp⟩
    · exact SP.Inv.pow hg 4
    · rw [← pow_mul, show 4 * 3 = 6 * 2 by norm_num, pow_mul, h6, SP.neg_one_pow_two]
    · intro h; exact absurd h (by decide)
    · simpa using hF
    · simpa using hT
  · -- m = 4
    obtain ⟨j, rfl⟩ := hdiv
    obtain ⟨C, J, hC, hI, hJ, hJ2⟩ := JChain.exists_J (4 * j) (by omega) ⟨2 * j, by ring⟩
    exact ⟨C, hC, hI, fun _ => ⟨J, hJ, hJ2⟩, by simp, by simp, by simp⟩
  · -- m = 6: x = g²
    obtain ⟨C, g, hC, hI, hg, h6, hF, hT⟩ := hcyc (Nat.dvd_trans (by norm_num) hdiv)
    refine ⟨C, hC, hI, by simp, fun _ => ⟨g ^ 2, ?_, ?_, ?_, ?_, ?_⟩, by simp, by simp⟩
    · exact SP.Inv.pow hg 2
    · rw [← pow_mul, show 2 * 6 = 6 * 2 by norm_num, pow_mul, h6, SP.neg_one_pow_two]
    · intro _; rw [← pow_mul]; exact h6
    · rw [← pow_mul]; exact hF
    · rw [← pow_mul]; exact hT
  · -- m = 8
    obtain ⟨C, J, K, hC, hI, hJ, hK, h1, h2, h3⟩ :=
      Q8Chain.exists_Q8 k (by obtain ⟨j, rfl⟩ := hdiv; omega) (Nat.dvd_trans (by norm_num) hdiv)
    exact ⟨C, hC, hI, by simp, by simp, fun _ => ⟨J, K, hJ, hK, h1, h2, h3⟩, by simp⟩
  · -- m = 12: x = g
    obtain ⟨C, g, hC, hI, hg, h6, hF, hT⟩ := hcyc (Nat.dvd_trans (by norm_num) hdiv)
    refine ⟨C, hC, hI, by simp, fun _ => ⟨g, hg, ?_, fun _ => h6, hF, hT⟩, by simp, by simp⟩
    rw [show g ^ 12 = (g ^ 6) ^ 2 by rw [← pow_mul], h6, SP.neg_one_pow_two]
  · -- m = 24
    obtain ⟨C, J, K, h, hC, hI, hJ, hK, hh, r1, r2, r3, r4, r5, r6, hF, hT⟩ :=
      Q8Z3.exists_Q8Z3 hE k (Nat.dvd_trans (by norm_num) hdiv) (by omega)
    exact ⟨C, hC, hI, by simp, by simp, by simp,
      fun _ => ⟨J, K, h, hJ, hK, hh, r1, r2, r3, r4, r5, r6, hF, hT⟩⟩

end GJF.Ex
