import GJF.SeedQ8Z3Data

/-!
# The Q₈ × ℤ/3-chain (Main Question, `24 ∣ k`), with `R_σ(E₇₂) = 24` as a hypothesis

The seed is `q8z3_seed72` (length 72), with `J, K` (left multiplication by `i, j` on each
`Q₈`-orbit) and `h` (a pure permutation cycling the orbits in triples). The blocks are the orbit
blocks of the first two `h`-triples, labelled `(s, t)` (`h : t ↦ t + 1`); `J` acts on each block by
`A 1`, `K` by `B 1` (it swaps the pairs), `h` by the identity.

Every seed fact is checked by the kernel except `R_σ(E₇₂) = 24` (`E72Hyp`), which needs `5.8·10⁶`
normalised SL₂-words or `2³⁶` information-set patterns (notes/blueprint/chains-and-seeds.md §3.5;
confirmed by three independent programs, `ternary60/theory/mainq_e72_infoset.py`).

* `exists_Q8Z3`: given `E72Hyp`, for every `k ≡ 0 mod 12` a self-dual code of length `12k` with
  index 24, `J, K, h ∈ Aut(C)` with the `Q₈` relations, `h³ = 1`, `h` commuting with `J` and `K`,
  `h` without fixed coordinate, and `T_h(C) = 0`.
-/

open Finset

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GJF.Ex

local notation "F" => ZMod 3

namespace Q8Z3

open Eval

set_option maxRecDepth 100000

/-- The shift `t ↦ t + 1` of `Fin 3`. -/
def shift : Equiv.Perm (Fin 3) := Equiv.addRight 1

/-! ### The seed -/

noncomputable def E : Submodule F (Fin 72 → F) := codeS 72 rows

lemma sys : Sys info := by unfold Sys; decide

lemma orth : ∀ r r', ∑ i, gen 72 rows r i * gen 72 rows r' i = 0 := by decide +kernel

theorem selfDual : SelfDualG E := selfDual_codeS sys orth rfl

def Jf : SP (Fin 72) := ⟨⟨Jperm, Jinv, by decide, by decide⟩, Jsgn, by decide⟩
def Kf : SP (Fin 72) := ⟨⟨Kperm, Kinv, by decide, by decide⟩, Ksgn, by decide⟩
def Hf : SP (Fin 72) := ⟨⟨Hperm, Hinv, by decide, by decide⟩, Hsgn, by decide⟩

theorem Jf_inv : Jf.Inv E := Inv_codeS (info := info) Jf (by decide +kernel)
theorem Kf_inv : Kf.Inv E := Inv_codeS (info := info) Kf (by decide +kernel)
theorem Hf_inv : Hf.Inv E := Inv_codeS (info := info) Hf (by decide +kernel)

lemma c_bij : Function.Bijective c := by decide +kernel

noncomputable def e : Blk (Fin 48) (Fin 2 × Fin 3) ≃ Fin 72 := Equiv.ofBijective c c_bij

/-- The seed state. -/
noncomputable def E0 : Submodule F (Blk (Fin 48) (Fin 2 × Fin 3) → F) := relabel e E

/-- **The one seed fact not checked here:** `R_σ(E₇₂) = 24`. -/
def E72Hyp : Prop := R E0 = 24

def JM : SM (Fin 48) (Fin 2 × Fin 3) :=
  ⟨⟨⟨JSperm, JSinv, by decide, by decide⟩, JSsgn, by decide⟩, 1, fun _ => (1, false)⟩
def KM : SM (Fin 48) (Fin 2 × Fin 3) :=
  ⟨⟨⟨KSperm, KSinv, by decide, by decide⟩, KSsgn, by decide⟩, 1, fun _ => (1, true)⟩
def HM : SM (Fin 48) (Fin 2 × Fin 3) :=
  ⟨⟨⟨HSperm, HSinv, by decide, by decide⟩, HSsgn, by decide⟩, Equiv.prodCongr 1 shift,
    fun _ => lone⟩

lemma JM_c : ∀ i, c (JM.toSP.perm i) = Jf.perm (c i) ∧ JM.toSP.sgn i = Jf.sgn (c i) := by
  decide +kernel
lemma KM_c : ∀ i, c (KM.toSP.perm i) = Kf.perm (c i) ∧ KM.toSP.sgn i = Kf.sgn (c i) := by
  decide +kernel
lemma HM_c : ∀ i, c (HM.toSP.perm i) = Hf.perm (c i) ∧ HM.toSP.sgn i = Hf.sgn (c i) := by
  decide +kernel

lemma JM_inv : JM.toSP.Inv E0 := by rw [toSP_of_c c_bij JM_c]; exact Jf_inv.pull _
lemma KM_inv : KM.toSP.Inv E0 := by rw [toSP_of_c c_bij KM_c]; exact Kf_inv.pull _
lemma HM_inv : HM.toSP.Inv E0 := by rw [toSP_of_c c_bij HM_c]; exact Hf_inv.pull _

lemma JM_sq : JM * JM = -1 := by decide +kernel
lemma KM_sq : KM * KM = -1 := by decide +kernel
lemma KJ : KM * JM = -(JM * KM) := by decide +kernel
lemma HM_cube : HM ^ 3 = 1 := by decide +kernel
lemma HJ : HM * JM = JM * HM := by decide +kernel
lemma HK : HM * KM = KM * HM := by decide +kernel

lemma HM_pure : HM.PureL := ⟨by unfold SP.Pure; decide, fun _ => rfl⟩
lemma HM_fpf : HM.gS.FPF := by unfold SP.FPF; decide

/-- The orbit structure of the blocks `(s, t)` under `h`. -/
def ψ6 : Fin 2 × Fin 3 ≃ Fin 2 × Fin 3 := Equiv.refl _

lemma HM_orb : OrbS HM.π ψ6 := by unfold OrbS; decide

theorem fastRh : fastT (WtF sL bLrep) ftree 0 0 = 0 := by decide +kernel

lemma sysF : Sys (n := 72) (rows := frows) J := by unfold Sys; decide +kernel

lemma memF : ∀ j, gen 72 frows j ∈ codeS 72 rows := fun j =>
  mem_codeS_of_sys (info := info) (by revert j; decide +kernel)

lemma fixF : ∀ j, Hf.act (gen 72 frows j) = gen 72 frows j := by decide +kernel

lemma certL : ∀ r r' : Fin 36, ((L r).map fun cl => cl.2 * fixForm (rows := rows) Hf J cl.1 r').sum =
    if r = r' then 1 else 0 := by decide +kernel

theorem Rh_E0 : Rh HM ψ6 E0 = 0 := by
  rw [E0, e, E, Rh_seed c c_bij HM Hf (toSP_of_c c_bij HM_c) ψ6 (Equiv.refl (Fin 2)) sysF memF fixF L
    certL (by decide +kernel) sL bLrep (by decide +kernel) (by decide +kernel) ftree rfl
    (by decide +kernel)]
  exact fastRh

/-! ### The chain -/

/-- The refined step-one blocks and their images: `O = Fin 2 × Fin 3`, `(a, t)`. -/
abbrev O := Fin 2 × Fin 3

/-- Generators `0 ↦ J`, `1 ↦ K`, `2 ↦ h`, and their block permutations on `O`. -/
def πO : Fin 3 → Equiv.Perm O := ![1, Equiv.prodCongr (Equiv.swap 0 1) 1, Equiv.prodCongr 1 shift]

/-- The orbit structure of `O` under `h`. -/
def ψO : Fin 2 × Fin 3 ≃ O := Equiv.refl _

lemma orbO : OrbS (πO 2) ψO := by unfold OrbS; decide

lemma πO_rel : πO 0 * πO 0 = 1 ∧ πO 1 * πO 1 = 1 ∧ πO 1 * πO 0 = πO 0 * πO 1 ∧ πO 2 ^ 3 = 1 ∧
    πO 2 * πO 0 = πO 0 * πO 2 ∧ πO 2 * πO 1 = πO 1 * πO 2 := by decide

/-- The relations of `Q₈ × ℤ/3`. -/
def Rel3 {M : Type} [Monoid M] [Neg M] (g : Fin 3 → M) : Prop :=
  g 0 * g 0 = -1 ∧ g 1 * g 1 = -1 ∧ g 1 * g 0 = -(g 0 * g 1) ∧ g 2 ^ 3 = 1 ∧
    g 2 * g 0 = g 0 * g 2 ∧ g 2 * g 1 = g 1 * g 2

lemma Rel3.map {M N : Type} [Monoid M] [Neg M] [Monoid N] [Neg N] {g : Fin 3 → M} (f : M → N)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hone : f 1 = 1) (hneg : ∀ a, f (-a) = -f a)
    (h : Rel3 g) : Rel3 (fun i => f (g i)) := by
  have hpow : ∀ a : M, f (a ^ 3) = f a ^ 3 := fun a => by
    rw [pow_succ, pow_succ, pow_one, hmul, hmul, pow_succ, pow_succ, pow_one]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hmul, h1, hneg, hone]
  · rw [← hmul, h2, hneg, hone]
  · rw [← hmul, h3, hneg, hmul]
  · rw [← hpow, h4, hone]
  · rw [← hmul, h5, hmul]
  · rw [← hmul, h6, hmul]

/-- The invariant of a state. -/
def QS {S : Type} [Fintype S] [DecidableEq S] (E : Submodule F (Blk S (O × Fin 2) → F))
    (gens : Fin 3 → SM S (O × Fin 2)) : Prop :=
  Rel3 gens ∧ (gens 2).PureL ∧ (gens 2).gS.FPF ∧ Rh (gens 2) (orbProd ψO) E = 0

/-- The invariant of a code. -/
def QC {X : Type} [Fintype X] [DecidableEq X] (C : Submodule F (X → F)) (gens : Fin 3 → SP X) :
    Prop :=
  Rel3 gens ∧ (gens 2).FPF ∧ Th (gens 2) C = 0

lemma qc_of {S B B' : Type} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    [Fintype B'] [DecidableEq B'] (E : Submodule F (Blk S B → F)) {g : Fin 3 → SM S B}
    (hr : Rel3 g) (hp : (g 2).PureL) (hS : (g 2).gS.FPF) {ψ : B' × Fin 3 ≃ B}
    (hψ : OrbS (g 2).π ψ) (hR : Rh (g 2) ψ E = 0) :
    QC (Qt E) (fun i => (SM.step1 (g i)).extD) := by
  refine ⟨Rel3.map (fun x => (SM.step1 x).extD) (fun a b => by rw [SM.step1_mul, SM.extD_mul])
    (by rw [SM.step1_one, SM.extD_one]) (fun a => by rw [SM.step1_neg, SM.extD_neg]) hr, ?_, ?_⟩
  · exact FPF_st1_extD hp hS hψ
  · show Th (SM.step1 (g 2)).extD (Qt E) = 0
    rw [Th_Qt E hp hψ, hR]

lemma qs_step {S : Type} [Fintype S] [DecidableEq S] (E : Submodule F (Blk S (O × Fin 2) → F))
    {g : Fin 3 → SM S (O × Fin 2)} (hu : ∀ i, Unif (g i) (πO i)) (hq : QS E g) :
    QS (NSt (spO O) E) (fun i => nxt (g i) (πO i)) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hp, hS, hR⟩ := hq
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := πO_rel
  have hψ : OrbS (g 2).π (orbProd ψO) := by rw [(hu 2).1]; exact orbO.prodCongr
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hp.newSM _ _, FPF_newSM_gS hp hS hψ (hu 2).compat, ?_⟩
  · show nxt (g 0) (πO 0) * nxt (g 0) (πO 0) = -1
    rw [← nxt_mul (hu 0), h1, p1, nxt_negOne]
  · show nxt (g 1) (πO 1) * nxt (g 1) (πO 1) = -1
    rw [← nxt_mul (hu 1), h2, p2, nxt_negOne]
  · show nxt (g 1) (πO 1) * nxt (g 0) (πO 0) = -(nxt (g 0) (πO 0) * nxt (g 1) (πO 1))
    rw [← nxt_mul (hu 0), ← nxt_mul (hu 1), h3, p3, nxt_neg]
  · show nxt (g 2) (πO 2) ^ 3 = 1
    rw [← nxt_pow (hu 2), h4, p4, nxt_one]
  · show nxt (g 2) (πO 2) * nxt (g 0) (πO 0) = nxt (g 0) (πO 0) * nxt (g 2) (πO 2)
    rw [← nxt_mul (hu 0), ← nxt_mul (hu 2), h5, p5]
  · show nxt (g 2) (πO 2) * nxt (g 1) (πO 1) = nxt (g 1) (πO 1) * nxt (g 2) (πO 2)
    rw [← nxt_mul (hu 1), ← nxt_mul (hu 2), h6, p6]
  · show Rh (nxt (g 2) (πO 2)) (orbProd ψO) (NSt (spO O) E) = 0
    unfold nxt
    rw [Rh_NSt _ E hp hψ (hu 2).compat orbO]
    exact hR

lemma qc_step {S : Type} [Fintype S] [DecidableEq S] (E : Submodule F (Blk S (O × Fin 2) → F))
    {g : Fin 3 → SM S (O × Fin 2)} (hu : ∀ i, Unif (g i) (πO i)) (hq : QS E g) :
    QC (Qt E) (fun i => (SM.step1 (g i)).extD) := by
  obtain ⟨hr, hp, hS, hR⟩ := hq
  have hψ : OrbS (g 2).π (orbProd ψO) := by rw [(hu 2).1]; exact orbO.prodCongr
  exact qc_of E hr hp hS hψ hR

/-- Stage 0 refines the step-one blocks of the first `h`-triple: `((0, t), a) ↦ (a, t)`. -/
def sp0 : (Fin 2 × Fin 3) × Fin 2 ≃ O ⊕ O where
  toFun x := if x.1.1 = 0 then .inl (x.2, x.1.2) else .inr (x.2, x.1.2)
  invFun y := y.elim (fun o => ((0, o.2), o.1)) (fun o => ((1, o.2), o.1))
  left_inv := by decide
  right_inv := by decide

def gensM : Fin 3 → SM (Fin 48) (Fin 2 × Fin 3) := ![JM, KM, HM]

lemma compat : ∀ i, SM.Compat sp0 (gensM i) (πO i) (πO i) := by
  intro i; fin_cases i <;> (unfold SM.Compat; decide)

lemma relM : Rel3 gensM := ⟨JM_sq, KM_sq, KJ, HM_cube, HJ, HK⟩

theorem q_state (hE : E72Hyp) : GCode (Fin 3) QC 144 ∧ UState O (Fin 3) πO QS 144 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := relM
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := πO_rel
  have c0 := compat 0
  have c1 := compat 1
  have c2 := compat 2
  have h := stage0 (Q := QS) (Q' := QC) E0 (selfDual_relabel _ selfDual) hE gensM
    (fun i => by fin_cases i; exacts [JM_inv, KM_inv, HM_inv]) sp0 πO πO compat ?_ ?_
  · simpa using h
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, HM_pure.newSM _ _, FPF_newSM_gS HM_pure HM_fpf HM_orb c2, ?_⟩
    · show SM.newSM sp0 (gensM 0) (πO 0) (πO 0) * SM.newSM sp0 (gensM 0) (πO 0) (πO 0) = -1
      rw [← SM.newSM_mul c0, h1, p1, SM.newSM_neg, SM.newSM_one]
    · show SM.newSM sp0 (gensM 1) (πO 1) (πO 1) * SM.newSM sp0 (gensM 1) (πO 1) (πO 1) = -1
      rw [← SM.newSM_mul c1, h2, p2, SM.newSM_neg, SM.newSM_one]
    · show SM.newSM sp0 (gensM 1) (πO 1) (πO 1) * SM.newSM sp0 (gensM 0) (πO 0) (πO 0) =
        -(SM.newSM sp0 (gensM 0) (πO 0) (πO 0) * SM.newSM sp0 (gensM 1) (πO 1) (πO 1))
      rw [← SM.newSM_mul c0, ← SM.newSM_mul c1, h3, p3, SM.newSM_neg]
    · show SM.newSM sp0 (gensM 2) (πO 2) (πO 2) ^ 3 = 1
      rw [← SM.newSM_pow c2, h4, p4, SM.newSM_one]
    · show SM.newSM sp0 (gensM 2) (πO 2) (πO 2) * SM.newSM sp0 (gensM 0) (πO 0) (πO 0) =
        SM.newSM sp0 (gensM 0) (πO 0) (πO 0) * SM.newSM sp0 (gensM 2) (πO 2) (πO 2)
      rw [← SM.newSM_mul c0, ← SM.newSM_mul c2, h5, p5]
    · show SM.newSM sp0 (gensM 2) (πO 2) (πO 2) * SM.newSM sp0 (gensM 1) (πO 1) (πO 1) =
        SM.newSM sp0 (gensM 1) (πO 1) (πO 1) * SM.newSM sp0 (gensM 2) (πO 2) (πO 2)
      rw [← SM.newSM_mul c1, ← SM.newSM_mul c2, h6, p6]
    · show Rh (SM.newSM sp0 HM (πO 2) (πO 2)) (orbProd ψO) (NSt sp0 E0) = 0
      rw [Rh_NSt sp0 E0 HM_pure HM_orb c2 orbO, Rh_E0]
  · exact qc_of E0 relM HM_pure HM_fpf HM_orb Rh_E0

theorem q_codes (hE : E72Hyp) (j : ℕ) : GCode (Fin 3) QC (144 * (j + 1)) := by
  rcases j with _ | j
  · simpa using (q_state hE).1
  · have := ustate_chain (Q := QS) (Q' := QC) ?_ ?_ (q_state hE).2 j
    · simpa [show 144 + 144 * (j + 1) = 144 * (j + 1 + 1) by ring] using this
    · intro S _ _ E gens _ hu hq
      exact qs_step E hu hq
    · intro S _ _ E gens _ hu hq
      exact qc_step E hu hq

lemma QC_pull {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (e : Y ≃ X)
    (C : Submodule F (X → F)) (gens : Fin 3 → SP X) (hq : QC C gens) :
    QC (relabel e C) (fun i => SP.pull e (gens i)) := by
  obtain ⟨hr, hF, hT⟩ := hq
  exact ⟨Rel3.map (SP.pull e) (SP.pull_mul e) (SP.pull_one e) (SP.pull_neg e) hr, hF.pull e,
    by rw [Th_relabel, hT]⟩

/-- **The Q₈ × ℤ/3-chain.** Given `R_σ(E₇₂) = 24`: for every `k ≡ 0 mod 12` there is a self-dual
ternary code of length `12k` with index `24`, signed permutations `J, K, h ∈ Aut(C)` with
`J² = K² = -1`, `KJ = -JK`, `h³ = 1`, `hJ = Jh`, `hK = Kh`, `h` without fixed coordinate, and
`T_h(C) = 0`. -/
theorem exists_Q8Z3 (hE : E72Hyp) (k : ℕ) (hk : 12 ∣ k) (hk0 : 0 < k) :
    ∃ (C : Submodule F (Fin (12 * k) → F)) (J K h : SP (Fin (12 * k))),
      IsSelfDual C ∧ gjfIndex C = 24 ∧ J.Inv C ∧ K.Inv C ∧ h.Inv C ∧
        J * J = -1 ∧ K * K = -1 ∧ K * J = -(J * K) ∧ h ^ 3 = 1 ∧ h * J = J * h ∧ h * K = K * h ∧
          h.FPF ∧ Th h C = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 12 * (j + 1) := by
    obtain ⟨m, hm⟩ := hk; exact ⟨m - 1, by omega⟩
  obtain ⟨C, gens, hC, hI, hinv, ⟨h1, h2, h3, h4, h5, h6⟩, hF, hT⟩ :=
    GCode.toFin (Q' := QC) QC_pull (q_codes hE j)
  rw [show 12 * (12 * (j + 1)) = 144 * (j + 1) by ring]
  exact ⟨C, gens 0, gens 1, gens 2, hC, hI, hinv 0, hinv 1, hinv 2, h1, h2, h3, h4, h5, h6, hF, hT⟩

end Q8Z3

end GJF.Ex
