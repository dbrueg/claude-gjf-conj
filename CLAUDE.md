# Working instructions: GJF Conjecture 1.4 project

Read `notes/ternary-code-index.md` first: §0 for the results, then §5.1 for the existence work. Every claim there carries a status label and, where checkable, a script. Build on the notes; don't restart from scratch.

## Goal

Prove or disprove the existence half of GJF Conj 1.4: a self-dual ternary code of index exactly ±24 at every length 12k. The divisibility half (24 | Index) is already proved (notes §1–2).

## Where things stand (2026-09-29)

**Both halves of Conj 1.4 are now proved here, and both are formally verified in Lean 4** (`GJF.conjecture_1_4`; pending literature check and independent reading).
- **Theorem 5.9** (§5.1(f‴)): an index-±24 code exists at every length 12k. The tool is *partial quadrupling* Q_σ: Hadamard-double a partial 4-block system σ (b blocks) twice against tetracodes and leave the other coordinates alone. This gives length m + 12b and Index = R_σ(E), a block-weighted index (Lemma 5.8). Refining one step-1 block gives a 2-block system with the same R, so (m, 2) → (m + 24, 2). Start from Golay with b = 1 (even k) or b = 2 (odd k).
- Verified by `ternary60/theory/existence_quadruple.py`: exact at n = 24, and Rust |Index| = 24 on explicit chains at n = 36, 48, 60, 72, 84 (log complete; codes in `ternary60/codes/quad_index24_len*.txt`).
- Independently re-verified by `ternary60/theory/paper_check.py` from the paper's definitions, with sign-exact Index = +24 at n = 24 and n = 36 (information-set enumeration).
- **Divisibility half formally verified in Lean 4** (`lean/GJF/Divisibility.lean`); the statement needs n ≥ 1 (n = 0 has index 1).
- **Divisibility half now has a finite, elementary proof** (notes §2 Step 1′, `design_poisson.py`): Poisson on F₃ⁿ for g_ij gives G_ij(C) = −G_ij(C)/3, hence the signed 2-design (◆) and 24 | Index with no modular forms. Critically checked (`divisibility_check.py`); all variants written up in `paper/divisibility.tex`.
- Earlier results in §5.1 still stand: Thm 5.4 (mod 48), Prop 5.5, Lemma 5.6, Thm 5.7 (the s = 0 case of Lemma 5.8), Lemmas 5.2–5.3. The seed search (`existence_seed_search.py`) is no longer needed.

**GJF's Main Question** (index 24/gcd(k,24) at c = 12k; notes `notes/main-question.md`, paper draft `paper/main-question.tex`), 2026-09-26, later session:
- Answered for every k (k ≡ 0 mod 24 via Q₈ × ℤ/3, below). For 24 ∤ k: For 8 ∤ k via GJF Thm 5.6 with the automorphism built into an *equivariant* partial quadrupling (Lemma 4.1): a J-chain from Golay (J² = −1) for gcd = 4, and ℤ/12-chains from a searched length-36 seed for gcd ∈ {3, 6, 12}. The twined count of the order-3 part propagates as R_σ̄ of the collapsed fixed code (Lemma 4.3). gcd ∈ {1, 2} is immediate.
- Obstruction (Thm 5.1): g⁴ = −1 in Aut(C) ⇒ 48 | Index, via a Hermitian four-code identity (◇). So Thm 5.6 never applies when 8 | k. Q₈ escapes this: Q₈-equivariant chains give Q₈-invariant index-24 codes at every k ≡ 0 mod 4, and the Q₈ anomaly is 3k·a with a of order 8 (Thm 8.1; reduction to free fermions in the regular representation, eta invariants on S³/Q₈ give 5/8). So k ≡ 8, 16 mod 24 are answered (index 3); only k ≡ 0 mod 24 is open.
- **The "72-rule" is false** (notes §9): at n = 36, T_h = 0 forces 72 | Index for Q₈ × ℤ/3-invariant codes (exact law Index ≡ T_h·A₁(P)² mod 72), but at n = 72 there are codes with T_h = 0 and Index ≢ 0 mod 72 (`codes/q8z3_len72_T0.txt`).
- **k ≡ 0 mod 24 answered** (notes §10, Thm 10.1): a length-72 seed (`codes/q8z3_seed72.U.txt`, R_σ = 24, R_σ̄(D) = 0 for σ = h-triples 0, 1) gives a Q₈ × ℤ/3-equivariant chain with Index 24, T_h = 0 at every k ≡ 0 mod 12 (codes to n = 288, `mainq_q8z3_chain24.py`); V//G has index 1 for 24 | k. **So the Main Question is answered for every k** (Cor 10.2), modulo GJF's orbifold/anomaly theorems and [I]. Thm 8.1 has two proofs: via the coprime-gauging lemma (§8.2), and directly via the twisted sector (§8.4).
- **Coprime-gauging step of Thm 8.1 checked** (notes §8.2, `mainq_q8_gauging.py`): correct. Lemmas A–F. Its only non-elementary input is the coprime-gauging lemma (Naidu Thm 4.9, Uribe Thm 3.7; Tachikawa §2.4; JF Prop 2.2.1/2.3.1, §2.4). That lemma is a theorem for fusion categories and follows from known results for bosonic VOAs (Γ solvable: Carnahan–Miyamoto). It reaches the super case via the bosonic shadow.
  - Closed gap: the 3-primary part of the anomaly of Ŵ ⋊ Q₈ vanishes (transfer, and Ŵ is non-anomalous).
  - GJF Ex 4.4 applied directly to V_{Λ(C)} confirms 3k·a on all cyclic subgroups. The order-2 class 4a is invisible to any cyclic-by-cyclic check (it needs all of Q₈, e.g. S³/Q₈).
- **(−1)-twisted sector computed directly** (notes §8.3, `mainq_q8_twisted.py`).
  - V_{−1} = S[θ] ⊗ T, with T the spinor module of the frame zero modes Cl(n). So with its projective Q₈-action it is independent of C (Lemma 8.3), and T ≅ (H ⊕ 2ψ)^{⊗3k}.
  - Normalise the lifts of J, K, JK modularly (chain S T² S applied to Z(1,J) = η(2τ)^{6k}/η(4τ)^{6k}). This gives Ĵ K̂ = μ (JK)^ with μ = e^{−2πik/8} = exp(2πi·3k·5/8), the S³/Q₈ eta value.
  - μ = −1 at k ≡ 4 mod 8 proves the anomaly 4a directly, without Step 1.
- **Non-anomaly for 8 | k proved directly** (notes §8.4, `mainq_q8_nonanomaly.py`).
  - Free fermions realise all 32 classes of rSH³(Q₈) (the layer bound), so the classes with zero cyclic restrictions are {0, κ}.
  - The anomaly of V_{Λ(C)} has Majorana layer 0 and zero cyclic restrictions for 4 | k, so it lies in {0, κ}; μ = −1 gives κ at k ≡ 4 mod 8.
  - For 8 | k: α_C = α_{C⊕C′} − α_{C′} = κ − κ = 0, with any Q₈-code C′ of k′ ≡ 4 mod 8.
  - With tetracode sums (Step 2) this reproves Thm 8.1 for all k without the gauging lemma.
- **The facts behind μ proved** (notes §8.5, `mainq_q8_orbifold_character.py`).
  - Modular covariance: three exact eta identities. For τ′ = τ/(1−2τ) the multipliers of γ₁, γ₂ are both e^{−πi/6}, so N = (√2e^{2πi/48})^{n/2}.
  - Trivial phases: for 4 | k a would-be orbifold V//Q₈ has S-invariant NS character iff ψ(J)+ψ(K)+ψ(JK) = 3e^{2πik/8}. So k ≡ 4 mod 8 is anomalous, using only standard theorems (GJF Thm 4.2, S-invariance of holomorphic SVOA characters, lattice twisted modules).
  - Remaining inputs of the direct proof: those, plus the rSH³ layer bound, additivity, and free-fermion eta values (only to count classes).
  - GJF numbering: Thm 3.1 (lift), Thm 4.2 (anomaly in extended supercohomology S̃H³), Ex 4.4 (Frame shapes).
- **Orbifold index proved for all groups used, incl. Q₈ and Q₈ × ℤ/3** (`notes/orbifold-index.md`, Theorem O, revised after a 3-lens review; `mainq_orbifold_index.py`).
  - Supersymmetry reduces Index(W) to Ramond ground states (Cor 1.3). Every g ∈ G ∖ {±1} has a fixed-point-free coordinate permutation, so an element of even order m has E_g = n/24 + n/(12m²) > c/24: no ground states (Lemmas 3.2–3.3).
  - Untwisted terms: even-order x fixes no maximal word; order-3 x gives ±ζT_h (ζ³ = 1 from the trivialisation; the order-3 lift is *not* unique, only conjugate). Order-3 sectors: modular covariance (DZ05), as in GJF. Evenness of ρ_g(x) is proved (Lemma 1.2).
  - The fermionic GJF Thm 4.2 is [T*]: only sketched in GJF. What is used is Hypothesis ORB (`notes/blueprint/orbifold-foundations.md` §5).
- **Tier A formalized in Lean** (2026-09-27, later): `GJF.Ex.tierA : Q8Z3.E72Hyp → ∀ k ≥ 1, MQcode k` (`lean/GJF/TierA.lean`; standard axioms, no `sorry`/`native_decide`). `MQcode k` = self-dual C of length 12k, Index 24, and the group data of [CS] §1.7 for m = gcd(k, 24) (J; ℤ/m ⊂ ℤ/12 with T_{g⁴} = 0; Q₈; Q₈ × ℤ/3 with T_h = 0). The only unchecked input is `E72Hyp` (R_σ(E₇₂) = 24, confirmed by three programs). Files: `SPerm`, `LocalMaps`, `Equivariant`, `Chain` (uniform equivariant chains), `ChainJ`, `ChainQ8`, `ChainZ12`, `ChainQ8Z3`, `Twined` ([CS] Lemma 2.3), `Eval` (verified bit-sliced evaluator with pruning, fixed-code certificates, chunk splitting), `SeedCert`; generated `Seed*Data`, `CertZ12*` from `ternary60/theory/lean_seed_data.py` (logs `lean_seed_data_*.log`). ≈ 3,650 hand-written lines.
  - Kernel limits found: `decide +kernel` costs ≈ 1–3 ms and ≈ 90 KB of kernel cache per leaf of a seed tree, so the 2¹⁸- and 2¹⁰·24²-leaf ℤ/12 sums are split into ≤ 4,500-leaf declarations (`Eval.fastT_split`); a single declaration was OOM-killed (15 GB). Use `decide +kernel`, not `decide`, for the length-72 checks (elaborator heartbeats).
- **Lean blueprint** (`notes/blueprint/`, 2026-09-27; start with its `README.md`): four files ([EQ] equivariant quadrupling, [CS] chains and seeds, [AN] anomalies, [OF] orbifold foundations), each with a `blueprint_*.py` check script. README has the dependency list D1–D14, the trusted base, and the size estimate:
  - Tier A (code level, E₇₂ value as hypothesis) ≈ 2,500–5,000 new lines (≈ 3,500);
  - Tier B (VOA facts as a hypothesis structure, everything elementary proved) + 4,000–9,000, total ≈ 9,500;
  - unconditional ≈ 10⁵–5·10⁵.
  - The only seed fact out of kernel reach is R_σ(E₇₂) = 24. It is now confirmed by independent programs: `sl2words` (Morita form, 5.8·10⁶ good planes), `rsigma_is` (information-set enumeration over 2³⁶ sign patterns, ≈ 1 min; `ternary60/src/bin/rsigma_is.rs`, reviewed) and a reviewer's `rsigma_mitm`; `mainq_e72_infoset.py`. The ℤ/12 seed sums (≤ 5.9·10⁵ candidates) need a verified bit-sliced evaluator. Lean's `Tfin` is not J-invariant and its refinement split is the canonical one; the chains need the transposed split ([MQ] §4 Conventions, corrected).
  - Generator files: use `jchain_len<n>.gens.txt` / `z12chain_len<n>.gens.txt` (`mainq_gens_files.py`); the old `.J.txt`/`.g.txt` have no separators and up to 888 parses.
- **Morita form** (notes §9.1): Q₈-invariant codes = F₃² ⊗ U, U Lagrangian in F₃^{2r}; maximal words are SL₂(F₃)-blocks with f₄ = φ∘ψ (ψ = abelianisation). `ternary60 sl2words` computes Index and orbit-block R_σ sign-exactly at n = 72 in seconds (`mainq_morita.py` wraps it; `rsys`).
- The Thm 5.9 chain codes themselves: n = 48 has the needed J; n = 36, 72 have 2-group automorphism groups (no order-3 symmetry).
- `mainq_automorphisms.py` needs nauty's `dreadnaut` (`scripts/build_nauty.sh`); everything else is stdlib Python + the Rust binary (new subcommands `words`, `rsigma`).
- **Review of 2026-09-28** (`paper/review-2026-09-28.md`): both halves of Conj 1.4 and the Main Question re-checked (hand re-derivation, fresh code `review_*.py`, Lean rebuilt in a fresh container). No mathematical error found; issues are presentation and draft/formal-proof consistency (its §4). Findings:
  - Simpler seeds (notes `main-question.md` §11): Golay with a Q₈ and a *mixed* block system (the three Q₈-orbits always give R = 72) seeds the Q₈-chain (gcd 4, 8; replaces the J-chain and the random length-24 seed); GJF's own k = 3 code with ℤ/6 = ⟨−h⟩ seeds gcd 3, 6; gcd 12 comes from the Q₈ × ℤ/3-chain with g = Jh. Only E₇₂ is still from our search.
  - R_σ(E) ≡ Index(E) mod 48 proved (notes §5.1(f‴)); a Dedekind-sum-free proof of the eta identity (iii) (notes §8.5); the reduction of the Main Question to k ≤ 24 by tensor products; a proposed two-paper structure (Conj 1.4 alone; the Main Question separately).
- **Paper I draft (2026-09-29): `paper/conj14.tex`** (+ .pdf, 15 pp.). One paper for all the combinatorics: Thm A (24 | Index, finite Poisson 2-design), Thm B (index 24 at every 12k), Thm C (codes with the symmetry GJF Thm 5.6 needs, from the simpler seeds Golay + Q₈ / E₃₆ + ℤ/6 / E₇₂ + Q₈ × ℤ/3; Construction 6.3 with transposed splits), Thm D (g⁴ = −1 ⇒ 48 | Index), complements (mod 48, 8 | #even, #odd), seed data in the appendix. §§6–8 can be split off if a shorter Paper I is wanted; Paper II would then be the VOA side only (anomaly of Q₈, Theorem O). Placeholders: authors, repository URL, companion paper [II].
  - `ternary60/theory/conj14_paper_check.py` (log beside it) checks every computable claim from the data *parsed from the .tex* and rebuilds all chains with a fresh implementation of Construction 6.3 (uses `rsigma_is` for the 2²⁴–2³⁶-pattern sums; `--fast` skips them).

## Next steps

1. **Citation search** for GJF (Google Scholar "Cited by" / INSPIRE, by hand in a browser: Scholar shows a CAPTCHA to the cloud session, and INSPIRE/Semantic Scholar are blocked). A web-search check on 2026-09-26 found no prior solution (notes §5.1(f‴)). Then consider contacting Johnson-Freyd (notes §5 item 4).
2. ~~An independent re-derivation of Lemma 5.8's local identities, and a sign-exact index check at n = 36~~ — done in `ternary60/theory/paper_check.py` (log beside it; notes §5.1(f‴) Status). The paper draft `paper/index24.tex` compiles cleanly and was checked line by line against the notes and GJF's source; the review is in `paper/review-2026-09-26.md`, and its wording edits are applied (author and repository placeholders remain). Still wanted: a reading by a second person.
3. Optional: the [C] in §5.1(d). (R_σ(E) ≡ Index(E) mod 48 is now proved: notes §5.1(f‴), 2026-09-28.)
3′. Papers: Paper I is drafted (`paper/conj14.tex`, supersedes `index24.tex` and the code half of `main-question.tex`); wanted: a second reader, the placeholders, and a decision whether §§6–8 stay in Paper I. Paper II (VOA side: Q₈ anomaly via the direct proof of notes §8.4–8.5, Theorem O, the orbifold statements) is not yet drafted; `paper/main-question.tex` and the review's issue list (§4) are its starting point.
4. **Lean formalization of the Main Question**: Tier A is done (above). Open: (a) certify R_σ(E₇₂) = 24 (a new seed with a cheap certificate, or `native_decide` on the information-set sum, whose soundness is `Eval.fastT_eq` + [CS] Lemma 2.5); (b) speed up the ℤ/12 certificates (they dominate `lake build`); (c) Tier B (VOA side as a hypothesis structure), `notes/blueprint/README.md` §4.
5. Main Question: all classes answered (notes §10). Still wanted: an independent reading of GJF's anomaly analysis (Thm 5.6, the ℤ/3 Frame-shape part); (the gauging lemma is no longer needed: notes §8.4); a literature check; optionally a proof of the n = 36 law (notes §9.3) and of "β ≥ 1 ⇒ 72 | Index".

## Conventions

- **Notes.** Markdown with unicode math and short bullets. Status labels: [P] proved here, [V] exact computation (cite the script), [C] conjecture, [H] heuristic, [T] cited theorem.
- **Scripts.** Every checkable claim gets a script in `ternary60/theory/` that writes a `.log` beside itself, is cited in the notes, and has a row in README's layout. Keep all code in the repo; session scratchpads get wiped.
- **Python.** Stdlib only (no numpy on the original machine). Shared helpers are in `existence_common.py`: f, span, rref, nbr, rand_iso, dsum, brute_index, rust_index, twisted. Hadamard helpers are in `existence_hadamard.py`; `S`, `double`, `refine`, `tetra_on` and `SIGMA0` are in `existence_refinement.py`.
- **Rust.** Fine to use for performance (the user said so). `cargo build --release` in `ternary60/`.
- **Research style.** Don't stop at a literature search. Attempt the construction, verify pieces by explicit computation, and separate [V] from [C].

## Lean / Mathlib (set up 2026-09-26)

- Project in `lean/` (Mathlib master, toolchain `leanprover/lean4:v4.35.0-rc3`). **`GJF/Divisibility.lean` formalizes the divisibility half** (route C): `GJF.index_dvd_24 : IsSelfDual C → 0 < n → 24 ∣ gjfIndex C`, standard axioms only, no `sorry`/`native_decide`. `GJF/Sanity.lean`: the tetracode is self-dual (non-vacuity). `GJF/Orthogonal.lean`: `IsSelfDual C ↔ (dotProductBilin).orthogonal C = C ↔ self-orthogonal ∧ 2·dim C = n`, and `index_dvd_24'` with Mathlib's orthogonal complement. `GJF/Existence.lean` formalizes the existence half (Thm 5.9): `GJF.Ex.exists_selfDual_index24`; `GJF.conjecture_1_4` states both halves (standard axioms only). Full `lake build` ≈ 30 min on 4 cores, dominated by the Tier A certificates `CertZ12*` (≈ 15 GB RAM machine: fine with the chunking). `GJF/Basic.lean`: the modular-forms facts (unused now). Check with `lake build` and `#print axioms GJF.index_dvd_24`.
- Lean pitfalls seen here: `simp`/`rw` fail to match `neg_neg` on `Fin n → ZMod 3` (use the term `neg_neg x`); `decide` handles all finite 𝔽₃ case checks, even ∀ over `Fin 4 → ZMod 3`; after `rw` of `n` in hypotheses mentioning `Fin n`, abstract the dependent term first (motive errors); Mathlib field lemmas on `ZMod 3` objects built from the ring instances fail instance synthesis (ring/field diamond), so pass instances with `@` (`Pi.Function.module`, `Module.Finite.pi`) and close by `Eq.trans`; keep `Word n` vs `Fin n → ZMod 3` consistent or `omega` sees different atoms; the Mathlib instance `instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent` hijacks `Neg (ZMod 3)` (simp/ring then fail): remove it with `attribute [-instance]`; nested sum/product coordinate types need `set_option synthInstance.maxSize 2048` for `DecidableEq`.
- A fresh container needs this setup, because `release.lean-lang.org` and `cache.mathlib.org` are blocked:
  1. `curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`
  2. Download `https://github.com/leanprover/lean4/releases/download/v4.35.0-rc3/lean-4.35.0-rc3-linux.tar.zst`, unpack it to `~/lean-toolchains/`, then run `elan toolchain link leanprover/lean4:v4.35.0-rc3 ~/lean-toolchains/lean-4.35.0-rc3-linux`.
  3. `cd lean && lake update` (≈ 10 min), then `MATHLIB_CACHE_GET_URL=https://lakecache.blob.core.windows.net/mathlib4-master lake exe cache get` (≈ 10 min), then `lake build`.
- If `lake update` moves Mathlib to a newer toolchain, repeat step 2 for the version in `lean/.lake/packages/mathlib/lean-toolchain`.
- Push to master (the user's instruction, 2026-09-26).

## Pitfalls learned the hard way

- **The Rust `index` sign is not meaningful.** It normalises a full-weight word to all-ones. Compare |I|, or use `brute_index` (n ≤ 24) or exact ℤ[ω] sums for sign-exact checks. Indices in 24ℤ are sign-independent mod 48.
- Guard script bodies with `if __name__ == "__main__":`, since modules import each other.
- Enumerating a length-48 code (3²⁴ words) in Python is infeasible. Test the lemma on small m, and use the Rust index on the doubled code instead.
- Sign convention: f(x) = ∏φ(x_i) with φ = (0, −1, +1), so Index = Σ_{x∈C} f(x) = GJF's #even − #odd. For the Hadamard H(E ⊕ E′) with pairs (i, m+i), a full-weight word from (u, u′) has sign (−1)^{wt u′}.
