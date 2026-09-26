# Working instructions: GJF Conjecture 1.4 project

Read `notes/ternary-code-index.md` first: §0 for the results, then §5.1 for the existence work. Every claim there carries a status label and, where checkable, a script. Build on the notes; don't restart from scratch.

## Goal

Prove or disprove the existence half of GJF Conj 1.4: a self-dual ternary code of index exactly ±24 at every length 12k. The divisibility half (24 | Index) is already proved (notes §1–2).

## Where things stand (2026-09-26, later session)

**Both halves of Conj 1.4 are now proved here** (pending literature check and independent reading).
- **Theorem 5.9** (§5.1(f‴)): an index-±24 code exists at every length 12k. The tool is *partial quadrupling* Q_σ: Hadamard-double a partial 4-block system σ (b blocks) twice against tetracodes and leave the other coordinates alone. This gives length m + 12b and Index = R_σ(E), a block-weighted index (Lemma 5.8). Refining one step-1 block gives a 2-block system with the same R, so (m, 2) → (m + 24, 2). Start from Golay with b = 1 (even k) or b = 2 (odd k).
- Verified by `ternary60/theory/existence_quadruple.py`: exact at n = 24, and Rust |Index| = 24 on explicit chains at n = 36, 48, 60, 72, 84 (log complete; codes in `ternary60/codes/quad_index24_len*.txt`).
- Independently re-verified by `ternary60/theory/paper_check.py` from the paper's definitions, with sign-exact Index = +24 at n = 24 and n = 36 (information-set enumeration).
- **Divisibility half now has a finite, elementary proof** (notes §2 Step 1′, `design_poisson.py`): Poisson on F₃ⁿ for g_ij gives G_ij(C) = −G_ij(C)/3, hence the signed 2-design (◆) and 24 | Index with no modular forms. Critically checked (`divisibility_check.py`); all variants written up in `paper/divisibility.tex`.
- Earlier results in §5.1 still stand: Thm 5.4 (mod 48), Prop 5.5, Lemma 5.6, Thm 5.7 (the s = 0 case of Lemma 5.8), Lemmas 5.2–5.3. The seed search (`existence_seed_search.py`) is no longer needed.

## Next steps

1. **Citation search** for GJF (Google Scholar "Cited by" / INSPIRE, by hand in a browser: Scholar shows a CAPTCHA to the cloud session, and INSPIRE/Semantic Scholar are blocked). A web-search check on 2026-09-26 found no prior solution (notes §5.1(f‴)). Then consider contacting Johnson-Freyd (notes §5 item 4).
2. ~~An independent re-derivation of Lemma 5.8's local identities, and a sign-exact index check at n = 36~~ — done in `ternary60/theory/paper_check.py` (log beside it; notes §5.1(f‴) Status). The paper draft `paper/index24.tex` compiles cleanly and was checked line by line against the notes and GJF's source; the review is in `paper/review-2026-09-26.md`, and its wording edits are applied (author and repository placeholders remain). Still wanted: a reading by a second person.
3. Optional: prove R_σ(E) ≡ Index(E) mod 48 (the Theorem 5.4 argument should carry over), and the [C] in §5.1(d).

## Conventions

- **Notes.** Markdown with unicode math and short bullets. Status labels: [P] proved here, [V] exact computation (cite the script), [C] conjecture, [H] heuristic, [T] cited theorem.
- **Scripts.** Every checkable claim gets a script in `ternary60/theory/` that writes a `.log` beside itself, is cited in the notes, and has a row in README's layout. Keep all code in the repo; session scratchpads get wiped.
- **Python.** Stdlib only (no numpy on the original machine). Shared helpers are in `existence_common.py`: f, span, rref, nbr, rand_iso, dsum, brute_index, rust_index, twisted. Hadamard helpers are in `existence_hadamard.py`; `S`, `double`, `refine`, `tetra_on` and `SIGMA0` are in `existence_refinement.py`.
- **Rust.** Fine to use for performance (the user said so). `cargo build --release` in `ternary60/`.
- **Research style.** Don't stop at a literature search. Attempt the construction, verify pieces by explicit computation, and separate [V] from [C].

## Lean / Mathlib (set up 2026-09-26)

- Project in `lean/` (Mathlib master, toolchain `leanprover/lean4:v4.35.0-rc3`). `GJF/Basic.lean` only type-checks the Mathlib facts Proof II needs (`levelOne_weight_two_rank_zero` = M₂(SL₂ℤ) = 0, `jacobiTheta₂_functional_equation`). Nothing is formalized yet; the size estimate is in notes §5 item 5 (divisibility via Step 1′ ≈ 600–1,200 lines).
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
