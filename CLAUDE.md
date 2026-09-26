# Working instructions: GJF Conjecture 1.4 project

Read `notes/ternary-code-index.md` first: §0 for the results, then §5.1 for the existence work. Every claim there carries a status label and, where checkable, a script. Build on the notes; don't restart from scratch.

## Goal

Prove or disprove the existence half of GJF Conj 1.4: a self-dual ternary code of index exactly ±24 at every length 12k. The divisibility half (24 | Index) is already proved (notes §1–2).

## Where things stand (end of 2026-09-26 session)

**Proved**, all in §5.1:
- **Theorem 5.7.** Index-24 codes exist at every length 12·2^j. The chain is E₀ = Golay with a partition σ₀ satisfying h ∈ {0, 6}, then E_{j+1} = H(E_j ⊕ σ_jT), where σ_{j+1} refines σ_j.
- **Lemma 5.6** (refinement invariance) is the engine of Theorem 5.7.
- **Theorem 5.4.** Doubling preserves Index mod 48.
- **Proposition 5.5.** The numbers of even and of odd maximal codewords are each ≡ 0 mod 8.
- **Lemmas 5.2 and 5.3.** Obstructions (72 | Index; 24·gcd | Index) that rule out many naive constructions.

**Covered lengths.** k ∈ {2^j} ∪ {3, 5}. **First open case: k = 6** (n = 72), then k = 7, 9, 10, 11, 12, ….

**Reduction.** For each odd k₀ ≥ 3 we need:
1. an index-24 code at length 12k₀, and
2. a *seed* (E, σ) at length 12k₀ with S_σ(E) = ±24.
A seed gives all lengths 12k₀·2^j with j ≥ 1. E must have Index ≡ 24 mod 48 (Theorem 5.4).

## Next steps, most promising first

1. **Seed at length 36.** This would give k = 6, 12, 24, …. Run `ternary60/theory/existence_seed_search.py`.
   - About 10 s per σ, estimated hit rate about 0.5%. Found seeds are appended to `ternary60/runs/seeds.txt`.
   - 160 random σ have been tried with no hit (all S ≡ 24 mod 48; standard deviation about 7,800; smallest |S| = 120).
   - Consider a local search over σ that swaps coordinates between blocks, instead of pure random sampling.
   - A hit is itself the Rust index of the n = 72 doubled code. All longer lengths 72·2^j then follow from Lemma 5.6, with no further computation (Rust cannot reach n ≥ 96 anyway).
2. **Seed at length 60.** This needs S_σ(E) for |E| = 60 without enumerating the n = 120 doubled code, e.g. a DP/meet-in-the-middle over blocks using Λ = ∏ λ(|c ∩ b|). Only words meeting every block in 1 or 4 points count.
3. **Direct index-24 codes at 12·(odd) for k₀ ≥ 7** (n = 84 is feasible in Rust at about 10 min per code). Alternatively, look for an operation that preserves S_σ and changes the length by an odd factor or by +12. §5.1(f″) records why Hadamard-type moves only double.
4. **Prove the [C] in §5.1(d):** 72 | Index(C_W) whenever dim W < the number of components.
5. **Literature check** before any claim: are Prop 5.5, Lemma 5.6 or Thm 5.7 known? Also consider contacting Johnson-Freyd (notes §5 item 4).

## Conventions

- **Notes.** Markdown with unicode math and short bullets. Status labels: [P] proved here, [V] exact computation (cite the script), [C] conjecture, [H] heuristic, [T] cited theorem.
- **Scripts.** Every checkable claim gets a script in `ternary60/theory/` that writes a `.log` beside itself, is cited in the notes, and has a row in README's layout. Keep all code in the repo; session scratchpads get wiped.
- **Python.** Stdlib only (no numpy on the original machine). Shared helpers are in `existence_common.py`: f, span, rref, nbr, rand_iso, dsum, brute_index, rust_index, twisted. Hadamard helpers are in `existence_hadamard.py`; `S`, `double`, `refine`, `tetra_on` and `SIGMA0` are in `existence_refinement.py`.
- **Rust.** Fine to use for performance (the user said so). `cargo build --release` in `ternary60/`.
- **Research style.** Don't stop at a literature search. Attempt the construction, verify pieces by explicit computation, and separate [V] from [C].

## Pitfalls learned the hard way

- **The Rust `index` sign is not meaningful.** It normalises a full-weight word to all-ones. Compare |I|, or use `brute_index` (n ≤ 24) or exact ℤ[ω] sums for sign-exact checks. Indices in 24ℤ are sign-independent mod 48.
- Guard script bodies with `if __name__ == "__main__":`, since modules import each other.
- Enumerating a length-48 code (3²⁴ words) in Python is infeasible. Test the lemma on small m, and use the Rust index on the doubled code instead.
- Sign convention: f(x) = ∏φ(x_i) with φ = (0, −1, +1), so Index = Σ_{x∈C} f(x) = GJF's #even − #odd. For the Hadamard H(E ⊕ E′) with pairs (i, m+i), a full-weight word from (u, u′) has sign (−1)^{wt u′}.
