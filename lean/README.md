# Lean formalization of GJF Conjecture 1.4

Lean 4 + Mathlib proofs of both halves of Conjecture 1.4 of Gaiotto–Johnson-Freyd,
*Holomorphic SCFTs with small index* (arXiv:1811.00589):

```lean
theorem GJF.conjecture_1_4 :
    (∀ (n : ℕ) (C : Submodule (ZMod 3) (Fin n → ZMod 3)), IsSelfDual C → 0 < n →
      (24 : ℤ) ∣ gjfIndex C) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ C : Submodule (ZMod 3) (Fin (12 * k) → ZMod 3),
      IsSelfDual C ∧ gjfIndex C = 24)
```

`gjfIndex C` is GJF's definition taken literally: the number of even minus the number of odd
maximal codewords. A maximal codeword has no zero entry; its parity is the number of entries
equal to 1. `IsSelfDual C` says `x ∈ C ↔ x ⬝ᵥ c = 0 for all c ∈ C`. The hypothesis `0 < n` is
needed: at length 0 the empty word is an even maximal codeword, so the index is 1.

Everything uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
There is no `sorry` and no `native_decide`: finite checks are done by the kernel with `decide`.

## Files

| file | contents |
|---|---|
| `GJF/Divisibility.lean` | 24 \| Index (`GJF.index_dvd_24`). The signed 2-design `GJF.design` is proved by one Poisson summation over C with two marked coordinates. The factors 8 and 3 follow by counting arguments. This is route C of `../paper/divisibility.tex`. |
| `GJF/Existence.lean` | A code of index exactly 24 at every length 12k (`GJF.Ex.exists_selfDual_index24`), by partial Hadamard quadrupling from the ternary Golay code. This is Theorem 5.9 of the notes and `../paper/index24.tex`. Also contains `GJF.conjecture_1_4`. |
| `GJF/Orthogonal.lean` | `IsSelfDual C` is Mathlib's `C⊥ = C` for `dotProductBilin`, and is equivalent to "self-orthogonal and 2·dim C = n". Also gives the main theorem restated in that form (`GJF.index_dvd_24'`). |
| `GJF/Sanity.lean` | The tetracode is self-dual, so the hypotheses are satisfiable at positive length. |
| `GJF/Basic.lean` | A toolchain check: M₂(SL₂ℤ) = 0 and the Jacobi theta law. The proofs above don't use them. |

## Building

```bash
lake build                      # about 2 min; mostly kernel `decide` on the Golay code
```

To inspect the axioms, put this in a file that imports `GJF` and compile it with `lake env lean`:

```lean
#print axioms GJF.conjecture_1_4
```

The toolchain is `leanprover/lean4:v4.35.0-rc3`, with Mathlib `master` pinned in `lake-manifest.json`.
In the cloud container, `release.lean-lang.org` and `cache.mathlib.org` are blocked. The toolchain
then comes from the GitHub release tarball, and the Mathlib cache from
`MATHLIB_CACHE_GET_URL=https://lakecache.blob.core.windows.net/mathlib4-master lake exe cache get`.
The step-by-step setup is in `../CLAUDE.md`.

## Notes for maintainers

- A Mathlib instance, `instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent`, applies to `ZMod 3`.
  It takes over the search for `Neg (ZMod 3)`, and `simp` and `ring` then fail to match.
  `Existence.lean` removes it with `attribute [-instance]`.
- Mathlib's field lemmas, such as `finrank_orthogonal`, don't find instances for objects built
  with `ZMod 3`'s ring instances. `Orthogonal.lean` passes the instances explicitly.
- More pitfalls are listed in `../CLAUDE.md`. The mathematics is in `../notes/ternary-code-index.md`,
  §2 Step 1′ and §5.1(f‴).
