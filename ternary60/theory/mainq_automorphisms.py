"""Monomial automorphism groups and GJF Thm 5.6 element types (notes/main-question.md §3).

Needs nauty's `dreadnaut` ($DREADNAUT or on $PATH; `scripts/build_nauty.sh` builds it) and the Rust
binary (`ternary60 words`). Every generator nauty returns is re-verified to preserve the code.

For each code: |Aut(C)| (nauty/Traces on the graph of ± coordinate vertices and codewords of weight ≤ w,
w minimal with the words spanning C), and counts of the element types that Theorem 5.6 uses:
  J  : order 4, J² = −1                       (m = 4)
  h  : order 3, cycle shape 3^{n/3}, T_h = 0  (m = 3; "h*" = same shape with T_h ≠ 0)
  g6 : order 6, g³ = −1, g² of shape 3^{n/3}  (m = 6)
  g8 : order 8, g⁴ = −1                       (m = 8; impossible by Thm 5.1 when Index = 24)
  g12: order 12, g⁶ = −1, g⁴ of shape 3^{n/3} (m = 12)
For the Thm 5.9 code of length 72 the words of weight ≤ 12 do not span (rank 34 of 36) and weight 15 is
too large for the graph, so we bound instead: Aut(C) ⊂ Aut(W₁₂), and Aut(W₁₂) is a 2-group.
"""
import os, sys, time
from collections import Counter
from existence_common import GOLAY, HERE
import mainq_common as M
from mainq_common import (aut_gens, closure, mono_order, mono_pow, mono_neg, cycle_type, read_code,
                          twined_count)

CODES = os.path.join(HERE, "..", "codes")


def classify(rows, n, gens, limit=250000):
    G = closure(gens, n, limit=limit)
    neg = mono_neg(n)
    cnt = Counter()
    for g in G:
        o = mono_order(g)
        if o == 4 and mono_pow(g, 2) == neg:
            cnt["J"] += 1
        elif o == 3 and set(cycle_type(g[0])) == {3}:
            cnt["h" if twined_count(rows, n, g) == 0 else "h*"] += 1
        elif o == 6 and mono_pow(g, 3) == neg and set(cycle_type(mono_pow(g, 2)[0])) == {3}:
            cnt["g6"] += 1
        elif o == 8 and mono_pow(g, 4) == neg:
            cnt["g8"] += 1
        elif o == 12 and mono_pow(g, 6) == neg and set(cycle_type(mono_pow(g, 4)[0])) == {3}:
            cnt["g12"] += 1
    return len(G), dict(cnt)


def report(name, rows, n, full=True):
    t = time.time()
    gens, gs, w = aut_gens(rows, n)
    order, types = classify(rows, n, gens) if full else (None, {})
    print(f"{name} (n = {n}, k = {n // 12}): weight ≤ {w} words span; |Aut| = {gs} (closure {order}); "
          f"Thm 5.6 element types {types}  [{time.time() - t:.0f}s]", flush=True)


def bound_72():
    rows = read_code(os.path.join(CODES, "quad_index24_len72.txt")); n = 72
    ws = M.rust_words(rows, n, 12)
    rank = M.bits_rank(ws)
    orig = M.is_aut
    M.is_aut = lambda g, r, nn: True          # generators of Aut(W12) need not preserve C
    try:
        gens, gs, _ = aut_gens(rows, n, wmax=12)
    finally:
        M.is_aut = orig
    import math
    pow2 = float(gs) == 2 ** round(math.log2(float(gs)))
    print(f"quad_index24_len72 (n = 72, k = 6): words of weight ≤ 12 have rank {rank} of 36; "
          f"|Aut(W₁₂)| = {gs}, a power of 2: {pow2}  ⇒ Aut(C) ⊂ Aut(W₁₂) is a 2-group, no element of order 3",
          flush=True)


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        report("Golay", GOLAY, 12)
        for n in (24, 36, 48, 60):
            report(f"quad_index24_len{n}", read_code(os.path.join(CODES, f"quad_index24_len{n}.txt")), n)
        bound_72()
        for n in (24, 36, 48, 60):
            report(f"gjf_ex57_len{n}", read_code(os.path.join(CODES, f"gjf_ex57_len{n}.txt")), n)
        for n in (24, 48):
            report(f"jchain_len{n}", read_code(os.path.join(CODES, f"jchain_len{n}.txt")), n)
        report("z12seed_len36_3", read_code(os.path.join(CODES, "z12seed_len36_3.txt")), 36)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
