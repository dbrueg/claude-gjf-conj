"""J-equivariant partial quadrupling from Golay: index-24 codes with J² = −1 at every even k
(notes/main-question.md §4.2, Theorem 4.3).

J is a signed fixed-point-free involution of the Golay coordinates with J² = −1 (one of the 792 such
elements of Aut(Golay) ≅ 2.M12; hard-coded here and re-verified). The block (0,1,2,3) is J-stable with
J-stable pairs {0,1}, {2,3}, and R_β(Golay) = 24. Each step applies the equivariant Q_σ of
mainq_equivariant.py and refines one J-stable step-1 block with a J-stable split, so σ'' is again two
J-stable blocks and k grows by 2 per step (by 1 at the first step).

Part 1: J ∈ Aut(Golay), J² = −1, cycle shape 2^6; R_β(Golay) for the J-stable block.
Part 2: the chain n = 24, 48, 72 (Index by brute force at 24, Rust at 48, 72), and n = 96, 120, 144
        (J-invariance, J² = −1, cycle shape 2^{n/2}, self-duality; Index = 24 by Lemma 5.8 of [I]).
        Codes saved to ../codes/jchain_len<n>.txt.
Part 3: GJF Thm 5.6 hypotheses at n = 48 (k = 4, m = 4): ord J = 4 = m and J^{m/2} = −1.
"""
import os, sys
from existence_common import GOLAY, brute_index, rust_index, dot, span, HERE
from existence_quadruple import R
from mainq_common import mono_mul, mono_neg, mono_order, cycle_type, is_aut, write_code, write_gens
from mainq_equivariant import quad_eq, choose_splits
from mainq_common import closure

J = ((1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10), (-1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1))
BLOCK = (0, 1, 2, 3)


def selfdual(B, n):
    return len(B) == n // 2 and all(dot(a, c) == 0 for a in B for c in B)


def main(maxn):
    print(f"1 J ∈ Aut(Golay): {is_aut(J, GOLAY, 12)}; J² = −1: {mono_mul(J, J) == mono_neg(12)}; "
          f"cycle shape {cycle_type(J[0])}; R_(0,1,2,3)(Golay) = {R(span(GOLAY, 12), [BLOCK], 12)}", flush=True)
    E, m, gens = GOLAY, 12, [J]
    blocks = choose_splits(closure(gens, m), [BLOCK])
    while True:
        rows, n, newb, gens2 = quad_eq(E, m, blocks, gens, refine=[0])
        Jn = gens2[0]
        ok = (selfdual(rows, n), is_aut(Jn, rows, n), mono_mul(Jn, Jn) == mono_neg(n),
              set(cycle_type(Jn[0])) == {2})
        line = (f"2 n = {n} (k = {n // 12}): self-dual {ok[0]}, J ∈ Aut {ok[1]}, J² = −1 {ok[2]}, "
                f"J fixed-point-free involution on coordinates {ok[3]}")
        if n <= 24:
            line += f"; Index = {brute_index(rows, n)} (brute force, sign-exact)"
        elif n <= 72:
            line += f"; |Index| = {abs(rust_index(rows, f'jchain{n}'))} (Rust)"
        else:
            line += "; Index = 24 by Lemma 5.8 of [I] (not computed)"
        print(line + f"; next σ'' = {newb}", flush=True)
        write_code(os.path.join(HERE, "..", "codes", f"jchain_len{n}.txt"), rows)
        write_code(os.path.join(HERE, "..", "codes", f"jchain_len{n}.J.txt"),
                   [list(Jn[0]), [1 if s == 1 else 2 for s in Jn[1]]])
        write_gens(os.path.join(HERE, "..", "codes", f"jchain_len{n}.gens.txt"), {"J": Jn})
        if n == 48:
            print(f"3 n = 48, k = 4, m = gcd(4,24) = 4: ord J = {mono_order(Jn)}, J^(m/2) = J² = −1: "
                  f"{mono_mul(Jn, Jn) == mono_neg(n)}  ⇒ GJF Thm 5.6 applies (index 6)", flush=True)
        if n >= maxn:
            break
        E, m, blocks, gens = rows, n, newb, gens2


if __name__ == "__main__":
    import io, contextlib
    maxn = int(sys.argv[1]) if len(sys.argv) > 1 else 144
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        main(maxn)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
