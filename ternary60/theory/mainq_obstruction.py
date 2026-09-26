"""Obstruction: an automorphism g with g⁴ = −1 forces 48 | Index (notes/main-question.md §5, Theorem 5.1).

Setting. J ∈ Aut(C) with J² = −1 makes C an F_9-space (J = multiplication by i) and the ternary form
the real part of a Hermitian form. For a J-invariant D ⊂ C of codimension 2, D^⊥/D is a Hermitian
hyperbolic plane over F_9 with exactly 4 isotropic F_9-lines; they give the 4 J-invariant self-dual
codes C_1..C_4 ⊇ D, and Poisson summation (f̂ = 3^{n/2} f) gives the four-code identity

        Index(C_1) + Index(C_2) + Index(C_3) + Index(C_4) = 12·F(D).                          (◇)

If moreover g ∈ Aut(C) has g⁴ = −1 (so g² = J), D is g-invariant and C, C' are the two g-invariant
lines, then g swaps the other two, 8 | F(D), and (◇) gives Index(C) + Index(C') ≡ 0 mod 48.

Part 1: (◇) on random J-invariant configurations (n = 24, sign-exact enumeration).
Part 2: the g-neighbour congruence: F(C) + F(C') ≡ 0 mod 48, F(C_3) = F(C_4), 8 | F(D) (n = 24, 48).
Part 3: random g-invariant self-dual codes (g⁴ = −1): |Index| mod 48 at n = 24, 36, 48, 60, 72
        (the prediction is 0; for k odd Index = 0 exactly).
"""
import itertools, os, random, sys
from collections import Counter
from existence_common import dot, rref, rust_index, HERE
from mainq_common import mono_apply, mono_pow, mono_neg, mono_order, is_aut, rust_R


def signed_cycles(n, L):
    """The standard monomial map with L-cycles e_{Lj+i} ↦ e_{Lj+i+1}, e_{Lj+L−1} ↦ −e_{Lj}."""
    p = [0] * n; s = [1] * n
    for j in range(n // L):
        for i in range(L):
            p[L * j + i] = L * j + (i + 1) % L
        s[L * j + L - 1] = -1
    return (tuple(p), tuple(s))


def nullspace(rows, n):
    if not rows:
        return [[1 if i == j else 0 for i in range(n)] for j in range(n)]
    R = rref(rows); piv = [next(j for j in range(n) if r[j]) for r in R]
    out = []
    for fj in [j for j in range(n) if j not in piv]:
        v = [0] * n; v[fj] = 1
        for r, pj in zip(R, piv):
            v[pj] = (-r[fj]) % 3
        out.append(v)
    return out


def rand_invariant_code(g, n, rng, order):
    """Random g-invariant self-dual code: grow a self-orthogonal g-invariant code by g-orbits of
    random vectors of its dual."""
    S = []
    while len(S) < n // 2:
        perp = nullspace(S, n); ok = False
        for _ in range(400):
            c = [rng.randrange(3) for _ in perp]
            w = [sum(a * b[i] for a, b in zip(c, perp)) % 3 for i in range(n)]
            if not any(w):
                continue
            orb = [list(mono_apply(mono_pow(g, i), w)) for i in range(order)]
            if all(dot(w, o) == 0 for o in orb):
                T = rref(S + orb)
                if len(T) > len(S):
                    S = T; ok = True; break
        if not ok:
            return None
    return S


def lagrangians_over(D, n):
    """All self-dual codes containing D (dim n/2 − 2): D + L for the totally isotropic 2-planes L of
    D^⊥/D. Returns a list of generator lists."""
    Dp = nullspace(D, n)
    comp = []
    for v in Dp:
        if len(rref(D + comp + [v])) > len(rref(D + comp)):
            comp.append(v)
    assert len(comp) == 4
    vecs = {}
    for c in itertools.product(range(3), repeat=4):
        if any(c):
            w = tuple(sum(a * b[i] for a, b in zip(c, comp)) % 3 for i in range(n))
            vecs[c] = w
    iso = [c for c, w in vecs.items() if dot(w, w) == 0]
    planes = set()
    for a, b in itertools.combinations(iso, 2):
        if dot(vecs[a], vecs[b]) == 0:
            pl = frozenset(tuple((x * u + y * v) % 3 for u, v in zip(a, b)) for x in range(3) for y in range(3))
            if len(pl) == 9:
                planes.add(pl)
    out = []
    for pl in planes:
        gens = [list(vecs[c]) for c in pl if any(c)]
        out.append(rref(D + gens))
    return out


def part1(rng, trials):
    n = 24
    J = signed_cycles(n, 2)
    ok = tot = 0
    for _ in range(trials):
        C = rand_invariant_code(J, n, rng, 4)
        if C is None:
            continue
        # random J-invariant D of codimension 2: C ∩ <v, Jv>^⊥ for random v with that intersection of codim 2
        while True:
            v = [rng.randrange(3) for _ in range(n)]
            W = rref([v, list(mono_apply(J, v))])
            D = rref(_intersect(C, nullspace(W, n), n))
            if len(D) == n // 2 - 2:
                break
        Ls = lagrangians_over(D, n)
        Jinv = [L for L in Ls if is_aut(J, L, n)]
        FD = rust_R(D, [], "obsD")
        s = sum(rust_R(L, [], "obsL") for L in Jinv)
        tot += 1; ok += (len(Ls) == 8 and len(Jinv) == 4 and s == 12 * FD)
    print(f"1 (◇) on {ok}/{tot} random J-invariant configurations at n = 24 "
          f"(8 Lagrangians over D, exactly 4 J-invariant, Σ Index = 12·F(D), sign-exact)", flush=True)


def _intersect(C, U, n):
    """Basis of span(C) ∩ span(U)."""
    Cb = rref(C); Ub = rref(U)
    # x ∈ C ∩ U  <=>  x ∈ C and x ⊥ U^⊥
    Uperp = nullspace(Ub, n)
    # solve for coefficients c with Σ c_j C_j ⊥ Uperp
    M = [[dot(r, u) for r in Cb] for u in Uperp]
    ker = nullspace(M, len(Cb)) if any(any(r) for r in M) else [[1 if i == j else 0 for i in range(len(Cb))] for j in range(len(Cb))]
    return [[sum(c[j] * Cb[j][i] for j in range(len(Cb))) % 3 for i in range(n)] for c in ker]


def part2(rng, trials):
    for n in (24, 48):
        g = signed_cycles(n, 4); J = mono_pow(g, 2)
        k = n // 12
        res = Counter()
        for _ in range(trials):
            C = rand_invariant_code(g, n, rng, 8)
            if C is None:
                continue
            # g-invariant D of codim 2: C ∩ W^⊥ with W = <v, gv, g²v, g³v> ∩ (an eigen-component), obtained
            # as the g-orbit span of a vector v with (g² + g + 2)v = 0 or (g² + 2g + 2)v = 0 (a 2-dim g-module)
            while True:
                v = [rng.randrange(3) for _ in range(n)]
                gv = mono_apply(g, v); g2v = mono_apply(g, gv)
                comp = rng.choice(((2, 1, 1), (2, 2, 1)))           # p(g) = g² + a g + 2 with a = 1 or 2
                w = [(comp[0] * x + comp[1] * y + comp[2] * z) % 3 for x, y, z in zip(v, gv, g2v)]   # p(g)v: in the other factor
                # the other factor's element: W = <w, gw>
                W = rref([w, list(mono_apply(g, w))])
                if len(W) != 2:
                    continue
                D = rref(_intersect(C, nullspace(W, n), n))
                if len(D) == n // 2 - 2:
                    break
            Ls = lagrangians_over(D, n)
            ginv = [L for L in Ls if is_aut(g, L, n)]
            Jinv = [L for L in Ls if is_aut(J, L, n) and not is_aut(g, L, n)]
            FD = rust_R(D, [], "obsD") if n <= 24 else None
            if n <= 24:
                Fg = [rust_R(L, [], "obsL") for L in ginv]
                Fo = [rust_R(L, [], "obsL") for L in Jinv]
                res[(len(ginv), len(Jinv), sum(Fg) % 48, Fo[0] == Fo[1] if len(Fo) == 2 else None, FD % 8)] += 1
            else:
                Ig = [abs(rust_index(L, "obsI")) for L in ginv]
                res[(len(ginv), len(Jinv), tuple(sorted(x % 48 for x in Ig)))] += 1
        print(f"2 n = {n} (k = {k}): g-neighbour configurations {dict(res)} "
              + ("[key: (#g-inv, #other J-inv, (F(C)+F(C')) mod 48, F(C3) = F(C4), F(D) mod 8)]" if n <= 24 else
                 "[key: (#g-inv, #other J-inv, |Index| mod 48 of the two g-invariant codes)]"), flush=True)


def part3(rng, per_n):
    for n, N in per_n:
        g = signed_cycles(n, 4)
        assert mono_order(g) == 8 and mono_pow(g, 4) == mono_neg(n)
        cnt = Counter()
        for _ in range(N):
            C = rand_invariant_code(g, n, rng, 8)
            if C is None:
                continue
            I = abs(rust_index(C, "obs3"))
            cnt[I % 48 if I else "0 exactly"] += 1
        print(f"3 n = {n} (k = {n // 12}): random g-invariant codes, |Index| mod 48: {dict(cnt)}", flush=True)


if __name__ == "__main__":
    import io, contextlib
    quick = "--quick" in sys.argv
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        rng = random.Random(2026)
        part1(rng, 10 if quick else 40)
        part2(rng, 10 if quick else 30)
        part3(rng, [(24, 50), (36, 20), (48, 20)] if quick else [(24, 200), (36, 60), (48, 60), (60, 30), (72, 8)])
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
