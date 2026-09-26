"""Multi-step orbifold formula and ring transfer matrices (ternary-code-index.md §5.1, items (d)-(e)).

For isotropic W ⊂ F_3^n of dim r with W ∩ C = 0, C_W := (C ∩ W^⊥) + W is self-dual and
    Index(C_W) = 3^{-r} Σ_{w,v ∈ W} G_C(w, v),   G_C(y, v) = Σ_{x ∈ y+C} f(x) ω^{v·x}.
For C = ⊕ C_j, G factorises; for chain/ring-shaped W this is a transfer-matrix product.

Part V: formula vs Rust index for random chains (|.| compared: Rust's sign is a normalisation).
Part T: rings of tetracodes, 3-cells: power sums of the normalised transfer matrix (0 or 3·8^j).
Part S: exact characteristic polynomials of 1-dim-bond cells (code2, Golay): spectral radii.
Usage: python3 existence_orbifold.py [N_T] [N_S]
"""
import itertools, random, sys, cmath
from fractions import Fraction
from collections import Counter
from existence_common import *
from ternary import nullspace

W3 = [(1, 0), (0, 1), (-1, -1)]          # ω^k in Z[ω] as (p, q) = p + qω


def zmul(x, y):
    a, b = x; c, d = y
    return (a * c - b * d, a * d + b * c - b * d)


def zadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def G(Cw, y, v):
    tot = (0, 0)
    for c in Cw:
        x = add(y, c); fx = f(x)
        if fx:
            p, q = W3[dot(v, x)]
            tot = (tot[0] + fx * p, tot[1] + fx * q)
    return tot


PAIRS = [(a, b) for a in range(3) for b in range(3)]


def lin(a, z, b, y):
    return tuple((a * p + b * q) % 3 for p, q in zip(z, y))


def Mmat(Cw, z, y):
    return [[G(Cw, lin(a, z, a2, y), lin(b, z, b2, y)) for (a2, b2) in PAIRS] for (a, b) in PAIRS]


def endvec(Cw, y):
    return [G(Cw, tuple(a * t % 3 for t in y), tuple(b * t % 3 for t in y)) for (a, b) in PAIRS]


def vecmat(v, M):
    out = [(0, 0)] * len(M[0])
    for i, vi in enumerate(v):
        if vi != (0, 0):
            for j, m in enumerate(M[i]):
                out[j] = zadd(out[j], zmul(vi, m))
    return out


def matmul(A, B):
    return [vecmat(row, B) for row in A]


def powersums(M, K, norm=3):
    out, P = [], M
    for k in range(1, K + 1):
        t = (sum(P[i][i][0] for i in range(len(P))), sum(P[i][i][1] for i in range(len(P))))
        out.append((Fraction(t[0], norm ** k), Fraction(t[1], norm ** k)))
        P = matmul(P, M)
    return out


def rvec(m, rng, cond):
    while True:
        v = tuple(rng.randrange(3) for _ in range(m))
        if cond(v):
            return v


def part_V(rng):
    configs = [[GOLAY, TETRA, TETRA, TETRA, GOLAY], [GOLAY, CODE2], [CODE2, TETRA, TETRA, TETRA, GOLAY], [GOLAY, GOLAY, GOLAY]]
    ok = tot = 0
    for comps in configs:
        for _ in range(3):
            mats = [span(c, len(c[0])) for c in comps]
            s, ms = len(comps), [len(c[0]) for c in comps]
            ys, zs = [None] * s, [None] * s
            ys[0] = rvec(ms[0], rng, lambda v: not inspan(comps[0], v))
            for j in range(1, s):
                need = (-dot(ys[j - 1], ys[j - 1])) % 3
                zs[j] = rvec(ms[j], rng, lambda v: dot(v, v) == need)
                if j < s - 1:
                    ys[j] = rvec(ms[j], rng, lambda v: dot(v, zs[j]) == 0 and not inspan(comps[j], v))
            vec = endvec(mats[0], ys[0])
            for j in range(1, s - 1):
                vec = vecmat(vec, Mmat(mats[j], zs[j], ys[j]))
            t = (0, 0)
            for a, b in zip(vec, endvec(mats[-1], zs[-1])):
                t = zadd(t, zmul(a, b))
            assert t[1] == 0 and t[0] % 3 ** (s - 1) == 0
            formula = t[0] // 3 ** (s - 1)
            n = sum(ms); offs = [sum(ms[:j]) for j in range(s)]
            Wv = []
            for j in range(s - 1):
                w = [0] * n
                for i, a in enumerate(ys[j]): w[offs[j] + i] = a
                for i, a in enumerate(zs[j + 1]): w[offs[j + 1] + i] = a
                Wv.append(w)
            B = rref(dsum(comps))
            ker = nullspace([[dot(b, w) for b in B] for w in Wv], len(B))
            D = [[sum(c * b[t] for c, b in zip(k, B)) % 3 for t in range(n)] for k in ker]
            CW = rref(D + Wv)
            assert len(CW) == n // 2 and all(dot(a, b) == 0 for a in CW for b in CW)
            I = rust_index(CW)
            tot += 1; ok += abs(I) == abs(formula)
            print(f"V n={n}: formula {formula}, rust {I}")
    print(f"V formula = ±index on {ok}/{tot}")


def part_T(N, rng):
    T = span(TETRA, 4)
    V4 = list(itertools.product(range(3), repeat=4))
    pairs = [(z, y) for z in V4 for y in V4 if dot(z, y) == 0 and not inspan(TETRA, y)
             and not inspan(TETRA + [list(y)], z)]
    by = {}
    for p in pairs:
        by.setdefault(dot(p[0], p[0]), []).append(p)
    Ms = {}
    cnt = Counter()
    for _ in range(N):
        while True:
            cell = [rng.choice(pairs)]
            for j in range(2):
                cell.append(rng.choice(by[(-dot(cell[-1][1], cell[-1][1])) % 3]))
            if (dot(cell[-1][1], cell[-1][1]) + dot(cell[0][0], cell[0][0])) % 3 == 0:
                break
        P = None
        for c in cell:
            if c not in Ms:
                Ms[c] = Mmat(T, *c)
            P = Ms[c] if P is None else matmul(P, Ms[c])
        ps = powersums(P, 3, 27)
        cnt[tuple(str(p[0]) + ("" if p[1] == 0 else f"+{p[1]}w") for p in ps)] += 1
    print("T 3-tetracode cells, (p1,p2,p3) of transfer/27:", dict(cnt))


def charpoly(p):
    e = [Fraction(1)]
    for k in range(1, len(p) + 1):
        e.append(sum((-1) ** (i - 1) * e[k - i] * p[i - 1] for i in range(1, k + 1)) / k)
    return e


def roots(co):
    n = len(co) - 1
    r = [(0.4 + 0.9j) ** k for k in range(n)]
    for _ in range(500):
        new = []
        for i, ri in enumerate(r):
            num = sum(c * ri ** (n - k) for k, c in enumerate(co))
            den = 1
            for j, rj in enumerate(r):
                if j != i:
                    den *= ri - rj
            new.append(ri - num / den if den else ri + 1e-9)
        r = new
    return r


def part_S(N, rng):
    for name, X in [("code2", CODE2), ("Golay", GOLAY)]:
        Xw = span(X, 12)
        cnt = Counter(); kron = 0
        for _ in range(N):
            y = rvec(12, rng, lambda v: not inspan(X, v))
            z = rvec(12, rng, lambda v: dot(v, y) == 0 and (dot(v, v) + dot(y, y)) % 3 == 0)
            ps = powersums(Mmat(Xw, z, y), 9)
            assert all(p[1] == 0 and p[0].denominator == 1 for p in ps)
            e = charpoly([int(p[0]) for p in ps])
            co = [float((-1) ** k * e[k]) for k in range(10)]
            while len(co) > 1 and abs(co[-1]) < 1e-9:
                co.pop()
            rs = roots(co)
            rad = max([abs(x) for x in rs], default=0.0)
            cnt[round(rad, 2)] += 1
            kron += bool(rs) and rad < 1 + 1e-6
        print(f"S {name} cells: spectral radius -> count {dict(sorted(cnt.items()))}; Kronecker cells: {kron}")


if __name__ == "__main__":
    rng = random.Random(5)
    part_V(rng)
    part_T(int(sys.argv[1]) if len(sys.argv) > 1 else 300, rng)
    part_S(int(sys.argv[2]) if len(sys.argv) > 2 else 150, rng)
