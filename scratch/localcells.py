"""EXPLORATORY (notes §5.1(e)): 1-dim-bond cells with low-weight ("local") bond vectors.

For y of weight 1–3 (up to automorphism) and z of weight ≤ 3 with z·y = 0 and z·z + y·y = 0, compute
M/3 for the cell (code2 or Golay) and estimate the spectral radius from high power sums. Every
cell is either nilpotent or has radius ≳ 12: local bonds barely orbifold.
"""
import itertools, cmath, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ternary60', 'theory'))
from existence_common import f, dot, add, span, GOLAY, CODE2, inspan
from collections import Counter
w = cmath.exp(2j * cmath.pi / 3)


def Mfast(Xw, z, y):
    hist = {}
    for a in range(3):
        for a2 in range(3):
            u = tuple((a * p + a2 * q) % 3 for p, q in zip(z, y))
            h = {}
            for c in Xw:
                x = add(u, c); fx = f(x)
                if fx:
                    k = (dot(x, z), dot(x, y)); h[k] = h.get(k, 0) + fx
            hist[(a, a2)] = h
    P = [(a, b) for a in range(3) for b in range(3)]
    return [[sum(m * w ** ((b * k[0] + b2 * k[1]) % 3) for k, m in hist[(a, a2)].items()) / 3
             for (a2, b2) in P] for (a, b) in P]


def mm(A, B):
    Bt = list(zip(*B)); return [[sum(x * y for x, y in zip(r, c)) for c in Bt] for r in A]


def ps(M, K=9):
    out = []; Q = M
    for k in range(K):
        out.append(sum(Q[i][i] for i in range(9))); Q = mm(Q, M)
    return out


def lowvecs(n, maxw):
    out = []
    for wgt in range(1, maxw + 1):
        for S in itertools.combinations(range(n), wgt):
            for vals in itertools.product((1, 2), repeat=wgt):
                v = [0] * n
                for i, s in zip(S, vals): v[i] = s
                out.append(tuple(v))
    return out


if __name__ == "__main__":
    for name, X in [("code2", CODE2), ("golay", GOLAY)]:
        Xw = span(X, 12); cnt = Counter()
        ys = [(1,) + (0,) * 11, (1, 1) + (0,) * 10, (1, 2) + (0,) * 10, (1, 1, 1) + (0,) * 9, (1, 1, 2) + (0,) * 9]
        for y in ys:
            if inspan(X, list(y)): continue
            for z in lowvecs(12, 3):
                if dot(z, y) or (dot(z, z) + dot(y, y)) % 3: continue
                s = ps(Mfast(Xw, z, y))
                cnt[round(max(abs(s[8]), abs(s[7]), abs(s[6])) ** (1 / 8), 2)] += 1
        print(name, "radius estimate -> count", sorted(cnt.items()), flush=True)
