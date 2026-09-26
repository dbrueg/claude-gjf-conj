"""Coordinate connected sums (ternary-code-index.md §5.1, item (g)).

C_1 ⊙_φ C_2 along d-sets V_1, V_2 (φ an anti-isometry of F_3^d): delete V_i and match the deleted
values through φ. Index(C_1 ⊙ C_2) = Σ_q A_1(q) A_2(φ q), A(q) = Σ_{c: c|V = q, full off V} f(c|off V).
Chains of cells of length 12 + 2d give integer 3^d × 3^d transfer matrices T[q,q'] = B(φq, q').
Part A: A-vector of Golay on d = 1, 2, 3, 6 coordinates (gcd 12, 6, 3, 1).
Part B: d = 2, random length-16 cells: spectral radius of T (0 or ≥ 6 in all samples).
"""
import itertools, random, sys
from math import gcd
from functools import reduce
from collections import Counter
from existence_common import *
from ternary import random_self_dual
from existence_orbifold import charpoly, roots


def states(d):
    return list(itertools.product(range(3), repeat=d))


def Avec(Cw, V, n):
    idx = {s: i for i, s in enumerate(states(len(V)))}
    other = [i for i in range(n) if i not in V]
    A = [0] * 3 ** len(V)
    for c in Cw:
        fx = f([c[i] for i in other])
        if fx:
            A[idx[tuple(c[i] for i in V)]] += fx
    return A


def Bmat(Cw, Vin, Vout, n):
    S = states(len(Vin)); idx = {s: i for i, s in enumerate(S)}
    other = [i for i in range(n) if i not in Vin and i not in Vout]
    B = [[0] * len(S) for _ in S]
    for c in Cw:
        fx = f([c[i] for i in other])
        if fx:
            B[idx[tuple(c[i] for i in Vin)]][idx[tuple(c[i] for i in Vout)]] += fx
    return B


if __name__ == "__main__":
    Gw = span(GOLAY, 12)
    for d in (1, 2, 3, 6):
        A = Avec(Gw, list(range(d)), 12)
        print(f"A Golay, d={d}: gcd of A-values = {reduce(gcd, [abs(a) for a in A if a])}, "
              f"values {sorted(Counter(A).items())}")
    d, n = 2, 16
    S = states(d); idx = {s: i for i, s in enumerate(S)}
    perm = [idx[((s[0] + s[1]) % 3, (s[0] - s[1]) % 3)] for s in S]   # φ = Hadamard, φφ^T = −I
    rng = random.Random(1); cnt = Counter()
    for _ in range(int(sys.argv[1]) if len(sys.argv) > 1 else 300):
        B0, _ = random_self_dual(n, rng)
        Cw = span(B0, n)
        c = list(range(n)); rng.shuffle(c)
        B = Bmat(Cw, c[:d], c[d:2 * d], n)
        T = [B[perm[i]] for i in range(9)]
        P, p = T, []
        for _ in range(9):
            p.append(sum(P[i][i] for i in range(9)))
            Bt = list(zip(*T)); P = [[sum(x * y for x, y in zip(r, col)) for col in Bt] for r in P]
        e = charpoly(p)
        co = [float((-1) ** k * e[k]) for k in range(10)]
        while len(co) > 1 and abs(co[-1]) < 1e-9:
            co.pop()
        cnt[round(max([abs(x) for x in roots(co)], default=0.0), 2)] += 1
    print(f"B d=2 length-16 cells: spectral radius -> count {dict(sorted(cnt.items()))}")
