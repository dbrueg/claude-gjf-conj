"""Invariant-theoretic check of the signed 2-design identity.

Two-point Jacobi polynomial of a self-dual ternary code C containing 1, w.r.t. T = {1,2}:
    J(x; y) = sum_{c in C} prod_{l not in T} x_{c_l} * y_{c_1} y_{c_2},
bidegree (n-2, 2).  J is invariant under the group G acting DIAGONALLY on x and y:
MacWilliams M (Jacobi MacWilliams identity), S_3 symbol permutations, diag(w,1,1)... .

Functionals (GJF sign convention, symbols ordered (0, 1, -1)):
    Index  I(J) = J(0,1,-1; 0,1,-1)
    Design D(J) = J(0,1,-1; 0,1, 1) = sum_{eps maximal} s(eps) eps_1 eps_2.
Claim checked here: D vanishes on the whole space of G-invariant J (while I does not),
i.e. the 2-design identity is forced by invariance alone at the Jacobi level.
Linear algebra mod large primes p = 1 mod 3 (two primes).
"""
import sys, random
from itertools import permutations


def monomials(n):
    out = []
    for a0 in range(n - 1):
        for a1 in range(n - 1 - a0):
            a2 = n - 2 - a0 - a1
            for b in [(2, 0, 0), (0, 2, 0), (0, 0, 2), (1, 1, 0), (1, 0, 1), (0, 1, 1)]:
                if all((a + bb) % 3 == 0 for a, bb in zip((a0, a1, a2), b)):
                    out.append(((a0, a1, a2), b))
    return out


def orbits(mons):
    seen = {}
    orbs = []
    S = list(permutations(range(3)))
    for (a, b) in mons:
        if (a, b) in seen:
            continue
        orb = set()
        for p in S:
            aa = tuple(a[p[i]] for i in range(3))
            bb = tuple(b[p[i]] for i in range(3))
            orb.add((aa, bb))
        for o in orb:
            seen[o] = len(orbs)
        orbs.append(sorted(orb))
    return orbs


def ev(orb, x, y, p):
    tot = 0
    for a, b in orb:
        t = 1
        for i in range(3):
            t = t * pow(x[i], a[i], p) % p * pow(y[i], b[i], p) % p
        tot += t
    return tot % p


def rank_mod(rows, p):
    M = [r[:] for r in rows]
    rk = 0
    ncol = len(M[0])
    for c in range(ncol):
        piv = None
        for i in range(rk, len(M)):
            if M[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], p - 2, p)
        M[rk] = [v * inv % p for v in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c]
                M[i] = [(u - f * v) % p for u, v in zip(M[i], M[rk])]
        rk += 1
    return rk


def check(n, p, rng):
    # cube root of unity mod p
    while True:
        g = rng.randrange(2, p - 1)
        w = pow(g, (p - 1) // 3, p)
        if w != 1:
            break
    w2 = w * w % p
    orbs = orbits(monomials(n))
    K = len(orbs)
    s = pow(3, n // 2, p)
    rows = []
    for _ in range(K + 15):
        x = [rng.randrange(p) for _ in range(3)]
        y = [rng.randrange(p) for _ in range(3)]
        Mx = [(x[0] + x[1] + x[2]) % p, (x[0] + w * x[1] + w2 * x[2]) % p, (x[0] + w2 * x[1] + w * x[2]) % p]
        My = [(y[0] + y[1] + y[2]) % p, (y[0] + w * y[1] + w2 * y[2]) % p, (y[0] + w2 * y[1] + w * y[2]) % p]
        rows.append([(ev(o, Mx, My, p) - s * ev(o, x, y, p)) % p for o in orbs])
    r = rank_mod(rows, p)
    Drow = [ev(o, [0, 1, p - 1], [0, 1, 1], p) for o in orbs]
    Irow = [ev(o, [0, 1, p - 1], [0, 1, p - 1], p) for o in orbs]
    rD = rank_mod(rows + [Drow], p)
    rI = rank_mod(rows + [Irow], p)
    return K, K - r, rD == r, rI == r


if __name__ == "__main__":
    rng = random.Random(3)
    ns = [int(a) for a in sys.argv[1:]] or [12, 24, 36, 48, 60]
    for n in ns:
        for p in [1000000009, 2**61 - 1]:
            K, dim, Dzero, Izero = check(n, p, rng)
            print("n=%d p=%d: #orbit unknowns=%d  dim(G-invariant 2-point Jacobi polys)=%d  "
                  "design functional D vanishes on all: %s   index functional I vanishes on all: %s"
                  % (n, p, K, dim, Dzero, Izero))
            sys.stdout.flush()
