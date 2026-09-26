"""Utilities for self-dual ternary codes (stdlib only).

Vectors over F_3 are lists of ints in {0,1,2}.
"""
import random


def rref(rows, n):
    """Row-reduce a list of F_3 vectors; return (basis rows in RREF, pivot columns)."""
    M = [r[:] for r in rows]
    piv = []
    r = 0
    for c in range(n):
        p = None
        for i in range(r, len(M)):
            if M[i][c] % 3:
                p = i
                break
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 if M[r][c] == 1 else 2
        M[r] = [(x * inv) % 3 for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % 3 for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    return M[:r], piv


def nullspace(rows, n):
    """Basis of {x : r.x = 0 for all rows r} over F_3."""
    B, piv = rref(rows, n)
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        x = [0] * n
        x[f] = 1
        for i, pc in enumerate(piv):
            x[pc] = (-B[i][f]) % 3
        basis.append(x)
    return basis


def dot(a, b):
    return sum(x * y for x, y in zip(a, b)) % 3


def in_span(v, B, piv):
    w = v[:]
    for i, pc in enumerate(piv):
        if w[pc]:
            f = w[pc]
            w = [(a - f * b) % 3 for a, b in zip(w, B[i])]
    return not any(w)


def random_self_dual(n, rng, start=None):
    """Random self-dual ternary code of length n (n % 4 == 0) containing the rows of `start`."""
    rows = [r[:] for r in (start or [])]
    B, piv = rref(rows, n) if rows else ([], [])
    while len(B) < n // 2:
        N = nullspace(B, n) if B else [[1 if j == i else 0 for j in range(n)] for i in range(n)]
        for _ in range(10000):
            coeffs = [rng.randrange(3) for _ in N]
            v = [sum(c * r[j] for c, r in zip(coeffs, N)) % 3 for j in range(n)]
            if any(v) and dot(v, v) == 0 and not (B and in_span(v, B, piv)):
                break
        else:
            raise RuntimeError("failed to extend")
        B, piv = rref(B + [v], n)
    return B, piv


def systematic(B, piv, n):
    """Return (info, red, A) with codewords c: c[info]=u, c[red]=u*A (A: k x (n-k))."""
    red = [c for c in range(n) if c not in piv]
    A = [[row[c] for c in red] for row in B]
    return piv, red, A


def zero_one_words(B, piv, n):
    """All codewords with entries in {0,1}. Gray-code enumeration of u in {0,1}^k.

    Bit-sliced F_3 arithmetic on the redundancy part: (p, m) masks for value 1 and 2.
    """
    info, red, A = systematic(B, piv, n)
    k = len(info)
    rp, rm = [], []
    for row in A:
        p = m = 0
        for j, x in enumerate(row):
            if x == 1:
                p |= 1 << j
            elif x == 2:
                m |= 1 << j
        rp.append(p)
        rm.append(m)

    def add(p1, m1, p2, m2):
        s1 = (p1 & ~p2 & ~m2) | (p2 & ~p1 & ~m1) | (m1 & m2)
        s2 = (m1 & ~p2 & ~m2) | (m2 & ~p1 & ~m1) | (p1 & p2)
        return s1, s2

    out = []
    P = M = 0
    u = 0
    # u = 0 gives the zero word
    out.append((0, 0))
    for t in range(1, 1 << k):
        i = (t & -t).bit_length() - 1
        if (u >> i) & 1:  # remove row i: add -row = swap(p, m)
            P, M = add(P, M, rm[i], rp[i])
        else:
            P, M = add(P, M, rp[i], rm[i])
        u ^= 1 << i
        if M == 0:
            out.append((u, P))
    words = []
    for u, P in out:
        c = [0] * n
        for a, col in enumerate(info):
            if (u >> a) & 1:
                c[col] = 1
        for b, col in enumerate(red):
            if (P >> b) & 1:
                c[col] = 1
        words.append(c)
    return words


def cwe_point_index(words01, n):
    """Index via 0/1 words (requires all-ones in C): sum over A of (-1)^{|A|}."""
    return sum((-1) ** sum(w) for w in words01)
