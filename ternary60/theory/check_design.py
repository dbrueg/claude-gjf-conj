"""Verify the signed 2-design identity  sum_{eps in F} s(eps) eps_i eps_j = I * delta_ij
and the divisibility 24 | I on random self-dual ternary codes.

F = maximal (full-weight) codewords, s(eps) = (-1)^{#1s in eps} (GJF convention),
I = sum_F s = Index(C).
"""
import sys, random, itertools
from ternary import random_self_dual, zero_one_words, rref

GOLAY_GJF = [
    [1,0,0,0,0,0, 0, 1, 1, 1, 1, 1],
    [0,1,0,0,0,0,-1, 0, 1,-1,-1, 1],
    [0,0,1,0,0,0,-1, 1, 0, 1,-1,-1],
    [0,0,0,1,0,0,-1,-1, 1, 0, 1,-1],
    [0,0,0,0,1,0,-1,-1,-1, 1, 0, 1],
    [0,0,0,0,0,1,-1, 1,-1,-1, 1, 0],
]
CODE2_GJF = [
    [1,1,1,0,0,0,0,0,0,0,0,0],
    [0,0,0,1,1,1,0,0,0,0,0,0],
    [0,0,0,0,0,0,1,1,1,0,0,0],
    [0,0,0,0,0,0,0,0,0,1,1,1],
    [0,1,-1,0,1,-1,0,-1,1,0,0,0],
    [0,0,0,0,1,-1,0,1,-1,0,-1,1],
]


def all_codewords(B, n):
    for coeffs in itertools.product(range(3), repeat=len(B)):
        yield [sum(c * r[j] for c, r in zip(coeffs, B)) % 3 for j in range(n)]


def maximal_direct(B, n):
    """Maximal codewords as +-1 vectors, by brute force (small dim only)."""
    F = []
    for w in all_codewords(B, n):
        if all(w):
            F.append([1 if x == 1 else -1 for x in w])
    return F


def maximal_via_01(B, piv, n):
    """Requires all-ones in C. eps = 1 + 1_A, i.e. eps_i = -1 on A."""
    W = zero_one_words(B, piv, n)
    return [[-1 if x else 1 for x in w] for w in W]


def analyse(F, n):
    s = [(-1) ** sum(1 for x in e if x == 1) for e in F]
    I = sum(s)
    # design matrix
    bad = 0
    maxoff = 0
    for i in range(n):
        for j in range(n):
            v = sum(si * e[i] * e[j] for si, e in zip(s, F))
            target = I if i == j else 0
            if v != target:
                bad += 1
                maxoff = max(maxoff, abs(v - target))
    # triple-agreement identity: sum_{eps in F, eps_a=eps_b=eps_c} s = I/4, check a few triples
    trip_ok = True
    for (a, b, c) in [(0, 1, 2), (0, 5, n - 1), (3, 7, 11)]:
        v = sum(si for si, e in zip(s, F) if e[a] == e[b] == e[c])
        if 4 * v != I:
            trip_ok = False
    return I, len(F), bad, maxoff, trip_ok


def to3(rows):
    return [[x % 3 for x in r] for r in rows]


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    # named length-12 codes, brute force
    for name, G in [("Golay(GJF)", GOLAY_GJF), ("code2(GJF)", CODE2_GJF)]:
        B, piv = rref(to3(G), 12)
        F = maximal_direct(B, 12)
        print(name, "I=%d |F|=%d design_bad=%d triple_ok=%s" % (lambda r: (r[0], r[1], r[2], r[4]))(analyse(F, 12)))
    # random codes of length 24 not forced to contain 1: brute force
    for t in range(6):
        B, piv = random_self_dual(24, rng)
        F = maximal_direct(B, 24)
        I, nF, bad, mo, tok = analyse(F, 24) if F else (0, 0, 0, 0, True)
        print("n=24 random (no 1 forced) I=%d |F|=%d design_bad=%d triple_ok=%s 24|I:%s" % (I, nF, bad, tok, I % 24 == 0))
    # random codes containing 1, via 0/1 words
    for n, trials in [(24, 30), (36, 60)]:
        stats = {}
        for t in range(trials):
            B, piv = random_self_dual(n, rng, start=[[1] * n])
            F = maximal_via_01(B, piv, n)
            I, nF, bad, mo, tok = analyse(F, n)
            assert bad == 0 and tok, (n, I, nF, bad, mo)
            stats[I] = stats.get(I, 0) + 1
        print("n=%d: %d random codes containing 1; design identity held for all; index histogram %s; all 24|I: %s"
              % (n, trials, dict(sorted(stats.items())), all(I % 24 == 0 for I in stats)))
