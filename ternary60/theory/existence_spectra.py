"""Coset spectra F(u+C) and the one-coset state recursion (ternary-code-index.md §5.1).

Part A: multiset of F(u+C) = T_u(C) over u in F_3^n/C for tetracode, Golay, code2;
        twisted-twined sums G(y,v) of the tetracode (magnitudes 0 or sqrt 3).
Part B: state recursion (I, alpha) -> ((I p + 8 alpha beta)/3, (I p - alpha beta)/3) that
        appends a length-12 block (p, beta) and keeps only the coset c_0 + C' (Lemma 5.2 proof).
        Never produces |I| = 24: the 3-adic valuation of I/8 only grows.
"""
from collections import Counter
from existence_common import *


def coset_spectrum(B, n):
    C = span(B, n)
    return Counter(sum(f(add(u, c)) for c in C) for u in coset_reps(C, n))


print("A1 tetracode F(u+C):", dict(coset_spectrum(TETRA, 4)))
print("A2 Golay     F(u+C):", dict(coset_spectrum(GOLAY, 12)))
print("A3 code2     F(u+C):", dict(coset_spectrum(CODE2, 12)))
T = span(TETRA, 4)
reps = coset_reps(T, 4)
tab = Counter()
for y in reps:
    for v in reps:
        g = twisted(T, y, v)
        tab[round(abs(g) ** 2, 6)] += 1
print("A4 tetracode |G(y,v)|^2 over 81 pairs:", dict(tab))

BLOCKS = {"Golay": (24, [24, -12, 6, -3]), "code2": (0, [0, 9, -9])}
states = {(24, a) for a in [-12, 6, -3]} | {(0, a) for a in [9, -9]}
hit = False
for k in range(2, 10):
    nxt = set()
    for (I, al) in states:
        for a in {al, I}:
            for p, spec in BLOCKS.values():
                for b in spec:
                    if a == I and b == p:
                        continue
                    X, Y = I * p, a * b
                    I2, a2 = (X + 8 * Y) // 3, (X - Y) // 3
                    if abs(I2) < 10 ** 7:
                        nxt.add((I2, a2))
    states = nxt
    small = sorted({abs(I) for I, _ in states if I})[:4]
    hit |= any(abs(I) == 24 for I, _ in states)
    print(f"B n={12*k}: {len(states)} states, smallest nonzero |I|: {small}")
print("B |I|=24 ever reached:", hit)
