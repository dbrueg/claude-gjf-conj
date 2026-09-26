"""Lemma 5.2 check and random walks from decomposable codes (ternary-code-index.md §5.1).

Part L: one-step neighbours of E ⊕ B (E, B ∈ {Golay, code2}) along x = (x_E, x_B) with
        x_E ∉ E, x_B ∉ B: checks |Index(C')| = |I_E I_B + 8 F(x_E+E) F(x_B+B)|/3 and 72 | Index(C').
        (The Rust `index` normalises a full-weight word to all-ones, so its sign is not meaningful.)
Part W: walks of S steps from Golay ⊕ code2^m; per step, fraction with |I| = 24 and with 72 | I.
Usage: python3 existence_walks.py [N_lemma] [walk specs m:S:N ...]
"""
import random, sys
from collections import Counter
from existence_common import *


def part_L(N, rng):
    comps = {"Golay": GOLAY, "code2": CODE2}
    words = {k: span(v, 12) for k, v in comps.items()}
    idx = {k: sum(f(x) for x in words[k]) for k in comps}
    for a, b in [("Golay", "Golay"), ("Golay", "code2"), ("code2", "code2")]:
        B0 = rref(dsum([comps[a], comps[b]]))
        ok = div72 = tried = 0
        while tried < N:
            x = rand_iso(B0, 24, rng)
            xE, xB = tuple(x[:12]), tuple(x[12:])
            if inspan(comps[a], xE) or inspan(comps[b], xB):
                continue
            tried += 1
            TE = sum(f(add(xE, c)) for c in words[a])
            TB = sum(f(add(xB, c)) for c in words[b])
            I = rust_index(nbr(B0, x))
            ok += (3 * abs(I) == abs(idx[a] * idx[b] + 8 * TE * TB))
            div72 += (I % 72 == 0)
        print(f"L {a}+{b}: {tried} mixed neighbours, formula holds {ok}/{tried}, 72|I {div72}/{tried}")


def part_W(m, S, N, rng):
    B0 = rref(dsum([GOLAY] + [CODE2] * m))
    n = len(B0[0])
    res = [Counter() for _ in range(S)]
    for _ in range(N):
        B = B0
        for s in range(S):
            B = nbr(B, rand_iso(B, n, rng))
            res[s][rust_index(B)] += 1
    for s, c in enumerate(res):
        print(f"W n={n} (Golay+code2^{m}) step {s+1}: P(|I|=24)={(c[24]+c[-24])/N:.3f} "
              f"P(72|I)={sum(v for k, v in c.items() if k % 72 == 0)/N:.3f}")


if __name__ == "__main__":
    rng = random.Random(7)
    part_L(int(sys.argv[1]) if len(sys.argv) > 1 else 100, rng)
    for spec in (sys.argv[2:] or ["1:3:200", "2:4:150", "4:6:60"]):
        m, S, N = map(int, spec.split(":"))
        part_W(m, S, N, rng)
