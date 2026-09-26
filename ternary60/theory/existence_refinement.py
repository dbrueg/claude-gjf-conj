"""Refinement lemma and index-24 codes at every length 12·2^j (ternary-code-index.md §5.1(f″), Thm 5.7).

S_σ(E) := Σ_{c∈E} Π_{b∈σ} λ(|supp c ∩ b|), λ = (0,−2,0,0,1);  Index(H(E ⊕ σT)) = S_σ(E)  (§5.1(f)).
Doubling: E' = H(E ⊕ σT), pairs (i, m+i).  Refinement σ' of σ: split each σ-block {a,b,c,d} into two
pairs {a,b},{c,d} and take the E'-blocks {a, m+a, b, m+b}, {c, m+c, d, m+d}.
Lemma 5.6: S_σ'(E') = S_σ(E) for every E, σ and refinement σ'.
Part 1: Lemma 5.6 on random self-dual E of length 12 (E' of length 24, exact enumeration).
Part 2: the explicit chain from Golay: E_1 (n=24, brute force), E_2 (n=48, Rust), random refinements.
Part 3: the h-values of all 5775 partitions of the Golay coordinates into three 4-blocks.
"""
import itertools, random
from collections import Counter
from existence_common import *
from existence_hadamard import hadamard, HEX
from ternary import random_self_dual

LAM = (0, -2, 0, 0, 1)
SIGMA0 = [[1, 2, 10, 11], [3, 4, 8, 9], [0, 5, 6, 7]]   # h = 0 for the GOLAY generator of existence_common


def S(Ew, blocks):
    tot = 0
    for c in Ew:
        p = 1
        for bl in blocks:
            p *= LAM[sum(1 for j in bl if c[j])]
            if not p:
                break
        tot += p
    return tot


def tetra_on(blocks, m):
    rows = []
    for a, b, c, d in blocks:
        r1 = [0] * m; r1[a] = r1[b] = r1[c] = 1
        r2 = [0] * m; r2[b] = 1; r2[c] = 2; r2[d] = 1
        rows += [r1, r2]
    return rows


def double(E, blocks, m):
    return hadamard(dsum([E, tetra_on(blocks, m)]), [(i, m + i) for i in range(m)])


def refine(blocks, m, rng):
    new = []
    for bl in blocks:
        b = list(bl); rng.shuffle(b)
        new += [[b[0], m + b[0], b[1], m + b[1]], [b[2], m + b[2], b[3], m + b[3]]]
    return new


def h_of(blocks):
    sup = set()
    for c in span(tetra_on(blocks, 12), 12):
        if sum(1 for a in c if a) == 6:
            sup.add(frozenset(i for i in range(12) if c[i]))
    return len(sup & HEX)


if __name__ == "__main__":
    rng = random.Random(4)
    ok = 0
    for _ in range(40):
        E, _ = random_self_dual(12, rng)
        p = list(range(12)); rng.shuffle(p); bl = [p[4 * b:4 * b + 4] for b in range(3)]
        ok += S(span(E, 12), bl) == S(span(double(E, bl, 12), 24), refine(bl, 12, rng))
    print(f"1 Lemma 5.6 S_σ'(E') = S_σ(E) on {ok}/40 random (E, σ, σ') at m = 12")
    G = span(GOLAY, 12)
    print(f"2 σ0 = {SIGMA0}: h = {h_of(SIGMA0)}, S_σ0(Golay) = {S(G, SIGMA0)}")
    E1 = double(GOLAY, SIGMA0, 12)
    print(f"2 E1 (n=24): Index = {brute_index(E1, 24)} (brute force, sign-exact)")
    for _ in range(5):
        s1 = refine(SIGMA0, 12, rng)
        E2 = double(E1, s1, 24)
        print(f"2 E2 (n=48), σ1 = {s1}: S_σ1(E1) = {S(span(E1, 24), s1)}, Rust Index = {rust_index(E2)}")
    pts = list(range(12)); parts = set()
    for A in itertools.combinations(pts, 4):
        rest = [x for x in pts if x not in A]
        for B in itertools.combinations(rest, 4):
            C = tuple(x for x in rest if x not in B)
            parts.add(frozenset([A, B, C]))
    hist = Counter(h_of([list(b) for b in P]) for P in parts)
    print(f"3 h over all {len(parts)} partitions: {dict(sorted(hist.items()))}  (S = −24 + 8h)")
