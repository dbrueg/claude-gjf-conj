"""Hadamard gluing (ternary-code-index.md §5.1, item (f)).

H_π: (x_i, x_j) -> (x_i + x_j, x_i − x_j) on every pair of a perfect matching π is an
anti-isometry of F_3^n, so it maps self-dual codes to self-dual codes. Full-weight words of
H_π(C) <-> words of C with exactly one nonzero entry on each pair.

Part A: Index(H(Golay ⊕ σT^3)) = −24 + 8h, h = #(weight-6 supports of σT^3 that are hexads).
Part B: Index(H(E ⊕ σT^{m/4})) = Σ_{c∈E} Π_blocks λ(|supp c ∩ b|), λ = (0,−2,0,0,1), at n = 48.
Part C: doubling E_2 -> H(E_2 ⊕ σT^6): distribution of Index (n = 48).
Part D: Hadamard rings of Golays (6+6 split of each Golay): traces of the 64×64 transfer matrix.
"""
import itertools, random, sys
from collections import Counter
from existence_common import *


def hadamard(B, pairs):
    out = []
    for r in B:
        v = list(r)
        for i, j in pairs:
            v[i], v[j] = (r[i] + r[j]) % 3, (r[i] - r[j]) % 3
        out.append(v)
    return rref(out)


def tetra_perm(m, perm):
    B = dsum([TETRA] * (m // 4))
    return [[r[perm.index(i)] for i in range(m)] for r in B]


G = span(GOLAY, 12)
HEX = {frozenset(i for i in range(12) if x[i]) for x in G if sum(1 for a in x if a) == 6}
LAM = {0: 0, 1: -2, 2: 0, 3: 0, 4: 1}


def part_A(N, rng):
    cnt = Counter(); ok = 0
    for t in range(N):
        perm = list(range(12)); rng.shuffle(perm)
        T3 = tetra_perm(12, perm)
        h = len({frozenset(i for i in range(12) if x[i]) for x in span(T3, 12)
                 if sum(1 for a in x if a) == 6} & HEX)
        HB = hadamard(dsum([GOLAY, T3]), [(i, 12 + i) for i in range(12)])
        assert len(HB) == 12 and all(dot(a, b) == 0 for a in HB for b in HB)
        I = brute_index(HB, 24) if t < 4 else rust_index(HB)
        ok += (I == -24 + 8 * h) if t < 4 else (abs(I) == abs(-24 + 8 * h))
        cnt[(h, I)] += 1
    print(f"A (h, Index) -> count {dict(cnt)};  formula −24+8h holds {ok}/{N} (first 4 sign-exact by brute force)")


def make_E2(rng):
    while True:
        perm = list(range(12)); rng.shuffle(perm)
        E2 = hadamard(dsum([GOLAY, tetra_perm(12, perm)]), [(i, 12 + i) for i in range(12)])
        if abs(rust_index(E2)) == 24:
            return E2


def part_B(N, rng):
    E2 = make_E2(rng); Ew = span(E2, 24)
    for _ in range(N):
        p = list(range(24)); rng.shuffle(p)
        blocks = [[j for j in range(24) if p.index(j) // 4 == b] for b in range(6)]
        lam = 0
        for c in Ew:
            prod = 1
            for bl in blocks:
                prod *= LAM[sum(1 for j in bl if c[j])]
                if not prod:
                    break
            lam += prod
        I = rust_index(hadamard(dsum([E2, tetra_perm(24, p)]), [(i, 24 + i) for i in range(24)]))
        print(f"B lambda-formula {lam}, rust index {I}, |equal| {abs(lam) == abs(I)}")


def part_C(N, rng):
    E2 = make_E2(rng)
    cnt = Counter()
    for _ in range(N):
        p = list(range(24)); rng.shuffle(p)
        cnt[rust_index(hadamard(dsum([E2, tetra_perm(24, p)]), [(i, 24 + i) for i in range(24)]))] += 1
    print(f"C n=48 doubling: {N} samples, all Index ≡ 24 mod 48: {all(k % 48 == 24 for k in cnt)}, "
          f"P(|I|=24) = {(cnt[24] + cnt[-24]) / N:.3f}, max |I| = {max(abs(k) for k in cnt)}")


def part_D(N, rng):
    Nsupp = Counter(frozenset(i for i in range(12) if x[i]) for x in G)
    S = list(itertools.product((0, 1), repeat=6))
    res = Counter()
    for _ in range(N):
        L = list(rng.choice(sorted(HEX, key=sorted))) if rng.random() < .5 else rng.sample(range(12), 6)
        R = [i for i in range(12) if i not in L]; rng.shuffle(L); rng.shuffle(R)
        M = [[Nsupp.get(frozenset([L[i] for i in range(6) if s[i] == 0] + [R[i] for i in range(6) if t[i]]), 0)
              * (-1) ** (6 - sum(t)) for t in S] for s in S]
        P, tr = M, []
        for _ in range(5):
            tr.append(sum(P[i][i] for i in range(64)))
            Bt = list(zip(*M)); P = [[sum(x * y for x, y in zip(r, c)) for c in Bt] for r in P]
        res[tuple(tr)] += 1
    small = min(res, key=lambda t: abs(t[-1]))
    print(f"D Hadamard Golay rings: {len(res)} distinct trace sequences; smallest |Tr M^5| sequence {small}")


if __name__ == "__main__":
    rng = random.Random(2)
    part_A(40, rng)
    part_B(3, rng)
    part_C(int(sys.argv[1]) if len(sys.argv) > 1 else 200, rng)
    part_D(100, rng)
