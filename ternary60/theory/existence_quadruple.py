"""Partial quadrupling: +12b in length, and index 24 at every length 12k (ternary-code-index.md §5.1(f‴), Thm 5.9).

A *partial* 4-block system σ on [m] is a set of b disjoint 4-blocks; the other s = m − 4b coordinates
are singletons. Put
    R_σ(E) := Σ_{c∈E} Π_{i singleton} φ(c_i) · Π_{β∈σ} λ(|supp c ∩ β|),   φ = (0,−1,+1), λ = (0,−2,0,0,1).
(b = 0: R = Index; s = 0: R = S_σ of §5.1(f″).)
Q_σ(E): add a tetracode T₁ beside each σ-block and Hadamard-pair them (step 1), refine each doubled
block into two 4-blocks, add a tetracode T₂ beside each of those and Hadamard-pair again (step 2).
Singletons are untouched. The form on the image is ⟨e,e'⟩ + ⟨t₁,t₁'⟩ − ⟨t₂,t₂'⟩, so Q_σ(E) is self-dual;
its length is m + 12b and Index(Q_σ(E)) = R_σ(E) (Lemma 5.8).
Choosing any subset of the 2b step-1 blocks and refining each once more gives a partial system σ''
on Q_σ(E) with R_σ''(Q_σ(E)) = R_σ(E).

Part 1: Lemma 5.8 on random (E, σ) at m = 12, b = 1 (n = 24): self-duality, Index = R exactly (brute force),
        and R_σ'' = R_σ for all four choices of σ''.
Part 2: R_σ(Golay) over all partial systems with b = 1, 2, 3.
Part 3: the explicit chains (12,1) → 24 → 48 → 72 and (12,2) → 36 → 60 → 84, each step with b'' = 2;
        Index at each length (brute force at 24, Rust above); generators saved to ../codes/quad_index24_len<n>.txt.  --no84 skips n = 84 (≈ 20 min on 4 cores).
"""
import itertools, os, random, sys
from collections import Counter
from existence_common import *
from existence_hadamard import hadamard
from ternary import random_self_dual

LAM = (0, -2, 0, 0, 1)


def R(Ew, blocks, m):
    inb = {x for b in blocks for x in b}
    sing = [i for i in range(m) if i not in inb]
    tot = 0
    for c in Ew:
        p = 1
        for i in sing:
            p *= PHI[c[i]]
            if not p:
                break
        if not p:
            continue
        for b in blocks:
            p *= LAM[sum(1 for j in b if c[j])]
            if not p:
                break
        tot += p
    return tot


def quad(E, m, blocks, refine_mask):
    """Q_σ(E). blocks: list of 4-tuples (p,q,k,l), refined as {p,q},{k,l}. refine_mask: one bool per
    step-1 block (2b of them). Returns (generator rows, n, σ'' as list of 4-tuples)."""
    b = len(blocks); n = m + 12 * b
    T2base = m + 4 * b
    rows = [list(r) + [0] * (12 * b) for r in E]
    for j in range(b):                                   # T1 beside block j
        for t in TETRA:
            v = [0] * n
            for i in range(4):
                v[m + 4 * j + i] = t[i]
            rows.append(v)
    pairs1 = [(blocks[j][i], m + 4 * j + i) for j in range(b) for i in range(4)]
    mate = dict(pairs1)
    B1 = []                                              # step-1 blocks (refinement of σ)
    for p, q, k, l in blocks:
        B1 += [(p, mate[p], q, mate[q]), (k, mate[k], l, mate[l])]
    for r in range(2 * b):                               # T2 beside step-1 block r
        for t in TETRA:
            v = [0] * n
            for i in range(4):
                v[T2base + 4 * r + i] = t[i]
            rows.append(v)
    pairs2 = [(B1[r][i], T2base + 4 * r + i) for r in range(2 * b) for i in range(4)]
    mate2 = dict(pairs2)
    rows = hadamard(hadamard(rows, pairs1), pairs2)
    new = []
    for r, flag in enumerate(refine_mask):
        if flag:
            w, x, y, z = B1[r]
            new += [(w, mate2[w], x, mate2[x]), (y, mate2[y], z, mate2[z])]
    return rows, n, new


def selfdual(B, n):
    return len(B) == n // 2 and all(dot(a, c) == 0 for a in B for c in B)


def part1(N, rng):
    ok = okR = 0
    for _ in range(N):
        E, _ = random_self_dual(12, rng)
        p = list(range(12)); rng.shuffle(p)
        blocks = [tuple(p[:4])]
        r0 = R(span(E, 12), blocks, 12)
        allR = True
        for mask in itertools.product([False, True], repeat=2):
            Q, n, new = quad(E, 12, blocks, mask)
            assert selfdual(Q, n)
            QW = span(Q, n)
            if not any(mask):
                ok += (sum(f(x) for x in QW) == r0)
            allR &= R(QW, new, n) == r0
        okR += allR
    print(f"1 Index(Q_σ(E)) = R_σ(E) exactly on {ok}/{N}; R_σ''(Q_σ(E)) = R_σ(E) for all 4 σ'' on {okR}/{N} "
          f"(random E, m = 12, b = 1, n = 24, brute force)", flush=True)


def part2():
    G = span(GOLAY, 12)
    for b in (1, 2, 3):
        cnt = Counter()
        for combo in itertools.combinations(itertools.combinations(range(12), 4), b):
            if len({x for bl in combo for x in bl}) == 4 * b and list(combo) == sorted(combo):
                cnt[R(G, combo, 12)] += 1
        print(f"2 R_σ(Golay), b = {b}: {dict(sorted(cnt.items()))}", flush=True)


def first_block_system(E, m, b):
    W = span(E, m)
    for combo in itertools.combinations(itertools.combinations(range(m), 4), b):
        if len({x for bl in combo for x in bl}) == 4 * b and abs(R(W, combo, m)) == 24:
            return list(combo), R(W, combo, m)


def chain(E, m, blocks, steps, maxn):
    """Repeat Q with σ'' = refine exactly one step-1 block (b'' = 2), print Index at each length."""
    for s in range(steps):
        b = len(blocks)
        mask = [True] + [False] * (2 * b - 1)
        Q, n, new = quad(E, m, blocks, mask)
        assert selfdual(Q, n)
        if n > maxn:
            break
        I = brute_index(Q, n) if n <= 24 else rust_index(Q, f"q{n}")
        how = "brute force, sign-exact" if n <= 24 else "Rust, |I| meaningful"
        fn = os.path.join(HERE, "..", "codes", f"quad_index24_len{n}.txt")
        with open(fn, "w") as fh:
            fh.write("\n".join("".join(map(str, r)) for r in Q) + "\n")
        print(f"3   n = {n} = 12·{n // 12}: Index = {I} ({how}); saved codes/{os.path.basename(fn)}; next σ'' = {new}", flush=True)
        E, m, blocks = Q, n, new


if __name__ == "__main__":
    maxn = 72 if "--no84" in sys.argv else 84
    rng = random.Random(8)
    part1(40, rng)
    part2()
    for b in (1, 2):
        blocks, r = first_block_system(GOLAY, 12, b)
        print(f"3 chain from Golay, σ = {blocks} (b = {b}), R_σ(Golay) = {r}:", flush=True)
        chain(GOLAY, 12, blocks, 3, maxn)
