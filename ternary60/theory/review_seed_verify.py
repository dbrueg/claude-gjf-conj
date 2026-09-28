"""Review check (2026-09-28, paper/review-2026-09-28.md §5 S4): independent verification of the alternative seeds
proposed in the review (Golay with a Q₈; GJF's own k = 3 code with ℤ/6 = ⟨−h⟩), with fresh code.

Nothing is imported from the scripts that found them. R_σ is computed sign-exactly by information-set
enumeration: a word contributing to R_σ is nonzero on every singleton, so if I is a set of coordinates
containing an information set's worth of singletons, the contributing words are determined by their
values on I, with the values on the singletons in I restricted to {1, 2}. Words are walked in a mixed
Gray code, one bit-sliced F_3 addition per step.

Usage: python3 review_seed_verify.py   (reads the codes and systems written by review_golay_q8.py and
review_gjf36_z6.py, see main()).
"""
import os
import sys

from review_conj14_check import (vec, unvec, vadd, vneg, pc, rref, is_self_dual, codewords, R_sigma,
                                 GOLAY_PAPER, log, LOG)

HERE = os.path.dirname(os.path.abspath(__file__))
CODES = os.path.join(HERE, "..", "codes")


def read_rows(path):
    rows = []
    with open(path) as fh:
        for line in fh:
            s = line.strip().replace(" ", "")
            if s and all(c in "012" for c in s):
                rows.append([int(c) for c in s])
    return rows


def systematic(rows, n, prefer):
    """Row-reduce so that the pivots lie in `prefer` as far as possible (greedy, in the given order).
    Returns (pivot columns, rows) with rows[j] having 1 at pivot j and 0 at the other pivots."""
    rows = [list(r) for r in rref(rows, n)]
    k = len(rows)
    order = list(prefer) + [c for c in range(n) if c not in prefer]
    piv = []
    used = [False] * k
    R = [list(r) for r in rows]
    for c in order:
        if len(piv) == k:
            break
        j = next((j for j in range(k) if not used[j] and R[j][c] % 3), None)
        if j is None:
            continue
        inv = 1 if R[j][c] % 3 == 1 else 2
        R[j] = [(inv * v) % 3 for v in R[j]]
        for t in range(k):
            if t != j and R[t][c] % 3:
                a = R[t][c]
                R[t] = [(x - a * y) % 3 for x, y in zip(R[t], R[j])]
        used[j] = True
        piv.append((c, j))
    assert len(piv) == k
    return [c for c, _ in piv], [R[j] for _, j in piv]


def R_infoset(rows, n, blocks):
    """Sign-exact R_σ by enumeration over an information set chosen among the singletons first."""
    bm = [sum(1 << i for i in b) for b in blocks]
    inblock = set(i for b in blocks for i in b)
    sing = [i for i in range(n) if i not in inblock]
    smask = sum(1 << i for i in sing)
    lam = (0, -2, 0, 0, 1)
    pivots, R = systematic(rows, n, sing)
    vs = [vec(r) for r in R]
    # alphabet per pivot: singletons take {1, 2}, block coordinates take {0, 1, 2}
    alph = [(1, 2) if c in set(sing) else (0, 1, 2) for c in pivots]
    # start word: every pivot at its first letter
    w = (0, 0)
    for v, a in zip(vs, alph):
        if a[0] == 1:
            w = vadd(w, v)
    # mixed-radix reflected Gray code
    k = len(vs)
    digit = [0] * k
    direc = [1] * k
    total = 0

    def weight(x):
        A, B = x
        if (A | B) & smask != smask:
            return 0
        s = -1 if pc(A & smask) & 1 else 1
        supp = A | B
        for m in bm:
            s *= lam[pc(supp & m)]
            if s == 0:
                return 0
        return s

    total += weight(w)
    while True:
        j = 0
        while j < k:
            nd = digit[j] + direc[j]
            if 0 <= nd < len(alph[j]):
                break
            direc[j] = -direc[j]
            j += 1
        if j == k:
            break
        old, new = alph[j][digit[j]], alph[j][nd]
        delta = (new - old) % 3
        w = vadd(w, vs[j] if delta == 1 else vneg(vs[j]))
        digit[j] = nd
        total += weight(w)
    return total


def mono_apply(g, x):
    """(g x)_{perm[i]} = signs[i] x_i for a signed permutation g = (perm, signs)."""
    p, s = g
    y = [0] * len(x)
    for i, v in enumerate(x):
        y[p[i]] = (s[i] * v) % 3
    return y


def mono_mul(g, h):
    """g∘h."""
    n = len(g[0])
    e = [[1 if i == j else 0 for i in range(n)] for j in range(n)]
    p, s = [0] * n, [0] * n
    for j in range(n):
        y = mono_apply(g, mono_apply(h, e[j]))
        i = next(t for t in range(n) if y[t])
        p[j], s[j] = i, (1 if y[i] == 1 else -1)
    return (tuple(p), tuple(s))


def mono_pow(g, k):
    n = len(g[0])
    r = (tuple(range(n)), (1,) * n)
    for _ in range(k):
        r = mono_mul(g, r)
    return r


def is_aut(g, rows, n):
    """g maps the code into itself (rank test)."""
    base = rref(rows, n)
    return all(len(rref(base + [mono_apply(g, r)], n)) == len(base) for r in rows)


def left_kernel(M, m, n):
    """All a in F_3^m with a·M = 0 (M is m x n), as a basis."""
    # solve M^T a = 0: row-reduce the n x m matrix M^T
    T = [[M[i][j] for i in range(m)] for j in range(n)]
    R = rref(T, m)
    piv = []
    for r in R:
        piv.append(next(c for c in range(m) if r[c]))
    free = [c for c in range(m) if c not in piv]
    basis = []
    for fcol in free:
        a = [0] * m
        a[fcol] = 1
        for r, pc_ in zip(R, piv):
            a[pc_] = (-r[fcol]) % 3
        basis.append(a)
    return basis


def fixed_subcode(rows, n, h):
    base = rref(rows, n)
    m = len(base)
    M = [[(a - b) % 3 for a, b in zip(mono_apply(h, r), r)] for r in base]
    ker = left_kernel(M, m, n)
    fixed = [[sum(a[i] * base[i][c] for i in range(m)) % 3 for c in range(n)] for a in ker]
    return rref(fixed, n) if fixed else []


def twined_R(rows, n, h, blocks):
    """R^h_σ(E) = Σ_{x∈E^h} Π_{singletons j} φ(x_j) Π_{h-orbits of blocks} λ(wt x|β): the twined count of
    the chain codes (T_h(Q_σ E) = R^h_σ(E), [CS] Lemma 2.3); with blocks = [] it is T_h(E)."""
    F = fixed_subcode(rows, n, h)
    W = codewords(F, n) if F else [(0, 0)]
    # one block per h-orbit
    reps, seen = [], set()
    for b in blocks:
        fb = frozenset(b)
        if fb in seen:
            continue
        orb = {fb}
        cur = set(b)
        for _ in range(2):
            cur = {h[0][i] for i in cur}
            orb.add(frozenset(cur))
        seen |= orb
        reps.append(set(b))
    inblock = set(i for b in blocks for i in b)
    smask = sum(1 << i for i in range(n) if i not in inblock)
    lam = (0, -2, 0, 0, 1)
    bm = [sum(1 << i for i in b) for b in reps]
    tot = 0
    for A, B in W:
        if (A | B) & smask != smask:
            continue
        s = -1 if pc(A & smask) & 1 else 1
        for mk in bm:
            s *= lam[pc((A | B) & mk)]
        tot += s
    return tot, len(F)


def blocks_of(spec):
    """'(a,b|c,d)' specs -> list of sets."""
    return [set(b) for b in spec]


def check_E36():
    """The seed printed in paper/main-question.tex App. A (= codes/z12seed_len36_3.txt) and its claims."""
    rows = read_rows(os.path.join(CODES, "z12seed_len36_3.txt"))
    n = 36
    assert is_self_dual(rref(rows, n), n)
    p = [0] * n
    s = [1] * n
    for j in range(6):
        for i in range(6):
            p[6 * j + i] = 6 * j + (i + 1) % 6
            s[6 * j + i] = -1 if i == 5 else 1
    g = (tuple(p), tuple(s))
    assert is_aut(g, rows, n)
    ident = (tuple(range(n)), (1,) * n)
    neg = (tuple(range(n)), (-1,) * n)
    assert mono_pow(g, 6) == neg and mono_pow(g, 12) == ident
    h = mono_pow(g, 4)
    assert all(h[0][i] != i for i in range(n))
    idx = R_infoset(rows, n, [])
    Th, dimF = twined_R(rows, n, h, [])
    s3 = [(24, 27, 30, 33), (28, 25, 34, 31), (26, 29, 32, 35)]
    s3p = [(0, 3, 7, 10), (4, 1, 11, 8), (2, 5, 9, 6)]
    s6 = s3p + [(12, 15, 25, 28), (16, 13, 29, 26), (14, 17, 27, 24)]
    r3 = R_infoset(rows, n, blocks_of(s3))
    r6 = R_infoset(rows, n, blocks_of(s6))
    t3, _ = twined_R(rows, n, h, blocks_of(s3))
    t6, _ = twined_R(rows, n, h, blocks_of(s6))
    log(f"E36 (paper App. A = z12seed_len36_3): self-dual, g ∈ Aut, g^6 = −1, g^12 = 1, h = g^4 fixed-point-free; "
        f"Index = {idx}, T_h = {Th} (dim E^h = {dimF}); R_σ3 = {r3}, R_σ6 = {r6}; twined R^h_σ3 = {t3}, R^h_σ6 = {t6} "
        f"(paper: 24, 0, −24, −24, 0, 0)")
    assert (idx, Th, r3, r6, t3, t6) == (24, 0, -24, -24, 0, 0)


def read_gens(path, n):
    """Generators written by mainq_common.write_gens: per generator a line of the permutation (space-separated)
    and a line of signs (1/2 or ±1); tolerate either layout."""
    def ints(tokens):
        return [t for t in tokens if t.lstrip("-").isdigit()]
    lines = [ints(l.split()) for l in open(path) if l.strip() and not l.startswith("#")]
    lines = [l for l in lines if l]
    gens = []
    i = 0
    while i + 1 < len(lines):
        p = tuple(int(x) for x in lines[i])
        sraw = [int(x) for x in lines[i + 1]]
        s = tuple(1 if v == 1 else -1 for v in sraw)
        if len(p) == n and len(s) == n and sorted(p) == list(range(n)):
            gens.append((p, s))
            i += 2
        else:
            i += 1
    return gens


def check_gjf36():
    """GJF's own k = 3 example (GJF Ex 5.7, codes/gjf_ex57_len36.txt) as a ℤ/6 = <−h> seed, h = shift by 12."""
    rows = read_rows(os.path.join(CODES, "gjf_ex57_len36.txt"))
    n = 36
    assert is_self_dual(rref(rows, n), n)
    h = (tuple((i + 12) % n for i in range(n)), (1,) * n)
    assert is_aut(h, rows, n)
    idx = R_infoset(rows, n, [])
    Th, dimF = twined_R(rows, n, h, [])
    sA = [(0, 25, 2, 5), (12, 1, 14, 17), (24, 13, 26, 29)]
    sB = [(2, 15, 28, 21), (14, 27, 4, 33), (26, 3, 16, 9), (5, 6, 31, 10), (17, 18, 7, 22), (29, 30, 19, 34)]
    for sig in (sA, sB):                      # each is a union of h-orbits of blocks
        S = {frozenset(b) for b in sig}
        assert all(frozenset(h[0][i] for i in b) in S for b in sig)
        assert len(set(i for b in sig for i in b)) == 4 * len(sig)
    rA = R_infoset(rows, n, blocks_of(sA))
    rB = R_infoset(rows, n, blocks_of(sB))
    tA, _ = twined_R(rows, n, h, blocks_of(sA))
    tB, _ = twined_R(rows, n, h, blocks_of(sB))
    log(f"GJF k = 3 code: self-dual, h = shift by 12 ∈ Aut (unsigned, fixed-point-free); Index = {idx}, "
        f"T_h = {Th} (dim E^h = {dimF}); σ_A (3 blocks): R = {rA}, R^h = {tA}; σ_B (6 blocks): R = {rB}, R^h = {tB}")
    assert idx == 24 and Th == 0 and rA == 24 and rB == 24 and tA == 0 and tB == 0
    # the chain code at n = 72 built from σ_A
    path = os.path.join(CODES, "gjf36_z6chain_len72.txt")
    if os.path.exists(path):
        C = read_rows(path)
        m = 72
        sd = is_self_dual(rref(C, m), m)
        gens = read_gens(os.path.join(CODES, "gjf36_z6chain_len72.gens.txt"), m)
        auts = [is_aut(g, C, m) for g in gens]
        hh = next((g for g in gens if mono_pow(g, 3) == (tuple(range(m)), (1,) * m)
                   and all(g[0][i] != i for i in range(m))), None)
        Th72, dim72 = twined_R(C, m, hh, []) if hh else (None, None)
        log(f"chain code n = 72 (from σ_A): self-dual {sd}; {len(gens)} generators read, all automorphisms "
            f"{all(auts)}; h of order 3 without fixed coordinate found: {hh is not None}; T_h = {Th72} "
            f"(dim fixed code {dim72}); Index = R_σA(E) = +24 by the main lemma")
        assert sd and all(auts) and hh is not None and Th72 == 0


def group_closure(gens, n):
    ident = (tuple(range(n)), (1,) * n)
    G = {ident}
    frontier = [ident]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mono_mul(g, x)
                if y not in G:
                    G.add(y)
                    new.append(y)
        frontier = new
    return G


def stable_with_splits(G, blocks):
    """Every g maps each block (a,b|c,d) onto a block, and its split pairs onto that block's split pairs."""
    pairs = {}
    for b in blocks:
        pairs[frozenset(b)] = {frozenset(b[:2]), frozenset(b[2:])}
    for g in G:
        for b in blocks:
            img = frozenset(g[0][i] for i in b)
            if img not in pairs:
                return False
            if {frozenset(g[0][i] for i in b[:2]), frozenset(g[0][i] for i in b[2:])} != pairs[img]:
                return False
    return True


def check_golay_q8():
    """Golay with a Q₈ = <J, K> (J as in paper/main-question.tex §4.2) and the mixed 3-block system."""
    n = 12
    J = ((1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10), (-1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1))
    K = ((2, 3, 0, 1, 6, 7, 4, 5, 11, 10, 9, 8), (-1, 1, 1, -1, -1, -1, 1, 1, 1, -1, 1, -1))
    neg = (tuple(range(n)), (-1,) * n)
    assert is_aut(J, GOLAY_PAPER, n) and is_aut(K, GOLAY_PAPER, n)
    assert mono_mul(J, J) == neg and mono_mul(K, K) == neg
    assert mono_mul(K, J) == mono_mul(neg, mono_mul(J, K))
    G = group_closure([J, K], n)
    assert len(G) == 8
    W = codewords(GOLAY_PAPER, n)
    orbits = [(0, 1, 2, 3), (4, 5, 6, 7), (8, 9, 11, 10)]
    assert stable_with_splits(G, orbits)
    r_orb = R_sigma(W, n, blocks_of(orbits))
    sig = [(0, 1, 2, 3), (4, 5, 11, 10), (6, 7, 8, 9)]
    st = stable_with_splits(G, sig)
    r_sig = R_sigma(W, n, blocks_of(sig))
    stabs = []
    for b in sig:
        S = [g for g in G if frozenset(g[0][i] for i in b) == frozenset(b)]
        stabs.append(len(S))
    log(f"Golay with Q₈ = <J, K>: J, K ∈ Aut, J² = K² = −1, KJ = −JK, |<J,K>| = 8; the three Q₈-orbits give "
        f"R = {r_orb}; the mixed system {sig}: Q₈-stable with splits {st}, block stabilisers of orders {stabs}, "
        f"R_σ(Golay) = {r_sig}")
    assert r_orb == 72 and st and r_sig == -24 and stabs == [8, 4, 4]
    path = os.path.join(CODES, "golay_q8chain_len48.txt")
    if os.path.exists(path):
        m = 48
        C = read_rows(path)
        sd = is_self_dual(rref(C, m), m)
        gens = read_gens(os.path.join(CODES, "golay_q8chain_len48.gens.txt"), m)
        auts = all(is_aut(g, C, m) for g in gens)
        negm = (tuple(range(m)), (-1,) * m)
        Jm, Km = gens[0], gens[1]
        rel = (mono_mul(Jm, Jm) == negm and mono_mul(Km, Km) == negm
               and mono_mul(Km, Jm) == mono_mul(negm, mono_mul(Jm, Km)))
        free = all(Jm[0][i] != i and Km[0][i] != i and mono_mul(Jm, Km)[0][i] != i for i in range(m))
        idx = R_infoset(C, m, [])
        sig2 = [(1, 0, 26, 24), (13, 12, 27, 25), (2, 3, 28, 30), (14, 15, 29, 31)]
        r2 = R_infoset(C, m, blocks_of(sig2))
        st2 = stable_with_splits(group_closure([Jm, Km], m), sig2)
        log(f"Golay-seeded Q₈-chain, n = 48: self-dual {sd}; J, K ∈ Aut {auts}; relations {rel}; V₄ free on "
            f"coordinates {free}; Index = {idx} (sign-exact, 2^24 patterns); next system {sig2}: Q₈-stable with "
            f"splits {st2}, R = {r2}")
        assert sd and auts and rel and free and idx == -24 and r2 == -24 and st2


def selftest():
    """R_infoset against full enumeration on the Golay code and some systems."""
    W = codewords(GOLAY_PAPER, 12)
    for blocks in ([], [{0, 1, 2, 3}], [{0, 1, 2, 3}, {4, 5, 6, 8}], [{0, 5, 7, 9}, {1, 2, 10, 11}, {3, 4, 6, 8}]):
        a = R_infoset(GOLAY_PAPER, 12, blocks)
        b = R_sigma(W, 12, blocks)
        assert a == b, (blocks, a, b)
    log("selftest: information-set R_σ agrees with full enumeration on Golay (4 systems)")


def main():
    LOG.clear()
    selftest()
    check_E36()
    check_gjf36()
    check_golay_q8()
    log("all checks passed")
    with open(os.path.join(HERE, "review_seed_verify.log"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
