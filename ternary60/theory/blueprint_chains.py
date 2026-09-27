"""Checks for notes/blueprint/chains-and-seeds.md: the seeds and chains behind the Main Question, as finite
certificates for a Lean formalization.

Part 1 (tetracode placements, Lemma 2.1 of the blueprint). The 8 monomial images of the tetracode in F_3^4;
        which of them are invariant under the local maps that block stabilisers induce: signed double
        transpositions with square −1, pair swaps, and the regular Q_8-actions on a Q_8-orbit block. Also
        which local maps preserve the placement T_L hard-wired in lean/GJF/Existence.lean; the local identities
        (Lemmas A, B) for T_L and all three pair-splittings.
Part 2 (the seeds, §3). For each seed, recomputed here with independent code (stdlib, bit-sliced F_3):
        self-duality and the automorphisms (membership through a systematic generator matrix), the group
        relations, the stage-0 block systems and their stabilisers, and every number the chains need:
        R_σ(E) and Index(E) by information-set enumeration (sign-exact; the number of candidates is the
        certificate size, Lemma 2.5), the fixed code E^h through D = π(E)^⊥ (π = signed orbit sums; Lemma 2.4), and
        the orbit-weighted twined index R^h_σ(E) (Definition 1.6). Seeds: Golay with J; z12seed_len36_3 with σ_A,
        σ_B (the systems of mainq_z12chain.py) and z12seed_len36_6 with the offset-matched systems σ_A6, σ_B6
        (blueprint §3.3); q8chain_len24; q8z3_seed72.
Part 3 (split conventions and placements, Lemmas 2.2, 2.7, §3.6, §5). A combinatorial simulation of every chain, block systems only
        (no codes): the block counts b, the lengths reached, and the residue classes of k mod 24 covered,
        for the pair-stable refinement split used by the scripts and for the split hard-wired in
        Existence.lean. Also: with the transposed split, stage-0 blocks reordered within their split (searched
        orbit by orbit) and σ″-blocks ordered (x, y, y**, x**), every local map g: β → gβ (all g ∈ G, all
        blocks, and all step-one blocks in the labels of Existence.lean's r₁) preserves the Lean placement T_L,
        for three steps of every chain; so T_L can be placed on every block G-equivariantly.
Part 4 (Lemma 2.3, orbit-weighted form of [MQ] Lemma 4.3). On random h-invariant codes with a fixed-point-
        free permutation h of order 3 and a block system made of h-orbits: T_h(Q_σ(E)) = R^h_σ(E) and
        R^h_{σ″}(Q_σ(E)) = R^h_σ(E), sign-exact, with nonzero values; the naive restriction of R_σ to E^h
        differs.
Part 5 (data files, §6). The generator files jchain_len<n>.J.txt and z12chain_len<n>.g.txt write the
        permutation without separators; count all parses into a permutation of 0..n−1, and how many of
        them are automorphisms of the code with the stated relations.
Part 6 (the n = 72 certificate T6, §3.5). `ternary60 sl2words` on the Q_8 × Z/3 seed: R_σ(E) and Index(E), and
        the number of normalised SL_2-words (good planes) it enumerates.
Part 7 (§3.3). Over the 8 committed ℤ/12 seeds, the offset-matched 3- and 6-block systems (Lemma 2.7) with
        R^h_σ = 0 and |R_σ| = 24; seed 6 is the only seed with both (σ_A6, σ_B6).
"""
import itertools, os, random, subprocess, sys, tempfile, time
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
CODES = os.path.join(HERE, "..", "codes")
BIN = os.path.join(HERE, "..", "target", "release", "ternary60")
PHI = (0, -1, 1)
LAMBDA = (0, -2, 0, 0, 1)
TETRA = ((1, 1, 1, 0), (0, 1, 2, 1))          # also the Lean placement T_L: labels (a,b) ↦ 2a + b


# ------------------------------------------------------------------ F_3 linear algebra (lists)
def rref(rows, order=None):
    """Row-reduce over F_3 with pivots taken along `order`. Returns (rows, pivot columns)."""
    rows = [list(r) for r in rows if any(r)]
    if not rows:
        return [], []
    order = list(range(len(rows[0]))) if order is None else order
    out, piv = [], []
    for c in order:
        p = next((i for i, r in enumerate(rows) if r[c]), None)
        if p is None:
            continue
        r = rows.pop(p)
        r = [(x * r[c]) % 3 for x in r]                      # 1⁻¹ = 1, 2⁻¹ = 2
        rows = [[(x - s[c] * y) % 3 for x, y in zip(s, r)] for s in rows]
        out = [[(x - s[c] * y) % 3 for x, y in zip(s, r)] for s in out]
        out.append(r); piv.append(c)
        rows = [s for s in rows if any(s)]
        if not rows:
            break
    return out, piv


def nullspace(rows, n):
    R, piv = rref(rows) if rows else ([], [])
    out = []
    for fj in (j for j in range(n) if j not in piv):
        v = [0] * n; v[fj] = 1
        for r, pj in zip(R, piv):
            v[pj] = (-r[fj]) % 3
        out.append(v)
    return out


def dot(a, b):
    return sum(x * y for x, y in zip(a, b)) % 3


def read_code(path):
    with open(path) as fh:
        return [[int(ch) for ch in ln.strip()] for ln in fh if ln.strip()]


# ------------------------------------------------------------------ bit-sliced F_3 vectors (a = ones, b = twos)
def bs(v):
    a = b = 0
    for i, x in enumerate(v):
        if x == 1:
            a |= 1 << i
        elif x == 2:
            b |= 1 << i
    return (a, b)


def unbs(x, n):
    return [1 if (x[0] >> i) & 1 else 2 if (x[1] >> i) & 1 else 0 for i in range(n)]


def badd(x, y):
    a1, a2 = x; b1, b2 = y
    za, zb = ~(a1 | a2), ~(b1 | b2)
    return ((a1 & zb) | (b1 & za) | (a2 & b2), (a2 & zb) | (b2 & za) | (a1 & b1))


def bneg(x):
    return (x[1], x[0])


class Code:
    """A linear code given by generator rows, with a systematic form for fast membership."""

    def __init__(self, rows, n):
        self.n = n
        self.R, self.piv = rref(rows)
        self.k = len(self.R)
        self.bR = [bs(r) for r in self.R]

    def contains(self, v):
        x = bs(v)
        for c, r in zip(self.piv, self.bR):
            if v[c] == 1:
                x = badd(x, bneg(r))
            elif v[c] == 2:
                x = badd(x, r)
        return x == (0, 0)

    def self_dual(self):
        return 2 * self.k == self.n and all(dot(a, b) == 0 for i, a in enumerate(self.R) for b in self.R[i:])


# ------------------------------------------------------------------ monomial maps g = (p, s): e_i ↦ s_i e_{p(i)}
def mapply(g, v):
    p, s = g
    y = [0] * len(p)
    for i, x in enumerate(v):
        if x:
            y[p[i]] = x if s[i] == 1 else 3 - x
    return y


def mmul(g, h):
    """g∘h (first h)."""
    return (tuple(g[0][h[0][i]] for i in range(len(h[0]))), tuple(h[1][i] * g[1][h[0][i]] for i in range(len(h[0]))))


def mid(n):
    return (tuple(range(n)), (1,) * n)


def mneg(n):
    return (tuple(range(n)), (-1,) * n)


def mpow(g, k):
    r = mid(len(g[0]))
    for _ in range(k):
        r = mmul(g, r)
    return r


def morder(g):
    e, x, k = mid(len(g[0])), g, 1
    while x != e:
        x, k = mmul(g, x), k + 1
    return k


def closure(gens):
    n = len(gens[0][0])
    seen, fr = {mid(n)}, [mid(n)]
    while fr:
        nf = []
        for x in fr:
            for g in gens:
                y = mmul(g, x)
                if y not in seen:
                    seen.add(y); nf.append(y)
        fr = nf
    return seen


def is_aut(g, C):
    return all(C.contains(mapply(g, r)) for r in C.R)


def signed_cycles(n, L):
    p, s = [0] * n, [1] * n
    for j in range(n // L):
        for i in range(L):
            p[L * j + i] = L * j + (i + 1) % L
        s[L * j + L - 1] = -1
    return (tuple(p), tuple(s))


def q8_blocks(n):
    """J, K on each group of 4 coordinates (as in mainq_q8chain.q8): the first sign choice with the relations."""
    neg4 = mneg(4)
    for s in itertools.product((1, -1), repeat=4):
        for t in itertools.product((1, -1), repeat=4):
            J4, K4 = ((1, 0, 3, 2), s), ((2, 3, 0, 1), t)
            if mmul(J4, J4) == neg4 and mmul(K4, K4) == neg4 and mmul(J4, K4) == mmul(neg4, mmul(K4, J4)):
                J = (tuple(4 * j + x for j in range(n // 4) for x in J4[0]), J4[1] * (n // 4))
                K = (tuple(4 * j + x for j in range(n // 4) for x in K4[0]), K4[1] * (n // 4))
                return J, K


# ------------------------------------------------------------------ weights and sums
def weight_fn(n, blocks, lam=LAMBDA):
    """x ↦ Π_{singletons} φ(x_i) Π_{blocks} λ(wt x|_β), on bit-sliced x (λ = (λ(0), …, λ(4)), default (0,−2,0,0,1))."""
    inb = {x for b in blocks for x in b}
    smask = sum(1 << i for i in range(n) if i not in inb)
    bmasks = [sum(1 << i for i in b) for b in blocks]

    def w(x):
        a, b = x
        sup = a | b
        if sup & smask != smask:
            return 0
        val = -1 if (a & smask).bit_count() & 1 else 1
        for m in bmasks:
            c = (sup & m).bit_count()
            if c == 1:
                val *= lam[1]
            elif c != 4:
                return 0
        return val
    return w


def span_sum(rows, n, w):
    """Σ_{x ∈ span(rows)} w(x), full enumeration (3^dim leaves)."""
    vecs = [bs(r) for r in rows]
    tot = 0
    stack = [(0, (0, 0))]
    while stack:
        i, acc = stack.pop()
        if i == len(vecs):
            tot += w(acc)
            continue
        v = vecs[i]
        stack += [(i + 1, acc), (i + 1, badd(acc, v)), (i + 1, badd(acc, bneg(v)))]
    return tot


NPAT = {0: 1, 1: 3, 2: 9, 3: 15, 4: 24}      # patterns on |β ∩ I| coordinates extendable to block weight 1 or 4


def infoset_sum(rows, n, blocks, rng, tries=80, lam=LAMBDA):
    """R_σ(span rows) = Σ over candidates on an information set I (Lemma 2.7): singleton coordinates of I
    take the values ±1, the coordinates β ∩ I of a block take the patterns extendable to block weight 1 or 4.
    Returns (value, number of candidates, (|I ∩ singletons|, block profile))."""
    inb = {x: j for j, b in enumerate(blocks) for x in b}
    sing = [i for i in range(n) if i not in inb]
    best = None
    for t in range(tries):
        s = sing[:]; rng.shuffle(s)
        bl = list(range(len(blocks))); rng.shuffle(bl)
        cut = rng.randrange(len(bl) + 1) if t % 3 == 2 else (0 if t % 3 == 0 else len(bl))
        order = [x for j in bl[:cut] for x in blocks[j]] + s + [x for j in bl[cut:] for x in blocks[j]]
        R, piv = rref(rows, order)
        cnt = 2 ** sum(1 for c in piv if c not in inb)
        prof = [sum(1 for c in piv if inb.get(c) == j) for j in range(len(blocks))]
        for q in prof:
            cnt *= NPAT[q]
        if best is None or cnt < best[0]:
            best = (cnt, R, piv, prof)
    cnt, R, piv, prof = best
    rowof = {c: bs(r) for r, c in zip(R, piv)}
    units = [[rowof[c], bneg(rowof[c])] for c in piv if c not in inb]
    for j in range(len(blocks)):
        cs = [c for c in piv if inb.get(c) == j]
        if not cs:
            continue
        pats = []
        for vals in itertools.product(range(3), repeat=len(cs)):
            wt = sum(1 for x in vals if x)
            if (wt in (1, 4)) if len(cs) == 4 else (wt == len(cs) or wt <= 1):
                acc = (0, 0)
                for c, x in zip(cs, vals):
                    if x:
                        acc = badd(acc, rowof[c] if x == 1 else bneg(rowof[c]))
                pats.append(acc)
        units.append(pats)
    w = weight_fn(n, blocks, lam)
    tot = 0

    def rec(i, acc):
        nonlocal tot
        if i == len(units):
            tot += w(acc)
            return
        for v in units[i]:
            rec(i + 1, badd(acc, v))
    rec(0, (0, 0))
    return tot, cnt, (sum(1 for c in piv if c not in inb), sorted(prof, reverse=True))


# ------------------------------------------------------------------ order-3 elements: orbits, π, fixed codes
def h_orbits(h):
    n = len(h[0])
    seen, orbs = set(), []
    for i in range(n):
        if i not in seen:
            o = [i, h[0][i], h[0][h[0][i]]]
            assert len(set(o)) == 3 and h[0][o[2]] == i, "h must be fixed-point-free of order 3"
            seen.update(o); orbs.append(o)
    return orbs


def pi_map(h, orbs):
    """Signed orbit sums π(c)_o = c_i + s_i c_{hi} + s_i s_{hi} c_{h²i}; and the expansion x̄ ↦ x of fixed vectors."""
    p, s = h
    coef = [(o[0], 1, o[1], s[o[0]], o[2], s[o[0]] * s[o[1]]) for o in orbs]

    def pi(c):
        return [(c[i] + si * c[j] + sj * c[k]) % 3 for i, _, j, si, k, sj in coef]

    def expand(xb):
        x = [0] * len(p)
        for (i, _, j, si, k, sj), v in zip(coef, xb):
            x[i], x[j], x[k] = v, (si * v) % 3, (sj * v) % 3
        return x
    return pi, expand


def twined_data(C, h, blocks, fast=False):
    """For self-dual C and h ∈ Aut(C) fixed-point-free of order 3 (signed): D = π(C)^⊥ (the collapsed fixed
    code, Lemma 2.6), dim C^h, and the orbit-weighted twined index R^h_σ (Definition 1.6) together with
    T_h = Σ_{x∈C^h} f(x), both sign-exact (x expanded from x̄). blocks = σ (a union of h-orbits of blocks)."""
    n = C.n
    orbs = h_orbits(h)
    pi, expand = pi_map(h, orbs)
    P = [pi(r) for r in C.R]
    rk = len(rref(P)[0])
    D = nullspace(P, len(orbs))
    # sanity: the expansions of a basis of D lie in C and are h-fixed
    ok = all(C.contains(expand(d)) and mapply(h, expand(d)) == expand(d) for d in D)
    # one block per h-orbit of blocks
    bset = {frozenset(b): b for b in blocks}
    reps, seen = [], set()
    for b in blocks:
        if frozenset(b) in seen:
            continue
        orb = {frozenset(b), frozenset(h[0][x] for x in b), frozenset(h[0][h[0][x]] for x in b)}
        assert all(o in bset for o in orb) and len(orb) == 3
        seen |= orb; reps.append(b)
    inb = {x for b in blocks for x in b}
    orb_of = {x: t for t, o in enumerate(orbs) for x in o}
    sing_orbs = [t for t, o in enumerate(orbs) if o[0] not in inb]
    sbar = [sorted(orb_of[y] for y in b) for b in reps]
    if fast:
        # h a permutation: f(x) = f(x̄) (φ³ = φ) and the orbit weights are R_σ̄ on D, so both sums are
        # information-set sums on D (Lemma 2.5, Remark)
        assert all(v == 1 for v in h[1])
        rng = random.Random(3)
        Th = infoset_sum(D, len(orbs), [], rng)[0]
        Rh = infoset_sum(D, len(orbs), [tuple(b) for b in sbar], rng)[0]
        Rn = infoset_sum(D, len(orbs), [tuple(b) for b in sbar], rng, lam=(0, -8, 0, 0, 1))[0]
        return dict(D=D, dimD=len(D), rank_pi=rk, N=len(orbs), expand_ok=ok, Rh=Rh, Th=Th, naive=Rn, sbar=sbar)
    Rh = Th = 0
    wrep = weight_fn(n, reps)                # used only on the representative blocks
    for coeffs in itertools.product(range(3), repeat=len(D)):
        xb = [sum(c * d[t] for c, d in zip(coeffs, D)) % 3 for t in range(len(orbs))]
        x = expand(xb)
        # T_h: full f on x
        f = 1
        for v in x:
            f *= PHI[v]
            if not f:
                break
        Th += f
        # R^h: φ over one coordinate per singleton orbit (the orbit representative), λ per block orbit
        val = 1
        for t in sing_orbs:
            val *= PHI[x[orbs[t][0]]]
            if not val:
                break
        if val:
            for b in reps:
                val *= LAMBDA[sum(1 for y in b if x[y])]
                if not val:
                    break
        Rh += val
    return dict(D=D, dimD=len(D), rank_pi=rk, N=len(orbs), expand_ok=ok, Rh=Rh, Th=Th, sbar=sbar)


# ------------------------------------------------------------------ Part 1: placements
def all_signed_perms4():
    for p in itertools.permutations(range(4)):
        for s in itertools.product((1, -1), repeat=4):
            yield (p, s)


def placements():
    out = {}
    for g in all_signed_perms4():
        rows = [mapply(g, list(r)) for r in TETRA]
        words = frozenset(tuple((a * x + b * y) % 3 for x, y in zip(*rows)) for a in range(3) for b in range(3))
        out.setdefault(words, rows)
    return list(out.items())


def invariant_under(words, gens):
    return all(tuple(mapply(g, list(w))) in words for g in gens for w in words)


def part1():
    PL = placements()
    TL = next(i for i, (w, _) in enumerate(PL) if tuple(TETRA[0]) in w and tuple(TETRA[1]) in w)
    print(f"1 {len(PL)} tetracode placements in F_3^4; the Lean placement T_L = <1110, 0121> is placement {TL}", flush=True)
    for i, (w, rows) in enumerate(PL):
        print(f"1   placement {i}: rows {''.join(map(str, rows[0]))}, {''.join(map(str, rows[1]))}", flush=True)
    neg = mneg(4)
    dts = [g for g in all_signed_perms4() if sorted(len(c) for c in cycles(g[0])) == [2, 2] and mmul(g, g) == neg]
    inv = [[i for i, (w, _) in enumerate(PL) if invariant_under(w, [g])] for g in dts]
    print(f"1 signed double transpositions x with x² = −1: {len(dts)}; each fixes exactly "
          f"{sorted(set(len(v) for v in inv))} of the 8 placements", flush=True)
    # regular Q8-actions (J4 = (01)(23), K4 = (02)(13) with signs, J² = K² = −1, JK = −KJ)
    q8s = []
    for s in itertools.product((1, -1), repeat=4):
        for t in itertools.product((1, -1), repeat=4):
            J4, K4 = ((1, 0, 3, 2), s), ((2, 3, 0, 1), t)
            if mmul(J4, J4) == neg and mmul(K4, K4) == neg and mmul(J4, K4) == mmul(neg, mmul(K4, J4)):
                q8s.append((J4, K4))
    invq = [[i for i, (w, _) in enumerate(PL) if invariant_under(w, [J4, K4])] for J4, K4 in q8s]
    print(f"1 regular Q_8-actions on a 4-block (J = (01)(23), K = (02)(13) with signs): {len(q8s)}; each fixes "
          f"exactly {sorted(set(len(v) for v in invq))} placements", flush=True)
    try:
        sys.path.insert(0, HERE)
        from mainq_morita import q8_gens
        Jm, Km = q8_gens(1)
        im = [i for i, (w, _) in enumerate(PL) if invariant_under(w, [Jm, Km])]
        print(f"1 Morita Q_8 (left multiplication by i, j in quaternion coordinates): invariant placements {im}; "
              f"T_L among them: {TL in im}", flush=True)
    except ImportError:
        pass
    # local maps in Lean labels (a, b) ↦ 2a + b; pairs = first coordinate
    wTL = PL[TL][0]
    within = {}
    for s0, s1 in itertools.product((1, -1), repeat=2):
        x = ((1, 0, 3, 2), (s0, -s0, s1, -s1))
        within[(s0, s1)] = invariant_under(wTL, [x])
    swaps = {}
    for e in (1, -1):
        y = ((2, 3, 0, 1), (e, e, -e, -e))
        swaps[e] = invariant_under(wTL, [y])
    print(f"1 T_L under within-pair swaps x_(s0,s1) (e_(a,0) ↦ s_a e_(a,1), e_(a,1) ↦ −s_a e_(a,0)): "
          f"{ {k: v for k, v in within.items()} }  (invariant iff s0·s1 = −1)", flush=True)
    print(f"1 T_L under pair swaps y_ε (e_(0,s) ↦ ε e_(1,s), e_(1,s) ↦ −ε e_(0,s)): {swaps}", flush=True)
    diag = [i for i, (w, _) in enumerate(PL) if invariant_under(w, [((1, 0, 3, 2), (1, -1, 1, -1))])]
    print(f"1 placements invariant under the diagonal within-pair swap x_(1,1) (the stabiliser action on a block "
          f"refined with the pair-stable split, labels (u, b)): {diag}", flush=True)
    # table: placement × local-map type (x_(1,1) diagonal within-pair swap; x_(1,−1); y_1 pair swap; y'_1 pair swap
    # with opposite signs on the two copies; Morita Q_8), and the transposed labelling (a,b) ↦ (b,a)
    types = {"x(1,1)": [((1, 0, 3, 2), (1, -1, 1, -1))], "x(1,-1)": [((1, 0, 3, 2), (1, -1, -1, 1))],
             "y(1)": [((2, 3, 0, 1), (1, 1, -1, -1))]}
    try:
        types["Q8 Morita"] = [Jm, Km]
    except NameError:
        pass
    tau = ((0, 2, 1, 3), (1, 1, 1, 1))
    for i, (w, rows) in enumerate(PL):
        wt = frozenset(tuple(mapply(tau, list(v))) for v in w)
        j = next(t for t, (w2, _) in enumerate(PL) if w2 == wt)
        print(f"1   placement {i}: " + ", ".join(f"{k} {invariant_under(w, gs)}" for k, gs in types.items())
              + f"; in transposed labels it is placement {j}", flush=True)
    # the local identities (Lemma A: doubled block as 8 singletons; Lemma B: doubled block refined along each
    # of the 3 pair-splittings) for T_L, all u ∈ F_3^4; doubling pairs position i with a new position i′
    TLw = sorted(PL[TL][0])
    lamw = lambda c: LAMBDA[c]
    splits = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
    locA = locB = True
    for u in itertools.product(range(3), repeat=4):
        target = LAMBDA[sum(1 for x in u if x)]
        sA, sB = 0, [0, 0, 0]
        for t in TLw:
            v0 = [(a + b) % 3 for a, b in zip(u, t)]; v1 = [(a - b) % 3 for a, b in zip(u, t)]
            f8 = 1
            for x in v0 + v1:
                f8 *= PHI[x]
            sA += f8
            for j, (P, Q) in enumerate(splits):
                wP = sum(1 for i in P for v in (v0, v1) if v[i]); wQ = sum(1 for i in Q for v in (v0, v1) if v[i])
                sB[j] += LAMBDA[wP] * LAMBDA[wQ]
        locA &= sA == target
        locB &= all(x == target for x in sB)
    print(f"1 local identities for T_L, all 81 u: Lemma A {locA}; Lemma B for each of the 3 pair-splittings {locB}", flush=True)
    # split-preserving elements of Mon(T_L) and their pair maps (Lemma 2.7): with rotation pair maps they are
    # (r, r⁻¹) keeping the pairs and (r, −r⁻¹) swapping them
    def pmat(g, src, dst):
        M = [[0, 0], [0, 0]]
        for j, x in enumerate(src):
            M[dst.index(g[0][x])][j] = g[1][x]
        return M
    mul2 = lambda A, B: [[sum(A[i][t] * B[t][j] for t in range(2)) for j in range(2)] for i in range(2)]
    inv2 = lambda A: [[A[j][i] for j in range(2)] for i in range(2)]          # signed permutation matrices
    neg2 = lambda A: [[-x for x in r] for r in A]
    det2i = lambda A: A[0][0] * A[1][1] - A[0][1] * A[1][0]
    splitT = [g for g in all_signed_perms4() if {frozenset(g[0][:2]), frozenset(g[0][2:])} == {frozenset((0, 1)), frozenset((2, 3))}
              and invariant_under(wTL, [g])]
    rot_ok, n_rot = True, 0
    for g in splitT:
        swap = g[0][0] in (2, 3)
        M0 = pmat(g, (0, 1), (2, 3) if swap else (0, 1)); M1 = pmat(g, (2, 3), (0, 1) if swap else (2, 3))
        if det2i(M0) == 1 and det2i(M1) == 1:
            n_rot += 1
            rot_ok &= M1 == (neg2(inv2(M0)) if swap else inv2(M0))
        else:
            rot_ok &= det2i(M0) == det2i(M1) == -1
    print(f"1 split-preserving elements of Mon(T_L): {len(splitT)}; {n_rot} with both pair maps rotations, and these are "
          f"exactly (r, r⁻¹) (pairs kept) and (r, −r⁻¹) (pairs swapped); the rest have two reflections: {rot_ok}", flush=True)
    ok = (rot_ok and len(splitT) == 16 and n_rot == 8 and locA and locB and len(PL) == 8 and set(len(v) for v in inv) == {4} and set(len(v) for v in invq) == {4}
          and within[(1, -1)] and within[(-1, 1)] and not within[(1, 1)] and not within[(-1, -1)]
          and swaps[1] and swaps[-1] and len(diag) == 4)
    return ok, PL, TL


def cycles(p):
    seen, out = set(), []
    for i in range(len(p)):
        if i not in seen:
            c, j = [], i
            while j not in seen:
                seen.add(j); c.append(j); j = p[j]
            out.append(c)
    return out


def local_map(g, blk, img):
    """The local map of g from block blk (4-tuple, Lean labels 0..3) to block img: (perm of labels, signs)."""
    pos = {x: i for i, x in enumerate(img)}
    return (tuple(pos[g[0][x]] for x in blk), tuple(g[1][x] for x in blk))


# ------------------------------------------------------------------ Part 2: the seeds
GOLAY = [[1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1], [0, 1, 0, 0, 0, 0, 2, 0, 1, 2, 2, 1],
         [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 2, 2], [0, 0, 0, 1, 0, 0, 2, 2, 1, 0, 1, 2],
         [0, 0, 0, 0, 1, 0, 2, 2, 2, 1, 0, 1], [0, 0, 0, 0, 0, 1, 2, 1, 2, 2, 1, 0]]   # = golayRow in Existence.lean
J_GOLAY = ((1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10), (-1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1))   # mainq_jchain.J
SIGMA_A = [(24, 27, 30, 33), (28, 25, 34, 31), (26, 29, 32, 35)]                               # mainq_z12chain
SIGMA_B = [(0, 3, 7, 10), (4, 1, 11, 8), (2, 5, 9, 6), (12, 15, 25, 28), (16, 13, 29, 26), (14, 17, 27, 24)]
SIGMA_Q8 = [(9, 8, 11, 10), (13, 12, 15, 14)]                                                 # mainq_q8chain log
# seed 6: systems whose two J-pairs have equal offsets in their 6-cycles (Lemma 2.7; found by a search over the
# 15 + 45 offset-matched systems of the 8 committed seeds, see the blueprint §3.3)
SIGMA_A6 = [(0, 3, 12, 15), (4, 1, 16, 13), (2, 5, 14, 17)]
SIGMA_B6 = [(0, 3, 30, 33), (4, 1, 34, 31), (2, 5, 32, 35), (6, 9, 12, 15), (10, 7, 16, 13), (8, 11, 14, 17)]


def block_report(G, blocks, PL, TL):
    """G permutes the blocks and maps split pairs to split pairs; stabiliser orders; whether each stabiliser
    fixes both split pairs; the invariant placements for each stabiliser's local action (Lean labels)."""
    by = {frozenset(b): b for b in blocks}
    split = lambda b: frozenset((frozenset(b[:2]), frozenset(b[2:])))
    stable = all(frozenset(g[0][x] for x in b) in by and
                 split(tuple(g[0][x] for x in b)) == split(by[frozenset(g[0][x] for x in b)])
                 for g in G for b in blocks)
    stabs, pairfix, inv_TL, nplace = [], [], [], []
    for b in blocks:
        St = [g for g in G if frozenset(g[0][x] for x in b) == frozenset(b)]
        stabs.append(len(St))
        pairfix.append(all(frozenset(g[0][x] for x in b[:2]) == frozenset(b[:2]) for g in St))
        locs = [local_map(g, b, b) for g in St]
        inv = [i for i, (w, _) in enumerate(PL) if invariant_under(w, locs)]
        nplace.append(len(inv)); inv_TL.append(TL in inv)
    block_report.first = [i for i, (w, _) in enumerate(PL) if invariant_under(
        w, [local_map(g, blocks[0], blocks[0]) for g in G if frozenset(g[0][x] for x in blocks[0]) == frozenset(blocks[0])])]
    # (★) every g stabilising a split pair {x, y} acts on it as ±id or as a signed swap with square −1; and the
    # diagonal action of the pair stabiliser on the step-1 block {x, x*, y, y*} (labels x, x*, y, y*) fixes a placement
    star, p2 = True, True
    for b in blocks:
        for pr in (b[:2], b[2:]):
            St = [g for g in G if {g[0][z] for z in pr} == set(pr)]
            locs = []
            for g in St:
                (x, y), (sx, sy) = pr, (g[1][pr[0]], g[1][pr[1]])
                if g[0][x] == x:
                    star &= sx == sy
                    locs.append(((0, 1, 2, 3), (sx, sx, sy, sy)))
                else:
                    star &= sx * sy == -1
                    locs.append(((2, 3, 0, 1), (sx, sx, sy, sy)))
            p2 &= any(invariant_under(w, locs) for w, _ in PL)
    block_report.star, block_report.p2 = star, p2
    # Lean-compatible orderings: orderings of each block that keep its split (pairs = first two, last two) and in
    # whose labels the stabiliser's local maps preserve the Lean placement T_L
    wTL = PL[TL][0]
    good = []
    for b in blocks:
        St = [g for g in G if frozenset(g[0][x] for x in b) == frozenset(b)]
        cnt = 0
        for P1, P2 in ((b[:2], b[2:]), (b[2:], b[:2])):
            for o1 in (P1, P1[::-1]):
                for o2 in (P2, P2[::-1]):
                    o = tuple(o1) + tuple(o2)
                    cnt += invariant_under(wTL, [local_map(g, o, o) for g in St])
        good.append(cnt)
    block_report.lean_orders = sorted(set(good))
    return stable, stabs, pairfix, nplace, inv_TL


def seed_J(rng, PL, TL):
    C = Code(GOLAY, 12)
    J = J_GOLAY
    ok_aut = is_aut(J, C)
    G = closure([J])
    stable, stabs, pairfix, nplace, invTL = block_report(G, [(0, 1, 2, 3)], PL, TL)
    R = span_sum(C.R, 12, weight_fn(12, [(0, 1, 2, 3)]))
    I = span_sum(C.R, 12, weight_fn(12, []))
    print(f"2 J-chain seed Golay (= Lean golayRow): self-dual {C.self_dual()}, J ∈ Aut {ok_aut}, J² = −1 "
          f"{mmul(J, J) == mneg(12)}, cycle shape {sorted(len(c) for c in cycles(J[0]))}; σ = (0,1,2,3): G-stable with "
          f"split pairs {stable}, |stabiliser| {stabs}, stabiliser fixes both pairs {pairfix}, invariant placements "
          f"{nplace} (namely {block_report.first}), Lean T_L invariant {invTL}; (★) {block_report.star}, step-1 placements {block_report.p2}, split-respecting orderings with T_L invariant {block_report.lean_orders}/8; Index = {I}, R_σ = {R} (729 codewords)", flush=True)
    return ok_aut and C.self_dual() and stable and R == 24 and I == 24 and all(pairfix) and block_report.star and block_report.p2


def seed_z12(rng, PL, TL, stem="z12seed_len36_3", systems=(("A", SIGMA_A, -24), ("B", SIGMA_B, -24)), index=24):
    E = read_code(os.path.join(CODES, stem + ".txt"))
    C = Code(E, 36)
    g = signed_cycles(36, 6)
    J, h = mpow(g, 3), mpow(g, 4)
    G = closure([g])
    head = (f"2 ℤ/12 seed {stem}: self-dual {C.self_dual()}, g ∈ Aut {is_aut(g, C)}, ord g {morder(g)}, "
            f"g⁶ = −1 {mpow(g, 6) == mneg(36)}, h = g⁴ fixed-point-free {all(h[0][i] != i for i in range(36))}")
    t0 = time.time()
    I, cI, prI = infoset_sum(C.R, 36, [], rng)
    print(head + f"; Index(E) = {I} ({cI} candidates, {time.time() - t0:.0f}s)", flush=True)
    ok = C.self_dual() and is_aut(g, C) and morder(g) == 12 and mpow(g, 6) == mneg(36) and I == index
    for name, S, Rexp in systems:
        stable, stabs, pairfix, nplace, invTL = block_report(G, S, PL, TL)
        t0 = time.time()
        R, cnt, prof = infoset_sum(C.R, 36, S, rng)
        tw = twined_data(C, h, S)
        print(f"2   σ_{name} (b = {len(S)}): G-stable with split pairs {stable}, |stabiliser| {sorted(set(stabs))}, "
              f"stabiliser fixes both pairs {all(pairfix)}, invariant placements per block {sorted(set(nplace))}, "
              f"Lean T_L invariant {sorted(set(invTL))}, (★) {block_report.star}, step-1 placements {block_report.p2}, split-respecting orderings with T_L invariant {block_report.lean_orders}/8; R_σ(E) = {R} (information set: {prof[0]} singletons, block "
              f"profile {prof[1]}, {cnt} candidates, {time.time() - t0:.0f}s)", flush=True)
        print(f"2   σ_{name}: D = π(E)^⊥ has length {tw['N']}, rank π(E) = {tw['rank_pi']}, dim D = {tw['dimD']} "
              f"(expansions in E^h: {tw['expand_ok']}); collapsed system σ̄ = {tw['sbar']}; R^h_σ(E) = {tw['Rh']}, "
              f"T_h(E) = {tw['Th']} ({3 ** tw['dimD']} fixed codewords)", flush=True)
        ok &= stable and all(pairfix) and block_report.star and block_report.p2 and R == Rexp and tw['Rh'] == 0 and tw['Th'] == 0 and tw['expand_ok'] \
            and tw['dimD'] + tw['rank_pi'] == tw['N']
    return ok


def seed_q8(rng, PL, TL):
    E = read_code(os.path.join(CODES, "q8chain_len24.txt"))
    C = Code(E, 24)
    J, K = q8_blocks(24)
    G = closure([J, K])
    neg = mneg(24)
    rel = mmul(J, J) == neg and mmul(K, K) == neg and mmul(J, K) == mmul(neg, mmul(K, J))
    stable, stabs, pairfix, nplace, invTL = block_report(G, SIGMA_Q8, PL, TL)
    t0 = time.time()
    Rfull = span_sum(C.R, 24, weight_fn(24, SIGMA_Q8))
    t1 = time.time()
    R, cnt, prof = infoset_sum(C.R, 24, SIGMA_Q8, rng)
    I, cI, _ = infoset_sum(C.R, 24, [], rng)
    print(f"2 Q_8 seed q8chain_len24: self-dual {C.self_dual()}, J, K ∈ Aut {is_aut(J, C) and is_aut(K, C)}, relations "
          f"{rel}, |G| = {len(G)}; σ = {SIGMA_Q8}: G-stable with split pairs {stable}, |stabiliser| {stabs}, "
          f"stabiliser fixes both pairs {pairfix}, invariant placements {nplace} (block 0: {block_report.first}), Lean T_L "
          f"invariant {invTL}, (★) {block_report.star}, step-1 placements {block_report.p2}, split-respecting orderings with T_L invariant {block_report.lean_orders}/8; R_σ(E) = {Rfull} (all 3^12 codewords, {t1 - t0:.0f}s) = {R} (information set: {cnt} candidates); "
          f"Index(E) = {I} ({cI} candidates)", flush=True)
    return (C.self_dual() and rel and stable and Rfull == R == 24 and is_aut(J, C) and is_aut(K, C)
            and block_report.star and block_report.p2)


def seed_q8z3(rng, PL, TL):
    sys.path.insert(0, HERE)
    from mainq_morita import q8_gens, h_gen, code_from_U, omega, happly, h_blocks
    U = read_code(os.path.join(CODES, "q8z3_seed72.U.txt"))
    E = read_code(os.path.join(CODES, "q8z3_seed72.txt"))
    C = Code(E, 72)
    same = Code(code_from_U(U, 18), 72).R == C.R
    lag = len(rref(U)[0]) == 18 and all(omega(a, b) == 0 for a in U for b in U)
    hb = h_blocks(6)
    UC = Code(U, 36)
    hinv = all(UC.contains(happly(hb, u)) for u in U)
    J, K = q8_gens(18)
    h = h_gen(6)
    neg, one = mneg(72), mid(72)
    rel = (mmul(J, J) == neg and mmul(K, K) == neg and mmul(J, K) == mmul(neg, mmul(K, J)) and mpow(h, 3) == one
           and mmul(h, J) == mmul(J, h) and mmul(h, K) == mmul(K, h))
    aut = all(is_aut(x, C) for x in (J, K, h))
    G = closure([J, K, h])
    sigma = [tuple([4 * b, J[0][4 * b]] + [x for x in range(4 * b, 4 * b + 4) if x not in (4 * b, J[0][4 * b])])
             for b in range(6)]
    stable, stabs, pairfix, nplace, invTL = block_report(G, sigma, PL, TL)
    # U-level fixed space: π(U) and U^h (free over F_3[u]/u^3 ⇔ dim U^h = 6)
    Uh = [u for u in nullspace([[(a - b) % 3 for a, b in zip(happly(hb, r), r)] for r in rref(U)[0]], 18)]
    dimUh = len(Uh)
    t0 = time.time()
    tw = twined_data(C, h, sigma)
    print(f"2 Q_8×ℤ/3 seed q8z3_seed72: U Lagrangian {lag}, hU = U {hinv}, dim U^h = {dimUh} (free ⇔ 6); E = F_3²⊗U "
          f"(stored file agrees {same}) self-dual {C.self_dual()}; J, K, h ∈ Aut {aut}; relations {rel}; |G| = {len(G)}; "
          f"σ = {sigma}: G-stable with split pairs {stable}, |stabiliser| {sorted(set(stabs))}, stabiliser fixes both "
          f"pairs {all(pairfix)}, invariant placements per block {sorted(set(nplace))} (block 0: {block_report.first}), "
          f"Lean T_L invariant {sorted(set(invTL))}, (★) {block_report.star}, step-1 placements {block_report.p2}, split-respecting orderings with T_L invariant {block_report.lean_orders}/8", flush=True)
    star_ok = block_report.star and block_report.p2
    print(f"2   fixed code: rank π(E) = {tw['rank_pi']}, dim D = {tw['dimD']} of length {tw['N']} (expansions in E^h "
          f"{tw['expand_ok']}); σ̄ = {tw['sbar']}; R^h_σ(E) = {tw['Rh']}, T_h(E) = {tw['Th']} "
          f"({3 ** tw['dimD']} fixed codewords, {time.time() - t0:.0f}s)", flush=True)
    # the same two numbers on the collapsed code D by information sets (the Lean-sized certificate)
    Dn = tw['N']
    Rb, cnt, prof = infoset_sum(tw['D'], Dn, [tuple(b) for b in tw['sbar']], rng)
    Ib, cI, _ = infoset_sum(tw['D'], Dn, [], rng)
    print(f"2   on D (length {Dn}): R_σ̄(D) = {Rb} ({cnt} candidates), Index(D) = {Ib} ({cI} candidates); "
          f"R_σ(E) at n = 72 would need ≥ 2^36 information-set candidates (48 singletons ⊇ an information set) — "
          f"see Part 6", flush=True)
    return (star_ok and lag and hinv and dimUh == 6 and same and C.self_dual() and aut and rel and stable and tw['Rh'] == 0
            and tw['Th'] == 0 and Rb == 0 and Ib == 0 and tw['expand_ok'])


def part2(PL, TL):
    rng = random.Random(2027)
    return all([seed_J(rng, PL, TL), seed_z12(rng, PL, TL),
                seed_z12(rng, PL, TL, "z12seed_len36_6", (("A6", SIGMA_A6, 24), ("B6", SIGMA_B6, 24)), -24),
                seed_q8(rng, PL, TL), seed_q8z3(rng, PL, TL)])


# ------------------------------------------------------------------ Part 3: split conventions (combinatorics only)
TL_WORDS = None


def split_orders(blk):
    P1, P2 = blk
    for A, B in ((P1, P2), (P2, P1)):
        for o1 in (A, A[::-1]):
            for o2 in (B, B[::-1]):
                yield (tuple(o1), tuple(o2))


def all_local_ok(G, blocks):
    """Every g ∈ G maps every ordered block β onto an ordered block gβ with local map in Mon(T_L)."""
    by = {frozenset(P + Q): P + Q for P, Q in blocks}
    for g in G:
        for P, Q in blocks:
            o = P + Q
            img = by.get(frozenset(g[0][x] for x in o))
            if img is None or not invariant_under(TL_WORDS, [local_map(g, o, img)]):
                return False
    return True


def lean_orders(G, blocks):
    """Orderings of all blocks (within their splits) such that all local maps preserve T_L; orbit by orbit:
    an ordering of a representative good for its stabiliser, then for each other block of the orbit an
    ordering making the map from the representative preserve T_L. None if impossible."""
    key = {frozenset(P + Q): i for i, (P, Q) in enumerate(blocks)}
    out = [None] * len(blocks)
    for i, blk in enumerate(blocks):
        if out[i] is not None:
            continue
        orbit = {}
        for g in G:
            j = key[frozenset(g[0][x] for x in blk[0] + blk[1])]
            orbit.setdefault(j, g)
        done = False
        for o in split_orders(blk):
            St = [g for g in G if {g[0][x] for x in o[0] + o[1]} == set(o[0] + o[1])]
            if not invariant_under(TL_WORDS, [local_map(g, o[0] + o[1], o[0] + o[1]) for g in St]):
                continue
            trial = {i: o}
            for j, g in orbit.items():
                if j == i:
                    continue
                for oj in split_orders(blocks[j]):
                    if invariant_under(TL_WORDS, [local_map(g, o[0] + o[1], oj[0] + oj[1])]):
                        trial[j] = oj
                        break
                else:
                    break
            if len(trial) == len(orbit):
                for j, oj in trial.items():
                    out[j] = oj
                done = True
                break
        if not done:
            return None
    return out


def extend_map(g, mate, n_new):
    p = list(g[0]) + [None] * (n_new - len(g[0]))
    s = list(g[1]) + [None] * (n_new - len(g[1]))
    for x, xs in mate.items():
        p[xs] = mate[p[x]]; s[xs] = s[x]
    return (tuple(p), tuple(s))


def sim_step(n, gens, blocks, conv):
    """One equivariant quadrupling on block data only. blocks: list of ((a, b), (c, d)) (pairs = splits).
    Returns (new n, extended gens, new blocks, size of the refined orbit, all orbit sizes of step-1 blocks)."""
    b = len(blocks)
    mate1 = {}
    for j, (P, Q) in enumerate(blocks):
        for i, x in enumerate(P + Q):
            mate1[x] = n + 4 * j + i
    n1 = n + 4 * b
    g1 = [extend_map(g, mate1, n1) for g in gens]
    step1 = [pr for P, Q in blocks for pr in (P, Q)]           # step-1 block of pair (x, y) = {x, x*, y, y*}
    mate2 = {}
    for r, (x, y) in enumerate(step1):
        for i, z in enumerate((x, mate1[x], y, mate1[y])):
            mate2[z] = n1 + 4 * r + i
    n2 = n1 + 8 * b
    g2 = [extend_map(g, mate2, n2) for g in g1]
    if TL_WORDS is not None:
        G1 = closure(g1)
        okb = all_local_ok(G1, blocks)
        s1 = [((x, mate1[x]), (y, mate1[y])) for x, y in step1]          # Existence.lean's r₁ labels (b, s)
        oks = all_local_ok(G1, s1)
        sim_step.lean_ok = sim_step.lean_ok and okb and oks
    G2 = closure(g2)
    keys = [frozenset((x, mate1[x], y, mate1[y])) for x, y in step1]
    idx = {k: r for r, k in enumerate(keys)}
    orbits, seen = [], set()
    for r, k in enumerate(keys):
        if r in seen:
            continue
        o = {idx[frozenset(g[0][z] for z in k)] for g in G2}
        seen |= o; orbits.append(sorted(o))
    orb = min(orbits, key=len)                                 # refine a smallest orbit
    new = []
    for r in orb:
        x, y = step1[r]
        xs, ys = mate1[x], mate1[y]
        if conv == "lean":      # split {x, x*} | {y, y*}; new blocks {x, x**, x*, x***} with pairs {x, x**}, {x*, x***}
            new += [((x, mate2[x]), (xs, mate2[xs])), ((y, mate2[y]), (ys, mate2[ys]))]
        else:                   # pair-stable split {x, y} | {x*, y*}; new blocks {x, y, x**, y**}, {x*, y*, x***, y***}
            new += [((x, y), (mate2[y], mate2[x])), ((xs, ys), (mate2[ys], mate2[xs]))]   # second pair reversed
    return n2, g2, new, len(orb), sorted(len(o) for o in orbits)


def stab_info(gens, blocks):
    G = closure(gens)
    out = set()
    for P, Q in blocks:
        B = set(P + Q)
        St = [g for g in G if {g[0][x] for x in B} == B]
        fix = all({g[0][x] for x in P} == set(P) for g in St)
        out.add((len(St), fix))
    return sorted(out)


def simulate(name, n, gens, blocks, conv, kmax):
    ks, trail = [], []
    while n + 12 * len(blocks) <= 12 * kmax:
        b = len(blocks)
        n, gens, blocks, osz, allo = sim_step(n, gens, blocks, conv)
        ks.append(n // 12)
        trail.append((n // 12, b, osz, tuple(stab_info(gens, blocks))))
    return ks, trail


def part3():
    KMAX = 100
    sys.path.insert(0, HERE)
    from mainq_morita import q8_gens, h_gen
    g = signed_cycles(36, 6)
    Jq, Kq = q8_blocks(24)
    Jm, Km = q8_gens(18)
    hm = h_gen(6)
    tup = lambda S: [((a, b), (c, d)) for a, b, c, d in S]
    chains = {
        "J": (12, [J_GOLAY], [((0, 1), (2, 3))], {1}),
        "Z12-A": (36, [g], tup(SIGMA_A), None),
        "Z12-B": (36, [g], tup(SIGMA_B), None),
        "Z12-A6": (36, [g], tup(SIGMA_A6), None),
        "Z12-B6": (36, [g], tup(SIGMA_B6), None),
        "Q8": (24, [Jq, Kq], tup(SIGMA_Q8), None),
        "Q8xZ3": (72, [Jm, Km, hm], [((4 * b, Jm[0][4 * b]), tuple(x for x in range(4 * b, 4 * b + 4)
                                                                  if x not in (4 * b, Jm[0][4 * b]))) for b in range(6)], None),
    }
    need = {"J": {4}, "Z12": {3, 6, 12}, "Q8": {8}, "Q8xZ3": {24}}
    global TL_WORDS
    TL_WORDS = frozenset(tuple((a * x + b * y) % 3 for x, y in zip(*TETRA)) for a in range(3) for b in range(3))
    lean_all = True
    for name, (n, gens, blocks, extra) in chains.items():
        G0 = closure(gens)
        ordered = lean_orders(G0, blocks)
        sim_step.lean_ok = ordered is not None and all_local_ok(G0, ordered)
        nn, gg, bb = n, gens, ordered
        for _ in range(3):
            nn, gg, bb, _, _ = sim_step(nn, gg, bb, "stable")
        print(f"3 [transposed, Lean labels] {name}: stage-0 blocks reordered to {ordered[:2]}{' …' if len(ordered) > 2 else ''}; "
              f"every local map g: β → gβ (all g ∈ G, all blocks; and all step-one blocks in r₁ labels) lies in "
              f"Mon(T_L) for 3 steps (σ″-blocks ordered (x, y, y**, x**)): {sim_step.lean_ok}", flush=True)
        lean_all &= sim_step.lean_ok == (name != "Z12-B")          # σ_B pairs J-pairs of different offsets
    TL_WORDS = None
    ok = True
    for conv in ("stable", "lean"):
        reached = {}
        for name, (n, gens, blocks, extra) in chains.items():
            ks, trail = simulate(name, n, gens, blocks, conv, KMAX)
            reached[name] = set(ks)
            print(f"3 [{conv}] {name}: (k, b before the step, refined orbit size, (|stab|, fixes pairs) of the new "
                  f"blocks) = {trail[:5]}{' …' if len(trail) > 5 else ''}", flush=True)
        # coverage of the Main Question classes up to KMAX
        cov = {}
        cov["J"] = reached["J"] | {1}
        cov["Z12"] = reached["Z12-A"] | reached["Z12-B"] | {3}
        cov6 = reached["Z12-A6"] | reached["Z12-B6"] | {3}
        cov["Q8"] = reached["Q8"]
        cov["Q8xZ3"] = reached["Q8xZ3"]
        miss = {}
        for key, ms in need.items():
            want = [k for k in range(1, KMAX + 1) if gcd(k, 24) in ms]
            miss[key] = [k for k in want if k not in cov[key]]
        miss6 = [k for k in range(1, KMAX + 1) if gcd(k, 24) in need["Z12"] and k not in cov6]
        print(f"3 [{conv}] classes needed (gcd(k,24) ∈ set) but not reached for k ≤ {KMAX}: {miss}; "
              f"with the seed-6 systems (A6, B6): {miss6}", flush=True)
        if conv == "stable":
            ok &= all(not v for v in miss.values()) and lean_all and not miss6
        else:
            ok &= bool(miss["Z12"]) and not miss["J"] and not miss["Q8"] and not miss["Q8xZ3"]
    return ok


# ------------------------------------------------------------------ Part 4: the orbit-weighted twined lemma
def part4(trials=24):
    sys.path.insert(0, HERE)
    from mainq_equivariant import quad_eq
    from mainq_q8chain import rand_group_code
    rng = random.Random(11)
    n = 36
    h = (tuple(3 * (i // 3) + (i % 3 + 1) % 3 for i in range(n)), (1,) * n)
    done = agree = nonzero = differ = 0
    vals = []
    while done < trials:
        E = rand_group_code([h], n, rng)
        if E is None:
            continue
        C = Code(E, n)
        if not (C.self_dual() and is_aut(h, C)):
            continue
        nb = 1 + done % 2
        tri = list(range(12)); rng.shuffle(tri)
        blocks = []
        for j in range(nb):
            t = tri[4 * j:4 * j + 4]
            base = [3 * x + rng.randrange(3) for x in t]
            for r in range(3):
                blocks.append(tuple(3 * (y // 3) + (y % 3 + r) % 3 for y in base))
        tw = twined_data(C, h, blocks, fast=True)
        rows, nn, newb, gens2 = quad_eq(E, n, blocks, [h], refine="orbit0")
        Q = Code(rows, nn)
        tq = twined_data(Q, gens2[0], newb, fast=True)
        naive = tw["naive"]
        good = Q.self_dual() and is_aut(gens2[0], Q) and tq["Th"] == tw["Rh"] and tq["Rh"] == tw["Rh"]
        done += 1; agree += good; nonzero += tw["Rh"] != 0; differ += naive != tw["Rh"]
        vals.append((tw["Rh"], tq["Th"], tq["Rh"], naive))
    print(f"4 {done} random h-invariant self-dual codes of length 36 (h = twelve 3-cycles), σ = 1 or 2 h-orbits of blocks: "
          f"T_h(Q_σ E) = R^h_σ(E) = R^h_σ″(Q_σ E) in {agree}/{done} (nonzero in {nonzero}); the naive restriction of R_σ "
          f"to E^h (λ per block, i.e. λ³ per orbit) differs from R^h_σ in {differ}/{done}; sample (R^h_σ(E), T_h(Q), R^h_σ″(Q), naive) = {vals[:6]}",
          flush=True)
    return agree == done and nonzero > 0 and differ > 0


# ------------------------------------------------------------------ Part 5: the generator files
def all_parses(s, n, cap=10 ** 5):
    used, out, sols = [False] * n, [], []

    def rec(i):
        if len(sols) >= cap:
            return
        if i == len(s):
            if len(out) == n:
                sols.append(tuple(out))
            return
        for L in (1, 2, 3):
            if i + L <= len(s) and (L == 1 or s[i] != "0"):
                v = int(s[i:i + L])
                if v < n and not used[v]:
                    used[v] = True; out.append(v)
                    rec(i + L)
                    used[v] = False; out.pop()
    sys.setrecursionlimit(10000)
    rec(0)
    return sols


def part5():
    ok = True
    files = [(f"jchain_len{n}", n, "J") for n in (24, 48, 72, 96, 120, 144)] + \
            [(f"z12chain_len{n}", n, "g") for n in (72, 108, 144)]
    for stem, n, kind in files:
        C = Code(read_code(os.path.join(CODES, stem + ".txt")), n)
        with open(os.path.join(CODES, f"{stem}.{kind}.txt")) as fh:
            perm_s, sign_s = [ln.strip() for ln in fh if ln.strip()]
        s = tuple(1 if ch == "1" else -1 for ch in sign_s)
        sols = all_parses(perm_s, n)
        rel = []
        for p in sols:
            g = (p, s)
            if kind == "J":
                good = mmul(g, g) == mneg(n)
            else:
                good = mpow(g, 6) == mneg(n) and morder(g) == 12
            rel.append(good)
        aut = [is_aut((p, s), C) if r else False for p, r in zip(sols, rel)]
        first = sols[0] if sols else None
        print(f"5 {stem}.{kind}.txt: {len(perm_s)} digits for n = {n}: {len(sols)} parses into a permutation; "
              f"{sum(rel)} satisfy {'J² = −1' if kind == 'J' else 'ord 12, g⁶ = −1'}; {sum(aut)} of those are "
              f"automorphisms of the code; the first (backtracking) parse is one of them: {bool(sols) and aut[0]}",
              flush=True)
        ok &= bool(sols) and aut[0]
    return ok


# ------------------------------------------------------------------ Part 6: the n = 72 certificate (Rust)
def part6():
    if not os.path.exists(BIN):
        print("6 Rust binary not built; skipped", flush=True)
        return True
    tmp = tempfile.mkdtemp(prefix="blueprint_")
    U = read_code(os.path.join(CODES, "q8z3_seed72.U.txt"))
    uf, sf = os.path.join(tmp, "u.txt"), os.path.join(tmp, "sys.txt")
    with open(uf, "w") as fh:
        fh.write("\n".join("".join(map(str, r)) for r in U) + "\n")
    with open(sf, "w") as fh:
        fh.write("-\n0,1,2,3,4,5\n")
    t0 = time.time()
    pr = subprocess.run([BIN, "sl2words", uf, "0", sf], capture_output=True, text=True, check=True)
    vals = {int(a): int(b) for _, a, b in (ln.split() for ln in pr.stdout.splitlines() if ln.startswith("R "))}
    planes = int(next(ln for ln in pr.stderr.splitlines() if ln.startswith("planes=")).split("=")[1])
    dt = time.time() - t0
    r = 18
    print(f"6 sl2words on the Q_8×ℤ/3 seed (r = {r} Q_8-orbits): Index(E) = {vals[0]}, R_σ(E) = {vals[1]} "
          f"(σ = orbit blocks 0..5); {planes} normalised SL_2-words (good planes) enumerated; the first rows x_1 range "
          f"over an affine space of dimension r − 2 = {r - 2} (3^{r - 2} = {3 ** (r - 2)} points, pruned); "
          f"{dt:.0f}s wall-clock", flush=True)
    return vals[1] == 24 and vals[0] == -1608


# ------------------------------------------------------------------ Part 7: offset-matched ℤ/12 systems (§3.3)
def part7():
    """Over the 8 committed ℤ/12 seeds: the offset-matched systems (both J-pairs of every block have the same
    offset i in their 6-cycles, Lemma 2.7) with R^h_σ = 0 and |R_σ| = 24."""
    g = signed_cycles(36, 6)
    h = mpow(g, 4)
    jp = lambda c, i: (6 * c + i, 6 * c + i + 3)
    S3 = []
    for c1, c2 in itertools.combinations(range(6), 2):
        for d in range(3):
            orb = [jp(c1, 0) + jp(c2, d)]
            for _ in range(2):
                orb.append(tuple(h[0][x] for x in orb[-1]))
            S3.append((c1, c2, d, orb))
    m3 = [s for s in S3 if s[2] == 0]
    S6 = [(a, b) for a, b in itertools.combinations(S3, 2) if not ({a[0], a[1]} & {b[0], b[1]})]
    m6 = [(a, b) for a, b in S6 if a[2] == 0 and b[2] == 0]
    print(f"7 ℤ/12 systems: {len(S3)} three-block, {len(m3)} offset-matched; {len(S6)} six-block, {len(m6)} "
          f"offset-matched", flush=True)
    rng = random.Random(1)
    found = {}
    for sd in range(1, 9):
        C = Code(read_code(os.path.join(CODES, f"z12seed_len36_{sd}.txt")), 36)
        hits = {3: [], 6: []}
        for b, systems in ((3, [s[3] for s in m3]), (6, [a[3] + c[3] for a, c in m6])):
            for bl in systems:
                if twined_data(C, h, bl)["Rh"] != 0:
                    continue
                R = infoset_sum(C.R, 36, bl, rng, tries=20)[0]
                if abs(R) == 24:
                    hits[b].append((R, bl))
        I = infoset_sum(C.R, 36, [], rng, tries=3)[0]
        found[sd] = (len(hits[3]), len(hits[6]))
        print(f"7 seed {sd}: Index {I}; matched b = 3 with R^h = 0, |R| = 24: {len(hits[3])} {hits[3][:1]}; "
              f"matched b = 6: {len(hits[6])} {hits[6][:1]}", flush=True)
    both = [sd for sd, (a, b) in found.items() if a and b]
    print(f"7 seeds with both a matched 3-block and a matched 6-block system: {both}", flush=True)
    return both == [6]


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        t0 = time.time()
        ok1, PL, TL = part1()
        ok2 = part2(PL, TL)
        ok3 = part3()
        ok4 = part4()
        ok5 = part5()
        ok6 = part6()
        ok7 = part7()
        print(f"parts pass: 1 {ok1}, 2 {ok2}, 3 {ok3}, 4 {ok4}, 5 {ok5}, 6 {ok6}, 7 {ok7}; "
              f"all {all([ok1, ok2, ok3, ok4, ok5, ok6, ok7])} "
              f"[{time.time() - t0:.0f}s]", flush=True)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
