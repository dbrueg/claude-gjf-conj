"""Independent re-check of the Conj 1.4 proof as written in paper/index24.tex and paper/divisibility.tex
(review of 2026-09-28, paper/review-2026-09-28.md).

Written from the papers' definitions only; it imports nothing from the other scripts in this directory.
Vectors over F_3 are bit-sliced pairs (A, B) of integer bitmasks: A = positions equal to 1, B = positions
equal to 2.

Part 1: the two local identities (Lemma A = doubling, Lemma B = refinement) for every u in F_3^4, all 8
        tetracode placements (the monomial images of T), and all 3 pair splittings.
Part 2: the main lemma (Index(Q_σ E) = R_σ(E), R_σ''(Q_σ E) = R_σ(E) for every subset of refined
        step-one blocks), with Q_σ built literally as in Definition 6 of paper/index24.tex, random
        placements and splits, on random self-dual E of length 12 (b = 1, n = 24) and length 8 (b = 1,
        n = 20); every codeword of Q_σ(E) is enumerated. Also self-duality of Q_σ(E).
Part 3: the base facts from the Golay matrix printed in paper/index24.tex: self-dual, Index = +24
        exactly, R_σ1 = R_σ2 = 24, and the distributions over all single blocks and all 2-block systems.
Part 4: the automorphism J printed in paper/main-question.tex §4.2 (gcd(k,24) = 4) is in Aut(G) with
        J² = −1, and the J-invariant tetracode printed in §3 is a tetracode and J-invariant.
Part 5: the finite divisibility proof (route C): G_ij(C) = 0 for all i < j, and 8 | Index, 3 | Index,
        on random self-dual codes of length 12 and 24 (all codewords enumerated).
"""
import itertools
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = []


def log(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


# ---------------------------------------------------------------- F_3 bit-sliced arithmetic
def vec(lst):
    A = B = 0
    for i, v in enumerate(lst):
        v %= 3
        if v == 1:
            A |= 1 << i
        elif v == 2:
            B |= 1 << i
    return (A, B)


def unvec(x, n):
    A, B = x
    return [1 if A >> i & 1 else (2 if B >> i & 1 else 0) for i in range(n)]


def vadd(x, y):
    a1, b1 = x
    a2, b2 = y
    z1 = ~(a1 | b1)
    z2 = ~(a2 | b2)
    s1 = (z1 & a2) | (a1 & z2) | (b1 & b2)
    s2 = (z1 & b2) | (b1 & z2) | (a1 & a2)
    return (s1, s2)


def vneg(x):
    return (x[1], x[0])


def vscale(c, x):
    c %= 3
    return (0, 0) if c == 0 else (x if c == 1 else vneg(x))


def pc(x):
    return bin(x).count("1")


def vdot(x, y):
    """Standard form in F_3: sum of products. 1*1 = 2*2 = 1, 1*2 = 2."""
    a1, b1 = x
    a2, b2 = y
    plus = pc(a1 & a2) + pc(b1 & b2)
    minus = pc(a1 & b2) + pc(b1 & a2)
    return (plus - minus) % 3


def rref(rows, n):
    rows = [list(r) for r in rows]
    out, col = [], 0
    for col in range(n):
        piv = next((r for r in rows if r[col] % 3), None)
        if piv is None:
            continue
        rows.remove(piv)
        inv = 1 if piv[col] % 3 == 1 else 2
        piv = [(inv * v) % 3 for v in piv]
        rows = [[(a - r[col] * b) % 3 for a, b in zip(r, piv)] for r in rows]
        out = [[(a - r[col] * b) % 3 for a, b in zip(r, piv)] for r in out]
        out.append(piv)
    return out


def rank(rows, n):
    return len(rref(rows, n))


def codewords(rows, n):
    """All codewords (bit-sliced) of the span of rows (rows must be independent)."""
    words = [(0, 0)]
    for r in rows:
        v = vec(r)
        w2 = vneg(v)
        words = [y for x in words for y in (x, vadd(x, v), vadd(x, w2))]
    return words


def is_self_dual(rows, n):
    if rank(rows, n) != n // 2 or 2 * len(rows) != n:
        return False
    vs = [vec(r) for r in rows]
    return all(vdot(a, b) == 0 for a in vs for b in vs)


# ---------------------------------------------------------------- the weights of the papers
LAM = (0, -2, 0, 0, 1)


def phi(v):
    return (0, -1, 1)[v % 3]


def f_bits(x, mask):
    """f restricted to the coordinates of mask: prod phi, i.e. 0 unless all nonzero, else (-1)^{#1s}."""
    A, B = x
    if (A | B) & mask != mask:
        return 0
    return -1 if pc(A & mask) & 1 else 1


def R_sigma(words, n, blocks):
    """R_σ = sum_c prod_{singletons} phi(c_i) prod_{β} λ(|supp c ∩ β|)."""
    bm = [sum(1 << i for i in b) for b in blocks]
    sing = (1 << n) - 1
    for m in bm:
        sing &= ~m
    tot = 0
    for x in words:
        s = f_bits(x, sing)
        if s == 0:
            continue
        supp = x[0] | x[1]
        for m in bm:
            s *= LAM[pc(supp & m)]
            if s == 0:
                break
        tot += s
    return tot


def index_count(words, n):
    """GJF's definition literally: #even − #odd maximal words, parity = number of 1s."""
    full = (1 << n) - 1
    ev = od = 0
    for A, B in words:
        if (A | B) == full:
            if pc(A) % 2 == 0:
                ev += 1
            else:
                od += 1
    return ev - od, ev, od


# ---------------------------------------------------------------- tetracode and placements
T_ROWS = [[1, 1, 1, 0], [0, 1, 2, 1]]            # paper/index24.tex §2


def span_list(rows, n):
    return [tuple(unvec(w, n)) for w in codewords(rows, n)]


T_WORDS = span_list(T_ROWS, 4)


def placements():
    """The distinct monomial images of T in F_3^4 (there are 8)."""
    seen = set()
    out = []
    for perm in itertools.permutations(range(4)):
        for signs in itertools.product((1, 2), repeat=4):
            img = frozenset(tuple((signs[i] * w[i]) % 3 for i in perm) for w in T_WORDS)
            if img not in seen:
                seen.add(img)
                out.append(sorted(img))
    return out


PLACE = placements()
SPLITS = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]


def psi(a, b):
    return phi(a + b) * phi(a - b)


def kappa(a, b):
    return ((a + b) % 3 != 0) + ((a - b) % 3 != 0)


def part1():
    log("Part 1: local identities")
    assert len(PLACE) == 8, len(PLACE)
    nA = nB = 0
    for P in PLACE:
        assert len(P) == 9
        for u in itertools.product(range(3), repeat=4):
            wt = sum(1 for v in u if v)
            a = sum(psi(u[0], t[0]) * psi(u[1], t[1]) * psi(u[2], t[2]) * psi(u[3], t[3]) for t in P)
            assert a == LAM[wt], (P, u, a)
            nA += 1
            for (p, q), (r, s) in SPLITS:
                bsum = sum(LAM[kappa(u[p], t[p]) + kappa(u[q], t[q])] *
                           LAM[kappa(u[r], t[r]) + kappa(u[s], t[s])] for t in P)
                assert bsum == LAM[wt], (P, u, (p, q, r, s), bsum)
                nB += 1
    log(f"  Lemma A: {nA} cases (8 placements x 81 u), all equal λ(wt u)")
    log(f"  Lemma B: {nB} cases (8 placements x 81 u x 3 splits), all equal λ(wt u)")


# ---------------------------------------------------------------- partial quadrupling, literally
def hadamard_rows(rows, pairs):
    """Apply (x_i, x_j) -> (x_i + x_j, x_i - x_j) on each pair (i, j)."""
    out = []
    for r in rows:
        r = list(r)
        for i, j in pairs:
            a, b = r[i], r[j]
            r[i], r[j] = (a + b) % 3, (a - b) % 3
        out.append(r)
    return out


def Q_sigma(E, m, blocks, rng):
    """Definition 6 of paper/index24.tex. blocks: list of 4-tuples (p, q, r, s) with split {p,q},{r,s}.
    Placements of T on beta* and B** chosen at random; step-one blocks split at random.
    Returns (rows, n, step-one blocks as 4-tuples with their chosen splits, star maps)."""
    b = len(blocks)
    n1 = m + 4 * b
    n = m + 12 * b
    star = {}
    for j, blk in enumerate(blocks):
        for t, i in enumerate(blk):
            star[i] = m + 4 * j + t
    rows = [list(r) + [0] * (12 * b) for r in E]
    # step 1: a copy of T on beta* (coordinates in the order of the block, random placement)
    for j, blk in enumerate(blocks):
        P = rng.choice(PLACE)
        basis = rref([list(w) for w in P], 4)
        for bv in basis:
            r = [0] * n
            for t, i in enumerate(blk):
                r[star[i]] = bv[t]
            rows.append(r)
    rows = hadamard_rows(rows, [(i, star[i]) for blk in blocks for i in blk])
    step1 = []
    for p, q, r_, s in blocks:
        for B in ((p, star[p], q, star[q]), (r_, star[r_], s, star[s])):
            B = list(B)
            rng.shuffle(B)                      # a random split of the step-one block
            step1.append(tuple(B))
    dstar = {}
    for j, B in enumerate(step1):
        for t, y in enumerate(B):
            dstar[y] = n1 + 4 * j + t
    for j, B in enumerate(step1):
        P = rng.choice(PLACE)
        basis = rref([list(w) for w in P], 4)
        for bv in basis:
            r = [0] * n
            for t, y in enumerate(B):
                r[dstar[y]] = bv[t]
            rows.append(r)
    rows = hadamard_rows(rows, [(y, dstar[y]) for B in step1 for y in B])
    return rows, n, step1, dstar


def random_self_dual(m, rng, steps=40):
    """Random Kneser walk from a sum of tetracodes."""
    rows = []
    for j in range(m // 4):
        for tr in T_ROWS:
            r = [0] * m
            r[4 * j:4 * j + 4] = tr
            rows.append(r)
    for _ in range(steps):
        C = set(span_list(rows, m))
        while True:
            x = [rng.randrange(3) for _ in range(m)]
            if tuple(x) in C or sum(v * v for v in x) % 3:
                continue
            break
        xv = vec(x)
        # C ∩ x^perp, then add x
        vs = [vec(r) for r in rows]
        piv = next(k for k, v in enumerate(vs) if vdot(v, xv) != 0)
        pv = vs[piv]
        new = []
        for k, v in enumerate(vs):
            if k == piv:
                continue
            d = vdot(v, xv)
            if d:
                c = (-d * (1 if vdot(pv, xv) == 1 else 2)) % 3   # v + c*pv ⟂ x
                v = vadd(v, vscale(c, pv))
            new.append(unvec(v, m))
        rows = rref(new + [x], m)
        assert is_self_dual(rows, m)
    return rows


def part2(rng):
    log("Part 2: main lemma (Lemma 8 of paper/index24.tex) by enumeration")
    cases = [(12, 1, 30), (8, 1, 20)]
    for m, b, reps in cases:
        ok = 0
        nonzero = 0
        for _ in range(reps):
            E = random_self_dual(m, rng)
            coords = list(range(m))
            rng.shuffle(coords)
            blocks = [tuple(coords[4 * j:4 * j + 4]) for j in range(b)]
            Ew = codewords(E, m)
            R = R_sigma(Ew, m, [set(bl) for bl in blocks])
            rows, n, step1, dstar = Q_sigma(E, m, blocks, rng)
            assert is_self_dual(rows, n), "Q_sigma(E) not self-dual"
            Qw = codewords(rref(rows, n), n)
            idx = sum(f_bits(x, (1 << n) - 1) for x in Qw)
            assert idx == R, (idx, R)
            # every subset of step-one blocks refined, with the split chosen in Q_sigma
            for sub in itertools.product((0, 1), repeat=len(step1)):
                sig2 = []
                for flag, B in zip(sub, step1):
                    if flag:
                        y1, y2, y3, y4 = B
                        sig2 += [{y1, dstar[y1], y2, dstar[y2]}, {y3, dstar[y3], y4, dstar[y4]}]
                assert R_sigma(Qw, n, sig2) == R, (sub, R)
            ok += 1
            nonzero += R != 0
        log(f"  m = {m}, b = {b}: {ok}/{reps} random (E, σ, placements, splits): Q_σ(E) self-dual, "
            f"Index(Q_σE) = R_σ(E) and R_σ''(Q_σE) = R_σ(E) for all {2 ** (2 * b)} choices of σ''; "
            f"R ≠ 0 in {nonzero} cases")


# ---------------------------------------------------------------- Golay (paper/index24.tex §4)
GOLAY_PAPER = [
    [1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1],
    [0, 1, 0, 0, 0, 0, 2, 0, 1, 2, 2, 1],
    [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 2, 2],
    [0, 0, 0, 1, 0, 0, 2, 2, 1, 0, 1, 2],
    [0, 0, 0, 0, 1, 0, 2, 2, 2, 1, 0, 1],
    [0, 0, 0, 0, 0, 1, 2, 1, 2, 2, 1, 0],
]


def part3():
    log("Part 3: the Golay base (paper/index24.tex Prop. 10)")
    n = 12
    assert is_self_dual(GOLAY_PAPER, n)
    W = codewords(GOLAY_PAPER, n)
    idx, ev, od = index_count(W, n)
    wd = {}
    for x in W:
        w = pc(x[0] | x[1])
        wd[w] = wd.get(w, 0) + 1
    log(f"  self-dual; weight distribution {dict(sorted(wd.items()))}; even {ev}, odd {od}, Index = {idx}")
    assert (idx, ev, od) == (24, 24, 0)
    r1 = R_sigma(W, n, [{0, 1, 2, 3}])
    r2 = R_sigma(W, n, [{0, 1, 2, 3}, {4, 5, 6, 8}])
    log(f"  R_σ1 = {r1}, R_σ2 = {r2} (paper: 24, 24)")
    assert r1 == r2 == 24
    d1 = {}
    for bl in itertools.combinations(range(n), 4):
        r = R_sigma(W, n, [set(bl)])
        d1[r] = d1.get(r, 0) + 1
    log(f"  all {sum(d1.values())} single blocks: {dict(sorted(d1.items()))}")
    d2 = {}
    for b1 in itertools.combinations(range(n), 4):
        rest = [i for i in range(n) if i not in b1]
        for b2 in itertools.combinations(rest, 4):
            if b2 < b1:
                continue
            r = R_sigma(W, n, [set(b1), set(b2)])
            d2[r] = d2.get(r, 0) + 1
    log(f"  all {sum(d2.values())} two-block systems: {dict(sorted(d2.items()))}")
    return W


def mono(perm, signs, x):
    """(g x)_{perm[i]} = signs[i] x_i on a list x."""
    y = [0] * len(x)
    for i, (p, s) in enumerate(zip(perm, signs)):
        y[p] = (s * x[i]) % 3
    return y


def part4(W):
    log("Part 4: J of paper/main-question.tex §4.2 and the J-invariant tetracode of §3")
    n = 12
    perm = [1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10]
    sg = "-+-++--++--+"
    signs = [1 if c == "+" else -1 for c in sg]
    words = {tuple(unvec(x, n)) for x in W}
    assert all(tuple(mono(perm, signs, list(w))) in words for w in words), "J not in Aut(G)"
    Jsq_ok = all(mono(perm, signs, mono(perm, signs, list(w))) == [(-v) % 3 for v in w] for w in words)
    e = [[1 if i == j else 0 for i in range(n)] for j in range(n)]
    Jsq_basis = all(mono(perm, signs, mono(perm, signs, v)) == [(-a) % 3 for a in v] for v in e)
    log(f"  J ∈ Aut(G): yes; J² = −1 on F_3^12: {Jsq_basis}")
    assert Jsq_basis and Jsq_ok
    r = R_sigma(W, n, [{0, 1, 2, 3}])
    log(f"  R_β(G) for β = {{0,1}}⊔{{2,3}}: {r} (paper: 24)")
    # J(e0)=e1, J(e1)=-e0, J(e2)=e3, J(e3)=-e2 on a block; tetracode <(1,1,1,0),(0,1,2,2)>
    P = span_list([[1, 1, 1, 0], [0, 1, 2, 2]], 4)
    Pset = set(P)
    wts = sorted(sum(1 for v in w if v) for w in P)
    selfdual = is_self_dual([[1, 1, 1, 0], [0, 1, 2, 2]], 4)
    Jb = lambda x: [(-x[1]) % 3, x[0] % 3, (-x[3]) % 3, x[2] % 3]
    inv = all(tuple(Jb(list(w))) in Pset for w in P)
    log(f"  <(1,1,1,0),(0,1,2,2)>: weights {wts}, self-dual {selfdual}, J-invariant {inv}")
    assert selfdual and inv and wts == [0] + [3] * 8


# ---------------------------------------------------------------- route C of paper/divisibility.tex
def part5(rng):
    log("Part 5: route C (signed 2-design) on random self-dual codes")
    for m, reps in ((12, 20), (24, 4)):
        nz = 0
        for _ in range(reps):
            C = random_self_dual(m, rng, steps=30 if m == 12 else 60)
            W = codewords(C, m)
            full = (1 << m) - 1
            maxw = [x for x in W if (x[0] | x[1]) == full]
            idx = sum(-1 if pc(x[0]) & 1 else 1 for x in maxw)
            # G_ij = sum_{maximal x} f(x) phi(x_i) phi(x_j)
            for i in range(m):
                for j in range(i + 1, m):
                    g = 0
                    for A, B in maxw:
                        s = -1 if pc(A) & 1 else 1
                        pi = -1 if A >> i & 1 else 1
                        pj = -1 if A >> j & 1 else 1
                        g += s * pi * pj
                    assert g == 0, (m, i, j, g)
            assert idx % 24 == 0, idx
            nz += idx != 0
        log(f"  m = {m}: {reps} codes, G_ij(C) = 0 for all i < j and 24 | Index; Index ≠ 0 in {nz}")


def main():
    t0 = time.time()
    rng = random.Random(20260928)
    part1()
    part2(rng)
    W = part3()
    part4(W)
    part5(rng)
    log(f"all checks passed ({time.time() - t0:.0f} s)")
    with open(os.path.join(HERE, "review_conj14_check.log"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
