"""Check of the explicit claims of paper/minimal-index.tex (Paper II, the vertex-algebra side), 2026-10-10.

The code data (Golay matrix, J, K, E36, U with the Morita coordinates) are parsed from paper/conj14.tex by
conj14_paper_check.parse_tex, so the two papers are checked against the same printed data.

Parts (paper numbering):
 1 §2     Prop 2.1(4): per-coordinate minima of the Ramond momenta, so ground states <-> maximal codewords with
          parity f(w) (and the count on Golay); Lemma 2.2: <chi,(1-g)chi> = 6 N_-(g); (1): g^j = -1 iff every
          signed cycle has length l | j, j/l odd, sigma = -1 (all of Mon(4), random elements of Mon(12)); the two
          expressions for rho_g (exact).
 2 §2.5   Lemma 2.4(2): the S T^L S^-1 eigenvalue of Z(1,g)/Z(1,1) for Fer(2) rotated by 2 pi r/m is
          exp(2 pi i r^2/m'), numerically for m = 2..12 and all r; Lemma 2.4(1): the orders m'.
 3 §3     Prop 2.3 (ch V(g) = S-transform of 1/eta_g) and Prop 3.2 (eigenvalue exp(2 pi i L rho_g)) on the eta
          quotients of the four even element types (n = 12, 24); Prop 3.3 on Theta_{Lambda^h}/eta(3 tau)^{n/3} for an
          order-3 automorphism without fixed coordinate of the Golay code (k = 1: eigenvalue exp(4 pi i/3)) and for
          the shift on GJF's E36 (k = 3: eigenvalue 1); Corollary 3.4's table for k = 1..48 (exact).
 4 §4.1   H^1, H^2 of Q8 with F2 coefficients from cochains (dims 2, 2), and the order-16 subgroup of Prop 4.2.
 5 §4.2-3 Lemma 4.4(3): Pin lifts of J, K in Cl(4) on every Q8-orbit of coordinates of the Golay code and of E72
          (even, unique up to scalars, exactly four genuine linearisations rho_2 + 2 psi), and on the whole spinor
          module of Cl(12) for Golay (traces 8 psi(x), 0 at -1); Lemma 4.5 numerically (n = 12, 24, 48); Prop 4.6:
          the S-defect formula numerically for k = 4, 8 and all four psi, and its zero set (8 | k, psi = 1) exactly.
 6 §4.4   Remark 4.7: Donnelly eta invariants on RP^3, S^3/<i>, S^3/Q8 (exact), and mu = exp(-2 pi i k/8) =
          exp(2 pi i 3k 5/8).
 7 §6     Lemmas 6.1-6.2 on the groups of Table 1 built from the printed data: (i)-(iii), no fixed coordinate off
          {+-1}, eigenvalue multiplicities 2n/m, E_g = n/24 + n/(12 m^2) > n/24; and for every element: Lemma 2.2,
          epsilon = 1 (Prop 3.1), the Frame shapes and anomalies 2k nu_m of Corollary 3.4 (Props 3.2-3.3).
 8 §1, §7 Table 1: 24/gcd(k,24) is the least M with 24 | M k (Hopkins), group orders; Remark 7.1 (reduction).

Usage: python3 minimal_index_paper_check.py   (stdlib only; log: minimal_index_paper_check.log)
"""
import cmath
import itertools
import math
import os
import random
import sys
import time
from fractions import Fraction as Fr

from conj14_paper_check import (parse_tex, TEX, sp_id, sp_neg, sp_mul, sp_inv, sp_apply, closure,
                                fixed_coords, Code)
from review_conj14_check import vec, unvec, pc, codewords, index_count
from review_seed_verify import fixed_subcode

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = []
T0 = time.time()
TWO_PI_I = 2j * math.pi


def log(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.append(s)


def need(cond, what):
    if not cond:
        raise AssertionError(what)


def stamp():
    return f"[{time.time() - T0:.0f}s]"


# ================================================================ q-series
def qpow(tau, x):
    return cmath.exp(TWO_PI_I * tau * x)


def eta(tau):
    q = cmath.exp(TWO_PI_I * tau)
    prod, qn = 1.0, q
    while abs(qn) > 1e-19:
        prod *= 1 - qn
        qn *= q
    return qpow(tau, Fr(1, 24)) * prod


def prod_odd(tau, step, sign, power):
    """prod over odd j of (1 + sign q^(j*step))^power."""
    out, j = 1.0, 1
    while True:
        t = qpow(tau, j * step)
        if abs(t) < 1e-19:
            return out
        out *= (1 + sign * t) ** power
        j += 2


def series(n):
    e = lambda t: eta(t) ** n / eta(2 * t) ** n
    f = lambda t: eta(2 * t) ** (n // 2) / eta(4 * t) ** (n // 2)
    E = lambda t: 2 ** (n / 2) * qpow(t, Fr(n, 48)) * prod_odd(t, Fr(1, 2), -1, -n)
    g = lambda t: 2 ** (n / 4) * qpow(t, Fr(n, 192)) * prod_odd(t, Fr(1, 4), -1, -n // 2)
    F = lambda t: qpow(t, Fr(n, 48)) * prod_odd(t, 1, 1, -n // 2)
    return e, f, E, g, F


def close(a, b, scale=None, tol=1e-9):
    scale = scale if scale is not None else max(abs(a), abs(b), 1e-300)
    return abs(a - b) <= tol * scale


# ================================================================ signed permutations
def signed_cycles(g):
    p, s = g
    seen, out = set(), []
    for i in range(len(p)):
        if i in seen:
            continue
        cyc, j, sig = [], i, 1
        while j not in seen:
            seen.add(j)
            cyc.append(j)
            sig *= s[j]
            j = p[j]
        out.append((len(cyc), sig))
    return out


def frame_shape(g):
    d = {}
    for l, sig in signed_cycles(g):
        if sig == 1:
            d[l] = d.get(l, 0) + 1
        else:
            d[l] = d.get(l, 0) - 1
            d[2 * l] = d.get(2 * l, 0) + 1
    return {k: v for k, v in d.items() if v}


def rho_frame(d):
    return sum(Fr(v, 24) * (k - Fr(1, k)) for k, v in d.items())


def rho_eigen(g):
    """1/4 sum theta(1-theta) over the eigenvalues e^{2 pi i theta}, theta in [0,1)."""
    tot = Fr(0)
    for l, sig in signed_cycles(g):
        for j in range(l):
            th = Fr(2 * j + (1 if sig == -1 else 0), 2 * l)
            tot += th * (1 - th) / 4
    return tot


def eig_mult(g):
    """Multiset of eigenvalue angles theta (Fractions in [0,1))."""
    out = {}
    for l, sig in signed_cycles(g):
        for j in range(l):
            th = Fr(2 * j + (1 if sig == -1 else 0), 2 * l)
            out[th] = out.get(th, 0) + 1
    return out


def order(g):
    n = len(g[0])
    x, k = g, 1
    while x != sp_id(n):
        x = sp_mul(g, x)
        k += 1
    return k


def power(g, j):
    n = len(g[0])
    r = sp_id(n)
    for _ in range(j):
        r = sp_mul(g, r)
    return r


# ================================================================ Part 1: §2
def part1(d, rng):
    log("Part 1 (§2): Ramond ground states (Prop 2.1(4)), Lemma 2.2, (1), rho_g")
    mins = {}
    for r in range(3):
        vals = [(2 * a + 3) ** 2 for a in range(-12, 13) if a % 3 == r]
        m = min(vals)
        mins[r] = (m, sorted(a for a in range(-12, 13) if a % 3 == r and (2 * a + 3) ** 2 == m))
    need(mins == {0: (9, [-3, 0]), 1: (1, [-2]), 2: (1, [-1])}, f"per-coordinate minima {mins}")
    G12 = d["golay"]
    C = Code(G12, 12)
    cnt = par = 0
    for a in itertools.product((-1, -2), repeat=12):
        if C.contains([v % 3 for v in a]):
            cnt += 1
            par += (-1) ** (sum(a) % 2)
    W = codewords(G12, 12)
    idx, ev, od = index_count(W, 12)
    need(cnt == ev + od and par == idx == 24, "Golay ground states")
    # Lemma 2.2 and (1)
    ok = True
    for _ in range(300):
        g = (tuple(rng.sample(range(12), 12)), tuple(rng.choice((1, -1)) for _ in range(12)))
        ok &= maj_number(g) == 6 * sum(1 for v in g[1] if v == -1)
    need(ok, "Lemma 2.2")
    mon4 = [(p, s) for p in itertools.permutations(range(4)) for s in itertools.product((1, -1), repeat=4)]
    samples = mon4 + [(tuple(rng.sample(range(12), 12)), tuple(rng.choice((1, -1)) for _ in range(12)))
                      for _ in range(300)]
    ok21 = True
    for g in samples:
        n = len(g[0])
        for j in range(1, 13):
            lhs = power(g, j) == sp_neg(n)
            rhs = all(j % l == 0 and (j // l) % 2 == 1 and sig == -1 for l, sig in signed_cycles(g))
            ok21 &= lhs == rhs
    need(ok21, "(1)")
    okrho = all(rho_eigen(g) == rho_frame(frame_shape(g)) for g in samples)
    need(okrho, "rho_g identity")
    log(f"  per-coordinate minima of (2a+3)^2: {mins}, so |nu|^2/2 >= n/24 with equality iff all a_i in {{-1,-2}}; "
        f"Golay: {cnt} minimal Ramond momenta, signed count {par} = Index = {idx}; Lemma 2.2 on 300 random g in "
        f"Mon(12); (1) for j <= 12 on all of Mon(4) and 300 random g in Mon(12); rho_g = 1/4 sum theta(1-theta) "
        f"= 1/24 sum d_k (k - 1/k) on the same elements  {stamp()}")


# ================================================================ Part 2: Lemma 2.4
def theta_char(tau, r, m, P=120):
    num = sum(cmath.exp(TWO_PI_I * p * r / m) * cmath.exp(1j * math.pi * tau * p * p) for p in range(-P, P + 1))
    den = sum(cmath.exp(1j * math.pi * tau * p * p) for p in range(-P, P + 1))
    return num, den


def part2():
    log("Part 2 (§2.5): Lemma 2.4, calibration of the multiplier principle")
    worst = 0.0
    for m in range(2, 13):
        L = m if m % 2 == 0 else 2 * m
        mp = 2 * m if m % 2 == 0 else m
        tau = complex(1, 1) / L
        tau2 = tau / (1 - L * tau)
        for r in range(m):
            n1, d1 = theta_char(tau, r, m)
            n2, d2 = theta_char(tau2, r, m)
            lam = cmath.exp(TWO_PI_I * r * r / mp)
            err = abs(n2 * d1 - lam * n1 * d2) / max(abs(n2 * d1), abs(n1 * d2))
            worst = max(worst, err)
            need(err < 1e-9, f"calibration m={m}, r={r}")
    orders = {m: (m * (2 if m % 2 == 0 else 1)) for m in range(1, 25)}
    log(f"  phi(tau/(1-L tau)) = exp(2 pi i r^2/m') phi(tau) for Z(1,g)/Z(1,1) of Fer(2), m = 2..12, all r "
        f"(max rel. error {worst:.1e}); m' = |H^3(Z/m;U(1))| |H^2(Z/m;Z/2)| = {orders}  {stamp()}")


# ================================================================ Part 3: §3
TYPES = {   # name: (m, frame shape as function of n, closed form rho/n)
    "-1": (2, lambda n: {1: -n, 2: n}, Fr(1, 16)),
    "x (x^2=-1)": (4, lambda n: {2: -n // 2, 4: n // 2}, Fr(3, 64)),
    "-h": (6, lambda n: {3: -n // 3, 6: n // 3}, Fr(19, 432)),
    "Jh": (12, lambda n: {6: -n // 6, 12: n // 6}, Fr(73, 1728)),
}


def eta_prod(tau, d):
    out = 1.0
    for k, v in d.items():
        out *= eta(k * tau) ** v
    return out


def find_golay_h(G12):
    """An order-3 element of Aut(Golay) without fixed coordinate."""
    W = codewords(G12, 12)
    Wset = set(W)
    hexads = {A | B for A, B in W if pc(A | B) == 6}
    rows = [unvec(vec(r), 12) for r in G12]
    pts = list(range(12))

    def triples(rest):
        if not rest:
            yield []
            return
        a = rest[0]
        for b, c in itertools.combinations(rest[1:], 2):
            r2 = [x for x in rest[1:] if x not in (b, c)]
            for t in triples(r2):
                yield [(a, b, c)] + t
    for part in triples(pts):
        for orient in itertools.product((0, 1), repeat=4):
            p = list(range(12))
            for (a, b, c), o in zip(part, orient):
                if o:
                    b, c = c, b
                p[a], p[b], p[c] = b, c, a
            good = True
            for h in hexads:
                img = 0
                for i in range(12):
                    if h >> i & 1:
                        img |= 1 << p[i]
                if img not in hexads:
                    good = False
                    break
            if not good:
                continue
            for signs in itertools.product(((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)), repeat=4):
                s = [1] * 12
                for (a, b, c), sg in zip(part, signs):
                    s[a], s[b], s[c] = sg
                g = (tuple(p), tuple(s))
                if all(vec(sp_apply(g, r)) in Wset for r in rows):
                    return g
    return None


def collapsed_theta(rows, n, h):
    """Theta_{Lambda^h} for an order-3 h without fixed coordinate, after conjugating h to a permutation:
    sum over the collapsed fixed code D of prod_j theta_{d_j}."""
    p, s = h
    t = [0] * n
    for i in range(n):                          # an h-fixed sign vector: t_{p(i)} = s_i t_i along each cycle
        if t[i] == 0:
            t[i] = 1
            j = i
            while t[p[j]] == 0:
                t[p[j]] = s[j] * t[j]
                j = p[j]
            need(t[p[j]] == s[j] * t[j], "cycle sign product +1")
    rows2 = [[(t[i] * r[i]) % 3 for i in range(n)] for r in rows]
    hp = (p, (1,) * n)
    need(Code(rows2, n).is_aut(hp), "conjugated h is a permutation automorphism")
    F = fixed_subcode(rows2, n, hp)
    reps = sorted({min(i, p[i], p[p[i]]) for i in range(n)})
    D = [[r[i] for i in reps] for r in F]
    words = [tuple(unvec(w, len(reps))) for w in codewords(D, len(reps))] if D else [tuple([0] * len(reps))]

    def theta(tau):
        th = []
        for rr in range(3):
            th.append(sum(cmath.exp(1j * math.pi * tau * a * a) for a in range(-60, 61) if a % 3 == rr))
        tot = 0
        for w in words:
            pr = 1
            for x in w:
                pr *= th[x]
            tot += pr
        return tot
    return theta, len(F)


def part3(d):
    log("Part 3 (§3): Frame-shape eigenvalues, odd order, Corollary 3.4")
    res = []
    for name, (m, fs, rho_n) in TYPES.items():
        for n in (12, 24):
            k = n // 12
            dsh = fs(n)
            rho = rho_frame(dsh)
            need(rho == rho_n * n, f"rho {name}")
            L = m
            tau = complex(1, 1) / L
            Z = lambda t: 1 / eta_prod(t, dsh)
            lam = cmath.exp(TWO_PI_I * L * rho)
            mp = 2 * m
            need(close(lam, cmath.exp(TWO_PI_I * 2 * k / mp)), f"eigenvalue = e(2k/m') for {name}")
            need(close(Z(tau / (1 - L * tau)), lam * Z(tau), tol=1e-8), f"Prop 3.2 numerically for {name}, n={n}")
            # Prop 2.3: S-transform of 1/eta_g is |det(1-g)|^{1/2} prod eta(tau/k)^{-d_k}
            t0 = complex(0.17, 0.9)
            detabs = 1
            for kk, v in dsh.items():
                detabs *= Fr(kk) ** v
            chi_tw = math.sqrt(detabs) * eta_prod_div(t0, dsh)
            need(close(Z(-1 / t0), chi_tw, tol=1e-8), f"Prop 2.3 for {name}")
        res.append(f"{name}: rho = {rho_n}n, eigenvalue e(2k/{2 * m})")
    # odd order: Golay with h (k = 1) and GJF's E36 with the shift (k = 3)
    h = find_golay_h(d["golay"])
    need(h is not None and not fixed_coords(h) and order(h) == 3, "an order-3 h on Golay")
    oddres = []
    for label, rows, n, hh in (("Golay", d["golay"], 12, h),
                               ("E36", d["E36"], 36, (tuple((i + 12) % 36 for i in range(36)), (1,) * 36))):
        k = n // 12
        need(Code(rows, n).is_aut(hh), f"h in Aut({label})")
        dsh = frame_shape(hh)
        need(dsh == {3: n // 3}, "Frame shape 3^{n/3}")
        theta, dimF = collapsed_theta(rows, n, hh)
        Zh = lambda t: theta(t) / eta(3 * t) ** (n // 3)
        tau = complex(1, 1) / 6
        lam = cmath.exp(TWO_PI_I * 2 * k / 3)
        need(close(Zh(tau / (1 - 6 * tau)), lam * Zh(tau), tol=1e-8), f"Prop 3.3 for {label}")
        oddres.append(f"{label} (k = {k}, dim E^h = {dimF}): eigenvalue exp(2 pi i {2 * k % 3}/3)")
    # Corollary 3.4 for k = 1..48, exact
    for k in range(1, 49):
        n = 12 * k
        for name, (m, fs, rho_n) in TYPES.items():
            a = (2 * m * m * rho_n * n) % (2 * m)      # a/m' = L rho with L = m, m' = 2m
            need(a == (2 * k) % (2 * m), f"Cor 3.4 {name} k={k}")
        a3 = (Fr(2 * 3) * Fr(4 * k, 9) * 3) % 3          # a/m = 2m rho_h with rho_h = 4k/9
        need(a3 == (2 * k) % 3, f"Cor 3.4 h k={k}")
    log(f"  even types: {'; '.join(res)} (Prop 3.2 numerically at n = 12, 24; Prop 2.3's twisted character); "
        f"odd: Golay h found = {h}; {'; '.join(oddres)}; Corollary 3.4: a = 2k for k = 1..48, all types  {stamp()}")


def eta_prod_div(tau, d):
    out = 1.0
    for k, v in d.items():
        out *= eta(tau / k) ** (-v)
    return out


# ================================================================ Part 4: cohomology of Q8, Prop 4.2
QUAT = {}


def q8_elements():
    """Q8 as pairs (sign, unit) with unit in 1, i, j, k; multiplication table."""
    units = ["1", "i", "j", "k"]
    table = {("1", u): (1, u) for u in units}
    table.update({(u, "1"): (1, u) for u in units})
    table.update({("i", "i"): (-1, "1"), ("j", "j"): (-1, "1"), ("k", "k"): (-1, "1"),
                  ("i", "j"): (1, "k"), ("j", "k"): (1, "i"), ("k", "i"): (1, "j"),
                  ("j", "i"): (-1, "k"), ("k", "j"): (-1, "i"), ("i", "k"): (-1, "j")})
    els = [(s, u) for s in (1, -1) for u in units]

    def mul(a, b):
        s, u = table[(a[1], b[1])]
        return (a[0] * b[0] * s, u)
    return els, mul


def f2_rank(rows):
    rows = [r for r in rows if r]
    rank = 0
    while rows:
        piv = max(rows)
        top = piv.bit_length() - 1
        rows = [r ^ piv if r >> top & 1 else r for r in rows if r != piv]
        rows = [r for r in rows if r]
        rank += 1
    return rank


def part4():
    log("Part 4 (§4.1): H^1, H^2 of Q8 over F2; the subgroup of Prop 4.2")
    els, mul = q8_elements()
    idx = {e: t for t, e in enumerate(els)}
    N = len(els)
    # d1: C^1 (8) -> C^2 (64): (df)(g,h) = f(g) + f(h) + f(gh)
    d1_rows = []                                 # rows indexed by (g,h): bitmask over C^1 coordinates
    for g in els:
        for h in els:
            d1_rows.append((1 << idx[g]) ^ (1 << idx[h]) ^ (1 << idx[mul(g, h)]))
    # matrix of d1 as a map: rank of the 64 x 8 matrix = rank of its rows
    rank_d1 = f2_rank(list(d1_rows))
    # d2: C^2 (64) -> C^3 (512): (dc)(g,h,k) = c(h,k) + c(gh,k) + c(g,hk) + c(g,h)
    def c2(a, b):
        return idx[a] * N + idx[b]
    d2_rows = []
    for g in els:
        for h in els:
            for k in els:
                d2_rows.append((1 << c2(h, k)) ^ (1 << c2(mul(g, h), k)) ^ (1 << c2(g, mul(h, k))) ^ (1 << c2(g, h)))
    rank_d2 = f2_rank(d2_rows)
    dim_Z1 = N - rank_d1
    dim_H1 = dim_Z1                               # B^1 = 0 for trivial coefficients
    dim_Z2 = N * N - rank_d2
    dim_B2 = rank_d1
    dim_H2 = dim_Z2 - dim_B2
    need((dim_H1, dim_H2) == (2, 2), f"H^1, H^2 of Q8: {(dim_H1, dim_H2)}")
    sizes = set()
    for c in (1, 3, 5, 7):
        gens = [(2 * c % 8,) * 3, (0, 4, 4), (4, 0, 4), (4, 4, 0)]
        S = {(0, 0, 0)}
        frontier = [(0, 0, 0)]
        while frontier:
            new = []
            for x in frontier:
                for g in gens:
                    y = tuple((a + b) % 8 for a, b in zip(x, g))
                    if y not in S:
                        S.add(y)
                        new.append(y)
            frontier = new
        sizes.add(len(S))
    need(sizes == {16}, f"Prop 4.2 subgroup orders {sizes}")
    log(f"  dim H^1(Q8;F2) = {dim_H1}, dim H^2(Q8;F2) = {dim_H2} (cochains: rank d1 = {rank_d1}, rank d2 = "
        f"{rank_d2}); so |rSH^3(Q8)| = 8 * 4 = 32; <(2c,2c,2c), (0,4,4), (4,0,4), (4,4,0)> has order 16 for every "
        f"odd c  {stamp()}")


# ================================================================ Part 5: §4.2
def mat_mul(A, B):
    n = len(A)
    out = []
    for i in range(n):
        row = [0j] * n
        for t, a in enumerate(A[i]):
            if a != 0:
                row = [r + a * b for r, b in zip(row, B[t])]
        out.append(row)
    return out


def mat_kron(A, B):
    return [[A[i // len(B)][j // len(B)] * B[i % len(B)][j % len(B)] for j in range(len(A) * len(B))]
            for i in range(len(A) * len(B))]


def mat_eq(A, B, tol=1e-12):
    return all(abs(A[i][j] - B[i][j]) < tol for i in range(len(A)) for j in range(len(A)))


def mat_scale(c, A):
    return [[c * x for x in row] for row in A]


def mat_trace(A):
    return sum(A[i][i] for i in range(len(A)))


def mat_inv_unitary_like(A):
    """Inverse by Gaussian elimination (complex)."""
    n = len(A)
    M = [list(row) + [1.0 if i == j else 0.0 for j in range(n)] for i, row in enumerate(A)]
    for c in range(n):
        piv = max(range(c, n), key=lambda r: abs(M[r][c]))
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and abs(M[r][c]) > 0:
                fac = M[r][c]
                M[r] = [x - fac * y for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]


def nullspace(eqs, nvar, tol=1e-9):
    """Complex nullspace of a list of equations (each a list of nvar coefficients)."""
    M = [list(r) for r in eqs]
    pivcols = []
    row = 0
    for c in range(nvar):
        piv = max(range(row, len(M)), key=lambda r: abs(M[r][c]), default=None)
        if piv is None or abs(M[piv][c]) < tol:
            continue
        M[row], M[piv] = M[piv], M[row]
        pv = M[row][c]
        M[row] = [x / pv for x in M[row]]
        for r in range(len(M)):
            if r != row and abs(M[r][c]) > tol:
                fac = M[r][c]
                M[r] = [x - fac * y for x, y in zip(M[r], M[row])]
        pivcols.append(c)
        row += 1
        if row == len(M):
            break
    free = [c for c in range(nvar) if c not in pivcols]
    basis = []
    for fc in free:
        v = [0j] * nvar
        v[fc] = 1
        for r, pc_ in enumerate(pivcols):
            v[pc_] = -M[r][fc]
        basis.append(v)
    return basis


def pin_lift(g, gam):
    """phi with phi gamma_i phi^-1 = s_i gamma_{p(i)} (16 unknowns)."""
    p, s = g
    eqs = []
    for i in range(4):
        A, B = gam[i], gam[p[i]]
        # (phi A - s_i B phi)_{ab} = sum_c phi_{ac} A_{cb} - s_i sum_c B_{ac} phi_{cb}
        for a in range(4):
            for b in range(4):
                row = [0j] * 16
                for c in range(4):
                    row[a * 4 + c] += A[c][b]
                    row[c * 4 + b] -= s[i] * B[a][c]
                eqs.append(row)
    ns = nullspace(eqs, 16)
    need(len(ns) == 1, f"Pin lift unique up to scalar ({len(ns)})")
    v = ns[0]
    return [[v[a * 4 + b] for b in range(4)] for a in range(4)]


def mat_id(n):
    return [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]


def kron_all(ms):
    out = ms[0]
    for m in ms[1:]:
        out = mat_kron(out, m)
    return out


def linearisations(phJ, phK):
    """All scalings R_J = l phJ, R_K = m phK with R_J^4 = 1, R_K^2 = R_J^2, R_J R_K R_J = R_K (i.e. genuine
    representations of Q8 = <J, K>); returns the traces at (1, -1, J, K, JK)."""
    d = len(phJ)
    I = mat_id(d)
    J2, K2 = mat_mul(phJ, phJ), mat_mul(phK, phK)
    J4, K4 = mat_mul(J2, J2), mat_mul(K2, K2)
    JKJ = mat_mul(mat_mul(phJ, phK), phJ)
    JK = mat_mul(phJ, phK)
    cJ, cK = J4[0][0], K4[0][0]
    need(mat_eq(J4, mat_scale(cJ, I)) and mat_eq(K4, mat_scale(cK, I)), "fourth powers are scalars")
    out = []
    for a in range(4):
        for b in range(4):
            lJ = (1 / cJ) ** 0.25 * 1j ** a
            lK = (1 / cK) ** 0.25 * 1j ** b
            if not mat_eq(mat_scale(lJ ** 2, J2), mat_scale(lK ** 2, K2)):
                continue
            if not mat_eq(mat_scale(lJ ** 2 * lK, JKJ), mat_scale(lK, phK)):
                continue
            tr = (d, lJ ** 2 * mat_trace(J2), lJ * mat_trace(phJ), lK * mat_trace(phK), lJ * lK * mat_trace(JK))
            need(all(abs(x.imag) < 1e-9 for x in tr[1:]), "real traces")
            out.append(tuple(round(x.real) + 0 for x in tr))
    return out


def q8_orbits(gens, n):
    seen, out = set(), []
    for i in range(n):
        if i in seen:
            continue
        orb, todo = {i}, [i]
        while todo:
            j = todo.pop()
            for g in gens:
                if g[0][j] not in orb:
                    orb.add(g[0][j])
                    todo.append(g[0][j])
        seen |= orb
        out.append(sorted(orb))
    return out


def restrict(g, orb):
    idx = {c: t for t, c in enumerate(orb)}
    return (tuple(idx[g[0][c]] for c in orb), tuple(g[1][c] for c in orb))


def part5(d):
    log("Part 5 (§4.2-4.3): Pin lifts and linearisations, eta identities, the S-defect")
    I2 = [[1, 0], [0, 1]]
    sx = [[0, 1], [1, 0]]
    sy = [[0, -1j], [1j, 0]]
    sz = [[1, 0], [0, -1]]
    gam = [mat_kron(sx, I2), mat_kron(sy, I2), mat_kron(sz, sx), mat_kron(sz, sy)]
    I4 = mat_id(4)
    for a in range(4):
        need(mat_eq(mat_mul(gam[a], gam[a]), I4), "gamma^2 = 1")
        for b in range(a + 1, 4):
            need(mat_eq(mat_mul(gam[a], gam[b]), mat_scale(-1, mat_mul(gam[b], gam[a]))), "anticommute")
    chir = mat_mul(mat_mul(gam[0], gam[1]), mat_mul(gam[2], gam[3]))
    need(mat_eq(mat_mul(chir, chir), I4), "chirality squares to 1")
    expected4 = {(4, 0, 2 * pj, 2 * pk, 2 * pj * pk) for pj in (1, -1) for pk in (1, -1)}

    def orbit_lifts(Jo, Ko):
        need(sp_mul(Jo, Jo) == sp_neg(4) and sp_mul(Ko, Ko) == sp_neg(4) and
             sp_mul(Ko, Jo) == sp_mul(sp_neg(4), sp_mul(Jo, Ko)), "Q8 relations on one orbit")
        phJ, phK = pin_lift(Jo, gam), pin_lift(Ko, gam)
        need(all(mat_eq(mat_mul(ph, chir), mat_mul(chir, ph)) for ph in (phJ, phK)), "Pin lifts are even")
        lin = linearisations(phJ, phK)
        need(len(lin) == 4 and set(lin) == expected4, f"linearisations on an orbit {lin}")
        return phJ, phK
    # every Q8-orbit of coordinates of the two Q8-codes of paper/conj14.tex
    J72, K72 = blockwise72(d["blkJ"]), blockwise72(d["blkK"])
    norb = 0
    for n, J, K in ((12, d["J"], d["K"]), (72, J72, K72)):
        orbs = q8_orbits([J, K], n)
        need(len(orbs) == n // 4 and all(len(o) == 4 for o in orbs), "free orbits of size 4")
        for o in orbs:
            orbit_lifts(restrict(J, o), restrict(K, o))
            norb += 1
    # the whole spinor module T of Cl(12) for the Golay code: Jordan-Wigner gammas, orbit by orbit
    J, K = d["J"], d["K"]
    orbs = q8_orbits([J, K], 12)
    lifts = [orbit_lifts(restrict(J, o), restrict(K, o)) for o in orbs]
    Gam = {}
    for b, o in enumerate(orbs):
        for t, c in enumerate(o):
            Gam[c] = kron_all([chir] * b + [gam[t]] + [I4] * (len(orbs) - 1 - b))
    I64 = mat_id(64)
    for c in range(12):
        need(mat_eq(mat_mul(Gam[c], Gam[c]), I64), "Gamma^2 = 1")
        for c2 in range(c + 1, 12):
            need(mat_eq(mat_mul(Gam[c], Gam[c2]), mat_scale(-1, mat_mul(Gam[c2], Gam[c]))), "Gammas anticommute")
    PhJ = kron_all([lf[0] for lf in lifts])
    PhK = kron_all([lf[1] for lf in lifts])
    for g, Ph in ((J, PhJ), (K, PhK)):
        for c in range(12):
            need(mat_eq(mat_mul(Ph, Gam[c]), mat_scale(g[1][c], mat_mul(Gam[g[0][c]], Ph))),
                 "tensor product of the orbit lifts is a Pin lift on Cl(12)")
    lin = linearisations(PhJ, PhK)
    expected64 = {(64, 0, 8 * pj, 8 * pk, 8 * pj * pk) for pj in (1, -1) for pk in (1, -1)}
    need(len(lin) == 4 and set(lin) == expected64, f"linearisations on T {lin}")
    log(f"  Lemma 4.4(3): on each of the {norb} Q8-orbits of coordinates of the Golay code (J, K) and of E72 the Pin "
        f"lifts of J, K in Cl(4) are even and unique up to scalars, with exactly 4 genuine linearisations, of traces "
        f"(1, -1, J, K, JK) = (4, 0, 2 psi(J), 2 psi(K), 2 psi(JK)), i.e. rho_2 + 2 psi; for Golay the tensor "
        f"product of the orbit lifts is a Pin lift on the whole spinor module T of Cl(12) (dim 64, Jordan-Wigner), "
        f"whose 4 linearisations have traces (64, 0, 8 psi(J), 8 psi(K), 8 psi(JK)): t_x = 2^(3k), Tr(-1) = 0  "
        f"{stamp()}")
    # Lemma 4.5
    taus = [complex(0.3, 1.1), complex(-0.2, 0.7), complex(0.45, 0.9)]
    worst = 0.0
    for n in (12, 24, 48):
        k = n // 12
        e, f, E, g, F = series(n)
        N = 2 ** (3 * k) * cmath.exp(TWO_PI_I * k / 8)
        need(close(N, (math.sqrt(2) * cmath.exp(TWO_PI_I / 48)) ** (n // 2)), "N closed form")
        for t in taus:
            for lhs, rhs in ((e(-1 / t), E(t)), (f(-1 / t), g(t)), (f(t / (1 - 2 * t)), N * F(t)),
                             (g(t + 2), N * F(-1 / t))):
                err = abs(lhs - rhs) / max(abs(lhs), abs(rhs))
                worst = max(worst, err)
                need(err < 1e-9, f"Lemma 4.5 n={n}")
    log(f"  Lemma 4.5: e|S = E, f|S = g, f(tau/(1-2tau)) = N F with N = 2^(3k) e^(2 pi i k/8), and g(tau+2) = "
        f"N F(-1/tau), for n = 12, 24, 48 at three tau (max rel. error {worst:.1e})  {stamp()}")
    # Prop 4.6.  ch W|S - ch W = 1/4 (3N - T_psi)(F - g(tau+2)/N) follows from Lemma 4.5 by algebra; check it
    # numerically where double precision resolves the defect (k = 4, 8; for larger k the defect is below the
    # rounding error of the dominant term e/8), and check the zero set exactly.
    worst, smallest = 0.0, 1.0
    for tau in (complex(0.2, 1.0), complex(0.1, 0.8), complex(0.13, 0.9)):
        for k in (4, 8):
            n = 12 * k
            e, f, E, g, F = series(n)
            N = 2 ** (3 * k) * cmath.exp(TWO_PI_I * k / 8)
            for psi in ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)):
                Tpsi = 2 ** (3 * k) * sum(psi)

                def parts(t):                 # ch W minus the S-invariant Z(1,1)/8, term by term
                    return [e(t) / 8, 3 * f(t) / 4, E(t) / 8, Tpsi * F(t) / 4, 3 * g(t) / 4, 3 * g(t + 2) / 4]
                P1, P0 = parts(-1 / tau), parts(tau)
                scale = sum(abs(x) for x in P1 + P0)
                lhs = sum(P1) - sum(P0)
                rhs = (3 * N - Tpsi) * (F(tau) - g(tau + 2) / N) / 4
                worst = max(worst, abs(lhs - rhs) / scale)
                need(abs(lhs - rhs) <= 1e-12 * scale, f"S-defect formula k={k} psi={psi}")
                if (k, psi) != (8, (1, 1, 1)):
                    smallest = min(smallest, abs(lhs) / scale)
                    need(abs(lhs) > 1e-11 * scale, f"S-defect nonzero k={k} psi={psi}")
                f2 = abs(F(tau) - g(tau + 2) / N) / max(abs(F(tau)), abs(g(tau + 2) / N))
                need(f2 > 0.5, "F differs from g(tau+2)/N")
    # zero set of the first factor, exactly: 3N - T_psi = 2^(3k)(3 zeta_8^k - sum psi), sum psi in {3, -1}
    zero = set()
    for k in range(4, 49, 4):
        for psi in ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)):
            need(psi[2] == psi[0] * psi[1], "psi is a character")
            # 3 zeta^k = sum psi forces |sum psi| = 3, so sum psi = 3 and zeta^k = 1
            if sum(psi) == 3 and k % 8 == 0:
                zero.add((k, psi))
            else:
                z = cmath.exp(TWO_PI_I * k / 8)
                need(abs(3 * z - sum(psi)) > 1, "nonzero factor")
    need(zero == {(k, (1, 1, 1)) for k in range(8, 49, 8)}, f"S-defect zero set {zero}")
    # leading exponents of F and g|T^2 are n/48 and n/192
    for k in (4, 8, 12):
        n = 12 * k
        e, f, E, g, F = series(n)
        t1, t2 = complex(0.0, 20.0), complex(0.0, 21.0)      # corrections are O(n q^(1/4)) < 1e-11
        lead = lambda h: (cmath.log(h(t2) / h(t1)) / (TWO_PI_I * (t2 - t1))).real
        need(abs(lead(F) - n / 48) < 1e-8 and abs(lead(lambda t: g(t + 2)) - n / 192) < 1e-8, "leading exponents")
    log(f"  Prop 4.6: ch W|S - ch W = 1/4 (3N - T_psi)(F - g(tau+2)/N) numerically for k = 4, 8, all four psi, at "
        f"three tau (max error {worst:.1e} of the term sum; the defect is >= {smallest:.1e} of it except at k = 8, "
        f"psi = 1); exactly, 3N = T_psi iff 8 | k and psi = 1 (k <= 48); F and g(tau+2) have leading exponents "
        f"n/48 and n/192, so the defect vanishes iff 8 | k and psi = 1  {stamp()}")


# ================================================================ Part 6: Remark 4.7
def part6():
    log("Part 6 (§4.4, Remark 4.7): eta invariants (Donnelly), mu")
    els, mul = q8_elements()
    trace = {(1, "1"): 2, (-1, "1"): -2}
    for s in (1, -1):
        for u in "ijk":
            trace[(s, u)] = 0
    chars = {}
    for u in "ijk":
        chars["chi_" + u] = {g: (1 if g[1] in ("1", u) else -1) for g in els}
    chars["1"] = {g: 1 for g in els}
    chars["H"] = {g: 2 * trace[g] for g in els}           # H (x) C = 2 rho_2
    chars["Reg"] = {g: chars["1"][g] + chars["chi_i"][g] + chars["chi_j"][g] + chars["chi_k"][g] + chars["H"][g]
                    for g in els}
    need(chars["Reg"] == {g: (8 if g == (1, "1") else 0) for g in els}, "Reg character")

    def subgroup(gens):
        S = {(1, "1")}
        frontier = [(1, "1")]
        while frontier:
            new = []
            for x in frontier:
                for g in gens:
                    y = mul(x, g)
                    if y not in S:
                        S.add(y)
                        new.append(y)
            frontier = new
        return sorted(S)

    def homs(Gam):
        out = []
        for vals in itertools.product((1, -1), repeat=len(Gam)):
            eps = dict(zip(Gam, vals))
            if all(eps[mul(a, b)] == eps[a] * eps[b] for a in Gam for b in Gam):
                out.append(eps)
        return out

    def eta_inv(Gam, eps, ch):
        return -Fr(1, len(Gam)) * sum(Fr(eps[g] * ch[g], 2 - trace[g]) for g in Gam if g != (1, "1"))

    def A(Gam, eps, rho):
        ch = chars[rho]
        dim = ch[(1, "1")]
        return (Fr(1, 2) * (eta_inv(Gam, eps, ch) - dim * eta_inv(Gam, eps, chars["1"]))) % 1
    groups = {"RP3": subgroup([(-1, "1")]), "S3/<i>": subgroup([(1, "i")]), "S3/Q8": els}
    got = {}
    for name, Gam in groups.items():
        hs = homs(Gam)
        got[name] = sorted({A(Gam, eps, "Reg") for eps in hs})
        need(len(hs) == {"RP3": 2, "S3/<i>": 2, "S3/Q8": 4}[name], "spin structures")
    need(got == {"RP3": [Fr(1, 2)], "S3/<i>": [Fr(1, 4)], "S3/Q8": [Fr(5, 8)]}, f"A_Reg {got}")
    # one Majorana odd under Z/2 on RP3
    Gam = groups["RP3"]
    sign = {g: (1 if g == (1, "1") else -1) for g in Gam}
    maj = sorted({(Fr(1, 2) * (eta_inv(Gam, eps, sign) - eta_inv(Gam, eps, {g: 1 for g in Gam}))) % 1
                  for eps in homs(Gam)})
    need(maj == [Fr(1, 8), Fr(7, 8)], f"Majorana on RP3 {maj}")
    AH = sorted({A(els, eps, "H") for eps in homs(els)})
    need(AH == [Fr(7, 8)], f"A_H {AH}")
    for k in range(1, 49):
        need(close(cmath.exp(-TWO_PI_I * k / 8), cmath.exp(TWO_PI_I * 3 * k * 5 / 8)), "mu")
    log(f"  A_Reg = {got} (all spin structures); A_H(S3/Q8) = {AH}; one Majorana odd under Z/2 on RP3: {maj}; "
        f"4 A_Reg is integral on RP3 and S3/<i> and 1/2 on S3/Q8; mu = e^(-2 pi i k/8) = e^(2 pi i 3k 5/8) "
        f"for k = 1..48  {stamp()}")


# ================================================================ Part 7: §6 on the groups of Table 1
def blockwise72(g4):
    """The signed permutation of 72 coordinates acting as g4 on each of the 18 blocks of 4 (E72, App. A.2)."""
    p, s = [0] * 72, [0] * 72
    for b in range(18):
        for t in range(4):
            p[4 * b + t], s[4 * b + t] = 4 * b + g4[0][t], g4[1][t]
    return (tuple(p), tuple(s))


def maj_number(g):
    """<chi, (1-g) chi> for chi = sqrt3 (1,...,1), with <a/sqrt3, b/sqrt3> = a.b/3 (Lemma 2.2)."""
    n = len(g[0])
    gchi = [0] * n
    for i in range(n):
        gchi[g[0][i]] = 3 * g[1][i]
    return sum(3 * (3 - y) for y in gchi) // 3


def element_anomaly(g):
    """(m, a) with alpha(<g>) = a nu_m by Props 3.2/3.3: a/m' = L rho_g for even m (no fixed vector), and
    a/m = 2m rho_g for odd m."""
    m = order(g)
    rho = rho_frame(frame_shape(g))
    if m % 2 == 0:
        a = (2 * m * m * rho) % (2 * m)
    else:
        a = (2 * m * m * rho) % m
    need(a.denominator == 1, "integral anomaly")
    return m, int(a)


def group_checks(label, n, gens, rows=None):
    G = closure(gens)
    neg, one = sp_neg(n), sp_id(n)
    # (i): commuting pairs generate cyclic groups
    for a in G:
        for b in G:
            if sp_mul(a, b) == sp_mul(b, a):
                H = closure([a, b])
                need(any(order(x) == len(H) for x in H), f"{label}: abelian subgroup not cyclic")
    invol = [x for x in G if x != one and sp_mul(x, x) == one]
    need((len(G) % 2 == 1 and not invol) or invol == [neg], f"{label}: (ii)")
    odd = [x for x in G if order(x) % 2 == 1]
    need(len(odd) in (1, 3) and all(sp_mul(x, y) == sp_mul(y, x) for x in odd for y in G), f"{label}: (iii)")
    k = n // 12
    for x in G:
        if x == one:
            continue
        # Lemma 2.2, Prop 3.1, Corollary 3.4 for every element
        need(maj_number(x) == 6 * sum(1 for v in x[1] if v == -1), f"{label}: Lemma 2.2")
        need(math.prod(x[1]) == 1, f"{label}: epsilon = 1 (Prop 3.1)")
        m, a = element_anomaly(x)
        fs = frame_shape(x)
        if m % 2 == 0:
            need(fs == {m // 2: -2 * n // m, m: 2 * n // m}, f"{label}: Frame shape")
            need(a == (2 * k) % (2 * m), f"{label}: anomaly 2k nu_m")
        else:
            need(m == 3 and fs == {3: n // 3} and a == (2 * k) % 3, f"{label}: order-3 elements")
        if x == neg:
            continue
        need(not fixed_coords(x), f"{label}: fixed coordinate")
        m = order(x)
        if m % 2 == 0:
            mult = eig_mult(x)
            need(mult == {Fr(s, m): 2 * n // m for s in range(1, m, 2)}, f"{label}: eigenvalues")
            Eg = rho_eigen(x)
            need(Eg == Fr(n, 24) + Fr(n, 12 * m * m) and Eg > Fr(n, 24), f"{label}: E_g")
    if rows is not None:
        Cc = Code(rows, n)
        need(all(Cc.is_aut(g) for g in gens), f"{label}: generators in Aut")
    return len(G)


def part7(d):
    log("Part 7 (§6): Lemmas 6.1-6.2 on the groups of Table 1 (seed codes of paper/conj14.tex)")
    G12 = d["golay"]
    J, K = d["J"], d["K"]
    res = []
    res.append(("Golay, <-1>", group_checks("<-1>", 12, [sp_neg(12)], G12)))
    res.append(("Golay, <J>", group_checks("<J>", 12, [J], G12)))
    res.append(("Golay, Q8", group_checks("Q8", 12, [J, K], G12)))
    hs = (tuple((i + 12) % 36 for i in range(36)), (1,) * 36)
    res.append(("E36, <h>", group_checks("<h>", 36, [hs], d["E36"])))
    res.append(("E36, <-h>", group_checks("<-h>", 36, [sp_mul(sp_neg(36), hs)], d["E36"])))
    # E72 from the Morita recipe
    mor = d["morita"]
    rows = []
    for u in d["U"]:
        for slot in (0, 1):
            r = [0] * 72
            for b in range(18):
                x, y = u[2 * b], u[2 * b + 1]
                coef = (x, y, 0, 0) if slot == 0 else (0, 0, x, y)
                for c, basis in zip(coef, mor):
                    for t in range(4):
                        r[4 * b + t] = (r[4 * b + t] + c * basis[t]) % 3
            rows.append(r)

    J72, K72 = blockwise72(d["blkJ"]), blockwise72(d["blkK"])
    hb = [3 * (b // 3) + (b % 3 + 1) % 3 for b in range(18)]
    h72 = (tuple(4 * hb[i // 4] + i % 4 for i in range(72)), (1,) * 72)
    res.append(("E72, <Jh>", group_checks("<Jh>", 72, [sp_mul(J72, h72)], rows)))
    res.append(("E72, Q8 x <h>", group_checks("Q8xZ3", 72, [J72, K72, h72], rows)))
    need([r[1] for r in res] == [2, 4, 8, 3, 6, 12, 24], f"group orders {res}")
    log(f"  {', '.join(f'{a}: |G| = {b}' for a, b in res)}: (i)-(iii) hold, every g outside {{+-1}} has no fixed "
        f"coordinate, and every g of even order m has the eigenvalues e^(2 pi i s/m), s odd, each 2n/m times, and "
        f"E_g = n/24 + n/(12 m^2) > n/24 (Lemmas 6.1-6.2); every g != 1 has <chi,(1-g)chi> = 6 N_-(g) and "
        f"epsilon(g) = 1 (Lemma 2.2, Prop 3.1), the Frame shape of Corollary 3.4, and alpha(<g>) = 2k nu_m from "
        f"Props 3.2-3.3  {stamp()}")


# ================================================================ Part 8: Table 1, Remark 7.1
def part8():
    log("Part 8 (§1, §7): Table 1 and the reduction to k <= 24")
    group_order = {1: 1, 2: 2, 3: 3, 4: 4, 6: 6, 8: 8, 12: 12, 24: 24}
    classes = {}
    for k in range(1, 97):
        m = math.gcd(k, 24)
        least = next(M for M in range(1, 25) if (M * k) % 24 == 0)
        need(least == 24 // m, f"TMF minimum k={k}")
        need(group_order[m] == m and 24 // group_order[m] == least, "index 24/|G|")
        classes.setdefault(m, set()).add(k % 24)
        q, r = (k - 1) // 24, (k - 1) % 24 + 1
        need(math.gcd(24 * q + r, 24) == math.gcd(r, 24), "reduction")
    pm = lambda *xs: {x % 24 for x in xs} | {-x % 24 for x in xs}       # Table 1 prints k mod 24 as +-r
    expect = {1: pm(1, 5, 7, 11), 2: pm(2, 10), 3: pm(3, 9), 4: pm(4), 6: pm(6), 8: pm(8), 12: {12}, 24: {0}}
    need(classes == expect, f"residue classes {classes}")
    log(f"  for k = 1..96: 24/gcd(k,24) is the least M with 24 | Mk, it equals 24/|G| for the group of Table 1, the "
        f"residue classes are as printed, and gcd(24q + r, 24) = gcd(r, 24)  {stamp()}")


def main():
    LOG.clear()
    log("minimal_index_paper_check.py: explicit claims of paper/minimal-index.tex (data from paper/conj14.tex)")
    d = parse_tex(open(TEX).read())
    rng = random.Random(2610)
    status = "all checks passed"
    try:
        part1(d, rng)
        part2()
        part3(d)
        part4()
        part5(d)
        part6()
        part7(d)
        part8()
    except AssertionError as e:
        status = f"FAILED: {e}"
    log(status + f" (total {time.time() - T0:.0f}s)")
    with open(os.path.join(HERE, "minimal_index_paper_check.log"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")
    if status.startswith("FAILED"):
        sys.exit(1)


if __name__ == "__main__":
    main()
