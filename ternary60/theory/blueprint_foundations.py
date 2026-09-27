"""Checks for notes/blueprint/orbifold-foundations.md (the VOA-side foundations of the Main Question).

Stdlib only; writes blueprint_foundations.log beside itself. Cited in the blueprint as [V: Part n].

Conventions. Λ(C) is written in a-coordinates: λ = a/√3 with a ∈ ℤⁿ, a mod 3 ∈ C, and ⟨a, b⟩ = a·b/3.
So χ = √3·𝟙 is a = 3·𝟙 and χ/2 is a = (3/2)·𝟙. The frame √3ℤⁿ is 3ℤⁿ. A signed permutation g = (p, s)
acts by g e_i = s_i e_{p(i)} (as in mainq_common.mono_apply).

Part 1 (Prop 3.2(d): GJF Prop 2.4 / Rem 2.5 as q-series). With x = q^{1/24}, the Ramond lattice sum
        Σ_{λ∈Λ(C)} (−1)^{⟨χ,λ⟩} x^{24·|λ+χ/2|²/2} is computed per coordinate by direct lattice sums
        θ_r(x) = Σ_{a ≡ r mod 3} (−1)^a x^{(2a+3)²} (no Euler identity), combined through the complete
        weight enumerator, and compared with Index(C)·η(q)ⁿ. Also θ_0 = 0, θ_1 = η, θ_2 = −η termwise.
        Codes: tetracode³, 4E₃⁺ and Golay (n = 12), q8chain_len24 (n = 24).
Part 2 (Props 3.2, 3.3). Ramond ground states ↔ maximal codewords: per-coordinate minimum and uniqueness;
        for every maximal codeword the lift a ∈ {−1, −2}ⁿ, (2a+3) = −ι(w), parity (−1)^{Σa} = f(w) = f(−w),
        signed count = Index; equivariance under the Q₈ generators of q8chain_len24; for h = g⁴ on the ℤ/12
        seed z12seed_len36_3: an h-fixed characteristic vector χ' = √3·s exists, and on the h-fixed
        maximal codewords the χ'-parity equals the χ-parity up to one global sign; T_h.
Part 3 (Prop 4.5). Vacuum energy: ¼Σθ(1−θ) = (1/24)Σ d_k(k − 1/k) and |det(1−g)| = Π k^{d_k} (Σ d_k = 0 iff
        fixed-point-free), exactly, for random signed permutations and the elements used; the
        S-transform 1/η_g(−1/τ) = |det(1−g)|^{1/2} Π η(τ/k)^{−d_k} numerically; leading exponent ρ_g − n/24.
Part 4 (Lemma 4.3, Props 4.4, 4.7). Bakalov–Kac: for fixed-point-free σ, |Z_σ| = |P_σ/Q| and the defect
        d(σ)² = |det(1−σ)|/|Z_σ| from BK's definition (Def 4.1 of arXiv:math/0402315) by enumerating
        (1−σ)⁻¹Q/Q; compared with the Majorana-layer criterion ⟨χ,(1−σ)χ⟩ mod 4 on unimodular lattices
        (ℤ^m, Λ(tetracode), Λ(Golay), Λ(q8chain_len24), Λ(z12seed_len36_3)); ⟨χ,(1−g)χ⟩ = 6·#{s_i = −1};
        and the frame claims of notes/main-question.md §8.3/§8.5:
        θ and J-type x on √3ℤⁿ have |Z| = 1, d² = 2ⁿ resp. 2^{n/2}.
Part 5 (Lemmas 2.2, 4.2). P_V = e^{2πi(χ/2)(0)} (on a basis of Λ(C)), and (g⁻¹ − 1)a = χ/2 is solvable for
        fixed-point-free g, so ĝ and ĝP_V are conjugate.
Part 6 (Lemma 2.5). Λ(C)_ev^*/Λ(C)_ev ≅ ℤ₂² with q = (0, ½, 3n/8, 3n/8) mod 1 and det Λ_ev = 4.
"""
import cmath, itertools, os, random, sys, time
from fractions import Fraction as Fr
from existence_common import rref, span, f, GOLAY, TETRA, CODE2, HERE
from mainq_common import read_code, mono_apply, mono_mul, mono_neg, mono_pow, mono_id, is_aut, fixed_code

CODES = os.path.join(HERE, "..", "codes")


# ------------------------------------------------------------------ small helpers
def dsum(blocks):
    n = sum(len(b[0]) for b in blocks)
    out, off = [], 0
    for b in blocks:
        m = len(b[0])
        for r in b:
            out.append([0] * off + list(r) + [0] * (n - off - m))
        off += m
    return out


def signed_cycles(g):
    p, s = g
    seen, out = set(), []
    for i in range(len(p)):
        if i not in seen:
            L, j, sg = 0, i, 1
            while j not in seen:
                seen.add(j); sg *= s[j]; j = p[j]; L += 1
            out.append((L, sg))
    return out


def frame_shape(g):
    """d_k with det(1 − x g) = Π (1 − x^k)^{d_k}: a signed L-cycle with sign product +1 gives (1 − x^L),
    with product −1 gives 1 + x^L = (1 − x^{2L})/(1 − x^L)."""
    d = {}
    for L, sg in signed_cycles(g):
        if sg == 1:
            d[L] = d.get(L, 0) + 1
        else:
            d[2 * L] = d.get(2 * L, 0) + 1
            d[L] = d.get(L, 0) - 1
    return {k: v for k, v in d.items() if v}


def rho_phases(g):
    rho, fpf = Fr(0), True
    for L, sg in signed_cycles(g):
        sh = Fr(1, 2) if sg == -1 else Fr(0)
        for j in range(L):
            th = (j + sh) / L
            if th == 0:
                fpf = False
            rho += th * (1 - th) / 4
    return fpf, rho


def perm_matrix(g):
    """Column convention: S e_i = s_i e_{p(i)}."""
    p, s = g
    n = len(p)
    S = [[0] * n for _ in range(n)]
    for i in range(n):
        S[p[i]][i] = s[i]
    return S


def det_frac(A):
    n = len(A)
    M = [[Fr(x) for x in r] for r in A]
    det = Fr(1)
    for c in range(n):
        piv = next((i for i in range(c, n) if M[i][c] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != c:
            M[c], M[piv] = M[piv], M[c]; det = -det
        det *= M[c][c]
        for i in range(c + 1, n):
            if M[i][c] != 0:
                t = M[i][c] / M[c][c]
                M[i] = [a - t * b for a, b in zip(M[i], M[c])]
    return det


def inv_frac(A):
    n = len(A)
    M = [[Fr(x) for x in r] + [Fr(int(i == j)) for j in range(n)] for i, r in enumerate(A)]
    for c in range(n):
        piv = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                t = M[i][c]
                M[i] = [a - t * b for a, b in zip(M[i], M[c])]
    return [r[n:] for r in M]


def matmul(A, B):
    return [[sum(a * b for a, b in zip(r, col)) for col in zip(*B)] for r in A]


def lattice_basis(C, n):
    """Columns of B: a basis of L = {a ∈ ℤⁿ : a mod 3 ∈ C} (a-coordinates of Λ(C))."""
    R = rref(C)
    piv = [next(j for j in range(n) if r[j]) for r in R]
    cols = []
    for r in R:
        cols.append([x if x < 2 else -1 for x in r])   # integer lift, entries in {0, 1, −1}
    for j in range(n):
        if j not in piv:
            v = [0] * n; v[j] = 3; cols.append(v)
    return [list(x) for x in zip(*cols)]              # n×n, columns = basis vectors


def cols(B):
    return [list(c) for c in zip(*B)]


# ------------------------------------------------------------------ Part 1
def series_mul(a, b, N):
    out = [0] * (N + 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b[: N + 1 - i]):
                if y:
                    out[i + j] += x * y
    return out


def series_pow(a, e, N):
    r = [1] + [0] * N
    b = a[:]
    while e:
        if e & 1:
            r = series_mul(r, b, N)
        b = series_mul(b, b, N)
        e >>= 1
    return r


def theta_r(r, N):
    """θ_r(x) = Σ_{a ≡ r mod 3} (−1)^a x^{(2a+3)²}, truncated at x^N."""
    t = [0] * (N + 1)
    for a in range(-60, 61):
        if a % 3 == r:
            e = (2 * a + 3) ** 2
            if e <= N:
                t[e] += (-1) ** (a % 2)
    return t


def eta_x(N, power=1):
    """η(q)^power in x = q^{1/24}: x^power Π (1 − x^{24m})^power."""
    base = [1] + [0] * N
    m = 1
    while 24 * m <= N:
        fac = [0] * (N + 1); fac[0] = 1; fac[24 * m] = -1
        base = series_mul(base, fac, N)
        m += 1
    base = series_pow(base, power, N)
    return [0] * power + base[: N + 1 - power] if power <= N else [0] * (N + 1)


def _gens_bits(C):
    out = []
    for r in rref(C):
        out.append((sum(1 << i for i, x in enumerate(r) if x == 1), sum(1 << i for i, x in enumerate(r) if x == 2)))
    return out


def _badd(x, y):
    t = (x[0] | y[1]) ^ (x[1] | y[0])
    return ((x[1] | y[1]) ^ t, (x[0] | y[0]) ^ t)


def maximal_words(C, n):
    """All codewords of full weight, as tuples over {0,1,2} (bit-sliced enumeration of the span)."""
    gens = _gens_bits(C)
    full = (1 << n) - 1
    out = []
    stack = [((0, 0), 0)]
    while stack:
        w, k = stack.pop()
        if k == len(gens):
            if (w[0] | w[1]) == full:
                out.append(tuple(1 if (w[0] >> i) & 1 else 2 for i in range(n)))
            continue
        g = gens[k]
        w1 = _badd(w, g); w2 = _badd(w1, g)
        stack.extend([(w, k + 1), (w1, k + 1), (w2, k + 1)])
    return out


def cwe(C, n):
    """Complete weight enumerator {(n0, n1, n2): count} by enumerating the span (bit-sliced)."""
    R = rref(C)
    gens = []
    for r in R:
        a = sum(1 << i for i, x in enumerate(r) if x == 1)
        b = sum(1 << i for i, x in enumerate(r) if x == 2)
        gens.append((a, b))

    def add(x, y):
        t = (x[0] | y[1]) ^ (x[1] | y[0])
        return ((x[1] | y[1]) ^ t, (x[0] | y[0]) ^ t)

    out = {}
    stack = [((0, 0), 0)]
    while stack:
        w, k = stack.pop()
        if k == len(gens):
            n1 = bin(w[0]).count("1"); n2 = bin(w[1]).count("1")
            key = (n - n1 - n2, n1, n2)
            out[key] = out.get(key, 0) + 1
            continue
        g = gens[k]
        w1 = add(w, g); w2 = add(w1, g)
        stack.extend([(w, k + 1), (w1, k + 1), (w2, k + 1)])
    return out


def part1():
    ok = True
    N0 = 24 * 3
    th = [theta_r(r, 200) for r in range(3)]
    eta1 = eta_x(200, 1)
    ok0 = all(x == 0 for x in th[0]) and th[1] == eta1 and th[2] == [-x for x in eta1]
    print(f"1 per-coordinate lattice sums: θ_0 = 0, θ_1 = η, θ_2 = −η termwise to x^200: {ok0}", flush=True)
    ok &= ok0
    codes = [("tetracode³", dsum([TETRA] * 3), 12), ("4E₃⁺ (GJF code 2)", CODE2, 12), ("Golay", GOLAY, 12),
             ("q8chain_len24", read_code(os.path.join(CODES, "q8chain_len24.txt")), 24)]
    for name, C, n in codes:
        N = n + N0
        W = cwe(C, n)
        index = sum(cnt * (0 if n0 else (-1) ** n1) for (n0, n1, n2), cnt in W.items())
        th = [theta_r(r, N) for r in range(3)]
        pw = {}
        total = [0] * (N + 1)
        for (n0, n1, n2), cnt in W.items():
            term = series_mul(series_mul(series_pow(th[0], n0, N), series_pow(th[1], n1, N), N),
                              series_pow(th[2], n2, N), N)
            total = [a + cnt * b for a, b in zip(total, term)]
        target = [index * x for x in eta_x(N, n)]
        agree = total == target
        # the raw (not divided by η) Ramond theta series has leading term Index·x^n: ground states
        lead = next(i for i, x in enumerate(total) if x) if any(total) else None
        ok &= agree
        tail = (f"leading term of the raw sum: q^{Fr(lead, 24)} = q^(n/24) with coefficient {total[lead]}"
                if lead is not None else "the raw sum vanishes identically to this order (no maximal codewords)")
        print(f"1 {name} (n = {n}): Σ_λ (−1)^⟨χ,λ⟩ q^(|λ+χ/2|²/2) = Index·ηⁿ through q^(n/24 + {N0 // 24}): {agree}; "
              f"Index = Σ f(w) = {index}; {tail}", flush=True)
    return ok


# ------------------------------------------------------------------ Part 2
def part2():
    ok = True
    # per-coordinate minimum of (2a+3)² over a ≡ r (mod 3), and its minimisers
    mins = {}
    for r in range(3):
        vals = [((2 * a + 3) ** 2, a) for a in range(-60, 61) if a % 3 == r]
        m = min(v for v, _ in vals)
        mins[r] = (m, [a for v, a in vals if v == m])
    okc = mins == {0: (9, [-3, 0]), 1: (1, [-2]), 2: (1, [-1])}
    ok &= okc
    print(f"2 per-coordinate min of (2a+3)² over a ≡ r mod 3: {mins}; so Σ(2a_i+3)² ≥ n + 8·#{{w_i = 0}}, "
          f"equality only for the unique lift with a_i ∈ {{−1, −2}} on nonzero coordinates: {okc}", flush=True)
    iota = {0: 0, 1: 1, 2: -1}
    for name, C, n in [("Golay", GOLAY, 12), ("q8chain_len24", read_code(os.path.join(CODES, "q8chain_len24.txt")), 24)]:
        words = maximal_words(C, n)
        good = True
        pos = neg = 0
        for w in words:
            a = [-2 if x == 1 else -1 for x in w]
            good &= all((ai - x) % 3 == 0 for ai, x in zip(a, w))
            good &= all(2 * ai + 3 == -iota[x] for ai, x in zip(a, w))
            par = (-1) ** (sum(a) % 2)
            wneg = tuple((-x) % 3 for x in w)
            good &= par == f(w) == f(wneg)
            if par == 1:
                pos += 1
            else:
                neg += 1
        index = sum(f(w) for w in words)                      # f vanishes off maximal words
        ok &= good and pos - neg == index
        print(f"2 {name}: {len(words)} maximal codewords = Ramond ground states; lift a ∈ {{−1,−2}}ⁿ with "
              f"2a+3 = −ι(w), parity (−1)^Σa = f(w) = f(−w) for all: {good}; #even − #odd = {pos} − {neg} = "
              f"{pos - neg} = Index {index}", flush=True)
    # equivariance under Q8 on q8chain_len24
    from mainq_q8chain import q8
    C = read_code(os.path.join(CODES, "q8chain_len24.txt")); n = 24
    J, K = q8(n)
    words = maximal_words(C, n)
    wset = set(words)

    def nu(w):
        return [-iota[x] for x in w]                 # 2a+3, i.e. 2√3·ν in coordinates

    def act(g, v):
        p, s = g
        out = [0] * len(v)
        for i, x in enumerate(v):
            out[p[i]] = s[i] * x
        return out
    eq = all(is_aut(g, C, n) for g in (J, K))
    for g in (J, K):
        for w in words:
            gw = mono_apply(g, w)
            eq &= gw in wset and nu(gw) == act(g, nu(w))
    fixed_J = sum(1 for w in words if mono_apply(J, w) == w)
    ok &= eq and fixed_J == 0
    print(f"2 q8chain_len24: J, K ∈ Aut and ν(gw) = g·ν(w) for all maximal w (the bijection is equivariant): "
          f"{eq}; maximal words fixed by J: {fixed_J} (J² = −1 fixes none)", flush=True)
    # order-3 element h = g^4 on the Z/12 seed: h-fixed characteristic vector and the parity comparison
    C = read_code(os.path.join(CODES, "z12seed_len36_3.txt")); n = 36
    p = [0] * n; s = [1] * n
    for j in range(6):
        for i in range(6):
            p[6 * j + i] = 6 * j + (i + 1) % 6
            s[6 * j + i] = -1 if i == 5 else 1
    g = (tuple(p), tuple(s))
    h = mono_pow(g, 4)
    okg = is_aut(g, C, n)
    cyc_ok = all(sg == 1 for L, sg in signed_cycles(h))
    # solve s' with h s' = s' (d_{p(i)} = s_i d_i along cycles)
    sv = [0] * n
    seen = set()
    hp, hs = h
    for i in range(n):
        if i in seen:
            continue
        sv[i] = 1; seen.add(i); j = i
        while hp[j] not in seen:
            sv[hp[j]] = hs[j] * sv[j]; seen.add(hp[j]); j = hp[j]
    fixed = [0] * n
    for i in range(n):
        fixed[hp[i]] = hs[i] * sv[i]
    s_fixed = fixed == sv
    L = lattice_basis(C, n)
    char_ok = all((sum(si * ai for si, ai in zip(sv, b)) - sum(ai * ai for ai in b) // 3) % 2 == 0
                  for b in cols(L))
    F = fixed_code(C, n, h)
    fw = [w for w in span(rref(F), n) if all(w)] if F else []
    ratios = set()
    for w in fw:
        a = [-2 if x == 1 else -1 for x in w]
        lam_prime = [ai + 3 * (1 - si) // 2 for ai, si in zip(a, sv)]          # λ' = ν − χ'/2 (a-coords)
        par_chi = (-1) ** (sum(a) % 2)
        par_chip = (-1) ** (sum(si * li for si, li in zip(sv, lam_prime)) % 2)
        ratios.add(par_chi * par_chip)
    T_h = sum(f(w) for w in fw)
    okh = okg and cyc_ok and s_fixed and char_ok and len(ratios) <= 1 and T_h == 0
    ok &= okh
    print(f"2 z12seed_len36_3, h = g⁴ (order 3): g ∈ Aut {okg}; every h-cycle has sign product +1 {cyc_ok}; "
          f"h-fixed sign vector s found {s_fixed}; χ' = √3·s characteristic {char_ok}; h-fixed maximal words "
          f"{len(fw)}, χ'-parity/χ-parity = {sorted(ratios)} (one global sign); T_h = {T_h}", flush=True)
    return ok


# ------------------------------------------------------------------ Part 3
def eta_c(t, terms=400):
    q = cmath.exp(2j * cmath.pi * t)
    prod = 1
    qn = 1
    for _ in range(terms):
        qn *= q
        prod *= (1 - qn)
        if abs(qn) < 1e-18:
            break
    return cmath.exp(2j * cmath.pi * t / 24) * prod


def part3():
    ok = True
    rng = random.Random(11)
    cnt = fpf_cnt = 0
    for _ in range(400):
        n = rng.randrange(1, 10)
        p = list(range(n)); rng.shuffle(p)
        s = [rng.choice((1, -1)) for _ in range(n)]
        g = (tuple(p), tuple(s))
        d = frame_shape(g)
        fpf, rho = rho_phases(g)
        rho2 = sum(Fr(v, 24) * (k - Fr(1, k)) for k, v in d.items())
        detv = det_frac([[int(i == j) - x for j, x in enumerate(r)] for i, r in enumerate(perm_matrix(g))])
        prodk = Fr(1)
        for k, v in d.items():
            prodk *= Fr(k) ** v
        sumd = sum(d.values())
        good = rho == rho2 and sum(k * v for k, v in d.items()) == n and (fpf == (sumd == 0))
        good &= (abs(detv) == prodk) if fpf else (detv == 0)
        ok &= good
        cnt += 1; fpf_cnt += fpf
    print(f"3 {cnt} random signed permutations (n ≤ 9, {fpf_cnt} fixed-point-free): ¼Σθ(1−θ) = (1/24)Σd_k(k−1/k), "
          f"Σk·d_k = n, fixed-point-free ⟺ Σd_k = 0, and |det(1−g)| = Πk^(d_k) (else det = 0): {ok}", flush=True)
    # the element types used (on 12 coordinates; everything scales with n)
    from mainq_q8chain import q8
    J, K = q8(12)
    minus = mono_neg(12)
    # order-3 fixed-point-free permutation h and order-12 element on 12 coordinates
    h = (tuple((i + 4) % 12 for i in range(12)), (1,) * 12)                        # (0 4 8)(1 5 9)(2 6 10)(3 7 11)
    p6 = [0] * 12; s6 = [1] * 12
    for j in range(2):
        for i in range(6):
            p6[6 * j + i] = 6 * j + (i + 1) % 6
            s6[6 * j + i] = -1 if i == 5 else 1
    g12 = (tuple(p6), tuple(s6))
    types = [("−1", minus), ("J (J² = −1)", J), ("JK", mono_mul(J, K)), ("−h (order 6)", mono_mul(minus, h)),
             ("g (order 12, g⁶ = −1)", g12), ("g² (order 6)", mono_pow(g12, 2)), ("g³ (order 4)", mono_pow(g12, 3)),
             ("h (order 3, not fpf)", h)]
    for name, g in types:
        d = frame_shape(g)
        fpf, rho = rho_phases(g)
        n = 12
        prodk = Fr(1)
        for k, v in d.items():
            prodk *= Fr(k) ** v
        lead = -sum(Fr(v, 24 * k) for k, v in d.items())
        good = lead == rho - Fr(n, 24)
        # numerical S-transform check (fixed-point-free only)
        num = ""
        if fpf:
            errs = []
            for t in (0.13 + 1.07j, -0.31 + 0.83j, 0.4 + 1.9j):
                lhs = 1
                for k, v in d.items():
                    lhs *= eta_c(-k / t) ** (-v)
                rhs = cmath.sqrt(prodk)
                for k, v in d.items():
                    rhs *= eta_c(t / k) ** (-v)
                errs.append(abs(lhs - rhs) / abs(rhs))
            num = f"; 1/η_g(−1/τ) = |det|^(1/2)·Πη(τ/k)^(−d_k): max rel. err {max(errs):.1e}"
            good &= max(errs) < 1e-9
        ok &= good
        fs = " ".join(f"{k}^{v}" for k, v in sorted(d.items()))
        print(f"3 {name} on n = 12: Frame {fs}; fixed-point-free {fpf}; ρ_g = {rho} (ρ_g/n = {rho / n}); "
              f"|det(1−g)| = {prodk if fpf else 0}; −Σd_k/(24k) = ρ_g − n/24: {lead == rho - Fr(n, 24)}{num}",
              flush=True)
    return ok


# ------------------------------------------------------------------ Part 4 (Bakalov–Kac)
def hnf_rows(rows):
    rows = [r[:] for r in rows if any(r)]
    n = len(rows[0])
    H = []
    for c in range(n):
        piv = [r for r in rows if r[c] != 0]
        rest = [r for r in rows if r[c] == 0]
        while len(piv) > 1:
            piv.sort(key=lambda r: abs(r[c]))
            p0 = piv[0]; new = [p0]
            for r in piv[1:]:
                q = r[c] // p0[c]
                r2 = [x - q * y for x, y in zip(r, p0)]
                (new if r2[c] != 0 else rest).append(r2)
            piv = new
        p0 = piv[0]
        if p0[c] < 0:
            p0 = [-x for x in p0]
        H.append(p0)
        rows = [r for r in rest if any(r)]
    return H


def bk_data(Bm, scale, S, chi):
    """Bakalov–Kac data for a fixed-point-free σ (matrix S, column convention) on the lattice Q with basis
    the columns of Bm and form ⟨x,y⟩ = x·y/scale; χ is only used for the Majorana number.
    Returns (|det(1−σ)|, |Z_σ| = |P_σ/Q|, d(σ)² = |Q/Q_σ|, ⟨χ,(1−σ)χ⟩)."""
    n = len(Bm)
    Bc = cols(Bm)                                                   # basis vectors
    Binv = inv_frac(Bm)
    M = matmul(matmul(Binv, S), [[Fr(x) for x in r] for r in Bm])    # S B = B M
    assert all(x.denominator == 1 for r in M for x in r)
    A = [[int(i == j) - int(M[i][j]) for j in range(n)] for i in range(n)]   # I − M
    D = abs(int(det_frac(A)))
    Ainv = inv_frac(A)
    den = 1
    for r in Ainv:
        for x in r:
            den = den * x.denominator // __import__("math").gcd(den, x.denominator)
    Ai = [[int(x * den) for x in r] for r in Ainv]
    BAi = [[sum(Bm[i][k] * Ai[k][j] for k in range(n)) for j in range(n)] for i in range(n)]   # den·B·A⁻¹
    # Q, Q_ev, and the dual tests (integers): x ∈ Q^* ⟺ x·b ≡ 0 mod scale for all basis b
    par = [(sum(x * x for x in b) // scale) % 2 for b in Bc]
    j0 = next(j for j, pj in enumerate(par) if pj)
    Qev = [[2 * x for x in Bc[j0]]] + [[x + pj * y for x, y in zip(b, Bc[j0])] for j, (b, pj) in enumerate(zip(Bc, par)) if j != j0]
    # (1−σ)x for x = B c: (1−σ)B c = B (I−M) c = B v with v integer; parity of |B v|² decides Q_ev
    # coset reps of ℤⁿ / A ℤⁿ (columns of A): row-HNF of Aᵀ
    H = hnf_rows([list(r) for r in zip(*A)])
    diag = [H[i][i] for i in range(n)]
    cntP = 0
    for v in itertools.product(*[range(dd) for dd in diag]):
        lam = [sum(BAi[i][j] * v[j] for j in range(n)) for i in range(n)]      # den·λ
        # λ ∈ Q_ev^* : λ·q/scale ∈ ℤ
        if any(sum(a * b for a, b in zip(lam, q)) % (den * scale) for q in Qev):
            continue
        alpha = [sum(Bm[i][j] * v[j] for j in range(n)) for i in range(n)]    # (1−σ)λ = B v ∈ Q
        alpha_even = (sum(x * x for x in alpha) // scale) % 2 == 0
        if alpha_even and any(sum(a * b for a, b in zip(lam, b)) % (den * scale) for b in Bc):
            continue
        cntP += 1
    Sc = [sum(S[i][j] * chi[j] for j in range(n)) for i in range(n)]
    maj = Fr(sum(c * (c - sc) for c, sc in zip(chi, Sc)), scale)
    return D, cntP, Fr(D, cntP), maj


def fpf_auts_small(C, n):
    out = []
    for perm in itertools.permutations(range(n)):
        for s in itertools.product((1, -1), repeat=n):
            g = (perm, s)
            if is_aut(g, C, n) and rho_phases(g)[0]:
                out.append(g)
    return out


def part4():
    ok = True
    t0 = time.time()
    # (a) standard lattices Z^m: −1, and the 90° rotation on Z^2
    cases = []
    for m in range(1, 5):
        cases.append((f"ℤ^{m}, σ = −1", [[int(i == j) for j in range(m)] for i in range(m)], 1,
                      perm_matrix(mono_neg(m)), [1] * m, True))
    cases.append(("ℤ², 90° rotation", [[1, 0], [0, 1]], 1, perm_matrix(((1, 0), (1, -1))), [1, 1], True))
    # (b) Λ(tetracode): all fixed-point-free automorphisms
    T = TETRA
    BT = lattice_basis(T, 4)
    fp = fpf_auts_small(T, 4)
    stats = {}
    for g in fp:
        D, Z, d2, maj = bk_data(BT, 3, perm_matrix(g), [3] * 4)
        pred = 2 if maj % 4 == 2 else 1
        eps = 1
        for x in g[1]:
            eps *= x
        key = (D, Z, int(d2), int(maj) % 4, eps)
        stats[key] = stats.get(key, 0) + 1
        ok &= (Z == pred) and d2 == Fr(D, pred) and maj == 6 * g[1].count(-1)
    print(f"4 Λ(tetracode) ≅ ℤ⁴: {len(fp)} fixed-point-free automorphisms; (|det(1−σ)|, |Z_σ|, d², ⟨χ,(1−σ)χ⟩ mod 4, "
          f"Π s_i) → count: {dict(sorted(stats.items()))}; |Z_σ| = 2 exactly when ⟨χ,(1−σ)χ⟩ ≡ 2 mod 4, and "
          f"⟨χ,(1−σ)χ⟩ = 6·#{{s_i = −1}}: {ok}", flush=True)
    rng = random.Random(5)
    okm = True
    for _ in range(300):
        n = rng.randrange(1, 13)
        p = list(range(n)); rng.shuffle(p)
        sg = [rng.choice((1, -1)) for _ in range(n)]
        S = perm_matrix((tuple(p), tuple(sg)))
        chi = [3] * n
        Sc = [sum(S[i][j] * chi[j] for j in range(n)) for i in range(n)]
        maj = Fr(sum(c * (c - x) for c, x in zip(chi, Sc)), 3)
        okm &= maj == 6 * sg.count(-1)
    ok &= okm
    print(f"4 300 random signed permutations: ⟨χ,(1−g)χ⟩ = 6·#{{i : s_i = −1}}, so the Majorana number is "
          f"≡ 2 mod 4 iff Π_i s_i = −1: {okm}", flush=True)
    # (c) Golay and q8chain_len24
    BG = lattice_basis(GOLAY, 12)
    cases.append(("Λ(Golay), σ = −1", BG, 3, perm_matrix(mono_neg(12)), [3] * 12, True))
    from mainq_q8chain import q8
    C24 = read_code(os.path.join(CODES, "q8chain_len24.txt"))
    J, K = q8(24)
    B24 = lattice_basis(C24, 24)
    cases.append(("Λ(q8chain_len24), σ = J", B24, 3, perm_matrix(J), [3] * 24, True))
    cases.append(("Λ(q8chain_len24), σ = JK", B24, 3, perm_matrix(mono_mul(J, K)), [3] * 24, True))
    C36 = read_code(os.path.join(CODES, "z12seed_len36_3.txt"))
    p = [0] * 36; s = [1] * 36
    for j in range(6):
        for i in range(6):
            p[6 * j + i] = 6 * j + (i + 1) % 6
            s[6 * j + i] = -1 if i == 5 else 1
    g36 = (tuple(p), tuple(s))
    assert is_aut(g36, C36, 36)
    cases.append(("Λ(z12seed_len36_3), σ = g (order 12)", lattice_basis(C36, 36), 3, perm_matrix(g36), [3] * 36, True))
    # (d) frame lattice √3ℤⁿ (a-coords 3ℤⁿ): θ and J-type x
    for n in (1, 2, 3, 4, 8, 12):
        cases.append((f"frame √3ℤ^{n}, σ = θ = −1", [[3 * int(i == j) for j in range(n)] for i in range(n)], 3,
                      perm_matrix(mono_neg(n)), [3] * n, False))
    for n in (4, 12, 24):
        Jn, _ = q8(n)
        cases.append((f"frame √3ℤ^{n}, σ = J-type x", [[3 * int(i == j) for j in range(n)] for i in range(n)], 3,
                      perm_matrix(Jn), [3] * n, False))
    for name, Bm, scale, S, chi, unimod in cases:
        D, Z, d2, maj = bk_data(Bm, scale, S, chi)
        if unimod:
            pred = 2 if int(maj) % 4 == 2 else 1
            good = Z == pred and d2 == Fr(D, pred)
            extra = f"⟨χ,(1−σ)χ⟩ = {maj} ≡ {int(maj) % 4} mod 4 → predicted |Z| = {pred}"
        else:
            n = len(Bm)
            if "θ" in name:
                good = (Z == 1 and d2 == 2 ** n) if n % 2 == 0 else (Z == 2 and d2 == 2 ** (n - 1))
                extra = "expected |Z| = 1, d² = 2ⁿ for n even (|Z| = 2, d² = 2^(n−1) Majorana for n odd)"
            else:
                good = Z == 1 and d2 == 2 ** (n // 2)
                extra = "expected |Z| = 1, d² = 2^(n/2): T_x = spinor module of Cl(n/2)"
        ok &= good
        print(f"4 {name}: |det(1−σ)| = {D}, |Z_σ| = {Z}, d(σ)² = {d2}; {extra}: {good}", flush=True)
    print(f"4 [{time.time() - t0:.0f}s]", flush=True)
    return ok


# ------------------------------------------------------------------ Part 5
def part5():
    ok = True
    from mainq_q8chain import q8
    C24 = read_code(os.path.join(CODES, "q8chain_len24.txt"))
    J, K = q8(24)
    C36 = read_code(os.path.join(CODES, "z12seed_len36_3.txt"))
    p = [0] * 36; s = [1] * 36
    for j in range(6):
        for i in range(6):
            p[6 * j + i] = 6 * j + (i + 1) % 6
            s[6 * j + i] = -1 if i == 5 else 1
    g36 = (tuple(p), tuple(s))
    for name, C, n, g in [("Golay, −1", GOLAY, 12, mono_neg(12)), ("q8chain_len24, J", C24, 24, J),
                          ("z12seed_len36_3, g (order 12)", C36, 36, g36), ("z12seed_len36_3, g²", C36, 36, mono_pow(g36, 2))]:
        L = lattice_basis(C, n)
        par_ok = all((sum(b) - (sum(x * x for x in b) // 3)) % 2 == 0 for b in cols(L))    # e^{2πi⟨χ/2,λ⟩} = (−1)^{|λ|²}
        S = perm_matrix(g)
        n_ = len(S)
        Sinv = [list(r) for r in zip(*S)]                                              # orthogonal: S⁻¹ = Sᵀ
        A = [[Sinv[i][j] - int(i == j) for j in range(n_)] for i in range(n_)]
        dA = det_frac(A)
        solved = False
        if dA != 0:
            Ai = inv_frac(A)
            a = [sum(Ai[i][j] * Fr(3, 2) for j in range(n_)) for i in range(n_)]
            chk = [sum(A[i][j] * a[j] for j in range(n_)) for i in range(n_)]
            solved = all(x == Fr(3, 2) for x in chk)
            dens = sorted({x.denominator for x in a})
        good = par_ok and solved and is_aut(g, C, n)
        ok &= good
        print(f"5 {name}: g ∈ Aut; t_(χ/2) acts on Λ(C) as the parity (−1)^|λ|² {par_ok}; (g⁻¹ − 1)a = χ/2 solvable "
              f"(a ∈ ℚ⊗Λ, denominators {dens if solved else '-'}), so t_a ĝ t_a⁻¹ = ĝ·P_V: {solved}", flush=True)
    return ok


# ------------------------------------------------------------------ Part 6
def part6():
    ok = True
    from mainq_q8chain import q8
    for name, C, n in [("Golay", GOLAY, 12), ("q8chain_len24", read_code(os.path.join(CODES, "q8chain_len24.txt")), 24)]:
        L = cols(lattice_basis(C, n))
        par = [(sum(x * x for x in b) // 3) % 2 for b in L]
        j0 = next(j for j, pj in enumerate(par) if pj)
        Qev = [[2 * x for x in L[j0]]] + [[x + pj * y for x, y in zip(b, L[j0])] for j, (b, pj) in enumerate(zip(L, par)) if j != j0]
        gram = [[Fr(sum(a * b for a, b in zip(u, v)), 3) for v in Qev] for u in Qev]
        det = det_frac(gram)
        e1 = [3] + [0] * (n - 1)
        reps = {"0": [Fr(0)] * n, "v = √3e₁": [Fr(x) for x in e1], "s = χ/2": [Fr(3, 2)] * n,
                "c = χ/2 + √3e₁": [Fr(3, 2) + x for x in e1]}
        Qev_inv = inv_frac([list(r) for r in zip(*Qev)])

        def in_dual(x):
            return all(sum(a * b for a, b in zip(x, q)) % 3 == 0 for q in Qev)

        def in_Qev(x):
            c = [sum(Qev_inv[i][j] * x[j] for j in range(n)) for i in range(n)]
            return all(ci.denominator == 1 for ci in c)
        names = list(reps)
        dual_ok = all(in_dual(reps[k]) for k in names)
        distinct = all(not in_Qev([a - b for a, b in zip(reps[k1], reps[k2])]) for k1, k2 in itertools.combinations(names, 2))
        order2 = all(in_Qev([2 * a for a in reps[k]]) for k in names)
        q = {k: (sum(x * x for x in reps[k]) / 3 / 2) % 1 for k in names}
        good = det == 4 and dual_ok and distinct and order2 and q["v = √3e₁"] == Fr(1, 2) \
            and q["s = χ/2"] == Fr(3 * n, 8) % 1 == q["c = χ/2 + √3e₁"]
        ok &= good
        print(f"6 {name} (n = {n}): det Λ_ev = {det}; reps in Λ_ev^*, pairwise distinct mod Λ_ev, all of order ≤ 2 "
              f"(so Λ_ev^*/Λ_ev ≅ ℤ₂²): {dual_ok and distinct and order2}; q mod 1 = "
              f"{ {k: str(v) for k, v in q.items()} } (3n/8 mod 1 = {Fr(3 * n, 8) % 1}): {good}", flush=True)
    return ok


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
        ok1 = part1()
        ok2 = part2()
        ok3 = part3()
        ok4 = part4()
        ok5 = part5()
        ok6 = part6()
        print(f"parts pass: 1 {ok1}, 2 {ok2}, 3 {ok3}, 4 {ok4}, 5 {ok5}, 6 {ok6}; "
              f"all {all([ok1, ok2, ok3, ok4, ok5, ok6])} [{time.time() - t0:.0f}s]", flush=True)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
