"""The coprime-gauging step (Step 1) of Theorem 8.1: checks (notes/main-question.md §8, §8.2).

Part 1 (multi-neighbour data, Lemma A of §8.2). Q₈-invariant self-dual codes in Morita form C = F₃² ⊗ U
        (mainq_morita.py). Test codes:
        - the Q₈-chain codes of mainq_q8chain.py (n = 24, 48, 96), converted with `to_morita`; the script
          checks that the coordinate change maps C onto F₃² ⊗ U and intertwines J, K with left
          multiplication by i, j;
        - random Q₈-invariant codes (n = 24, 48, 72, 96);
        - codes with large U ∩ U₀ (including C = C₀).
        C₀ = F₃² ⊗ U₀, U₀ = ⊕_b (a line in block b), is a sum of Q₈-invariant tetracodes. D = F₃² ⊗ (U ∩ U₀),
        and W = F₃² ⊗ X for a complement X of U ∩ U₀ in U₀ (every such W is Q₈-stable).
        Checks:
        - U is Lagrangian; C and C₀ are self-dual; C₀ and W are Q₈-stable;
        - W ∩ C = 0, C ∩ W^⊥ = D and D + W = C₀, so C₀ is the multi-neighbour of C along W;
        - W is isotropic, so the shifts h_w = w̃/√3 have integral norms and pairings;
        - the pairing W × C → F₃ is nondegenerate on W, so Ŵ ≅ W acts faithfully (a 3-group).
Part 2 (cyclic restrictions, exact arithmetic).
        (a) The eta-invariant machinery of mainq_q8_anomaly.py against GJF's quadratic rule
            A(rotation by 2πa/m) = a²·A(generator) on S³/<i> and RP³.
        (b) For g ∈ {J, K, JK, −1} on the chain codes, GJF Example 4.4 gives the anomaly α ∈ ℤ_{2m} of <g> on
            V_{Λ(C)} directly from the Frame shape of g. The script first checks that χ = √3(1,…,1) is
            characteristic, that g is fixed-point-free, that the Majorana layer vanishes
            (<χ,(1−g)χ> ∈ 4ℤ), and that g^{m/2} = −1. α is compared with 3k·α(Fer(Reg)|<q>): rotation
            planes of angle 2πq/m contribute q². It is also compared on the lens spaces S³/<q>, both spin
            structures, with 3k·A_Reg (Theorem 8.1).
        (c) The same comparison from the Frame shapes alone, for every k = 1..48.
        This checks Theorem 8.1 on cyclic subgroups independently of Step 1. It cannot see the part 4a of
        A(Q₈) that restricts to zero on all cyclic subgroups.
Part 3: the Majorana layer of the Q₈-action on Fer(Reg) vanishes (det Reg(g) = 1 for all g), consistent with
        the vanishing Majorana layer on V_{Λ(C)} (Part 2).
"""
import itertools, os, random, sys
from fractions import Fraction as Fr
from existence_common import rref, dot, HERE
from mainq_common import read_code, is_aut, mono_mul, mono_neg, mono_apply, mono_order, mono_pow
from mainq_morita import code_from_U, q8_gens, to_morita, omega, nullspace_form
import mainq_q8_anomaly as QA


# ------------------------------------------------------------------ linear algebra helpers
def rank(rows):
    return len(rref(rows)) if rows and any(any(r) for r in rows) else 0


def intersect(A, B, n):
    """Basis of span(A) ∩ span(B) (Zassenhaus)."""
    if not A or not B:
        return []
    R = rref([list(a) + list(a) for a in A] + [list(b) + [0] * n for b in B])
    low = [r[n:] for r in R if not any(r[:n]) and any(r[n:])]
    return rref(low) if low else []


def complement(sub, whole, n):
    """Vectors of `whole` extending a basis of span(sub) to a basis of span(whole)."""
    basis, out = list(sub), []
    for w in whole:
        if rank(basis + [w]) > rank(basis):
            basis.append(w); out.append(w)
    return out


def perp_in(C, W, n):
    """Basis of {c ∈ span(C) : c·w = 0 for all w ∈ W}."""
    B = rref(C)
    M = [[dot(b, w) for b in B] for w in W]           # rows: w, columns: basis of C
    R = rref(M) if any(any(r) for r in M) else []
    piv = [next(j for j in range(len(B)) if r[j]) for r in R]
    out = []
    for fj in (j for j in range(len(B)) if j not in piv):
        c = [0] * len(B); c[fj] = 1
        for r, pj in zip(R, piv):
            c[pj] = (-r[fj]) % 3
        out.append([sum(c[j] * B[j][i] for j in range(len(B))) % 3 for i in range(n)])
    return rref(out) if out else []


def random_lagrangian(r, rng):
    """A random Lagrangian U ⊂ F₃^{2r} for Ω (greedy: a random vector of B^Ω outside span B)."""
    n, B = 2 * r, []
    while len(B) < r:
        perp = nullspace_form(B, n, omega)
        c = [rng.randrange(3) for _ in perp]
        v = [sum(ci * p[i] for ci, p in zip(c, perp)) % 3 for i in range(n)]
        if rank(B + [v]) > len(B):
            B = rref(B + [v])
    return B


# ------------------------------------------------------------------ Part 1
def multi_neighbour(U, r, tag, extra=""):
    n = 4 * r
    J, K = q8_gens(r)
    C = code_from_U(U, r)
    U0 = [[int(i == 2 * b) for i in range(2 * r)] for b in range(r)]
    I = intersect(U, U0, 2 * r)
    X = complement(I, U0, 2 * r)
    C0, W = code_from_U(U0, r), code_from_U(X, r) if X else []
    D = code_from_U(I, r) if I else []
    ok = {}
    ok["U Lagrangian, C self-dual"] = (rank(U) == r and all(omega(a, b) == 0 for a in U for b in U)
                                       and rank(C) == n // 2 and all(dot(a, b) == 0 for a in C for b in C))
    ok["C0 self-dual, Q8-inv"] = (rank(C0) == n // 2 and all(dot(a, b) == 0 for a in C0 for b in C0)
                                  and is_aut(J, C0, n) and is_aut(K, C0, n))
    ok["W Q8-stable"] = (not W) or (is_aut(J, W, n) and is_aut(K, W, n))
    ok["W ∩ C = 0"] = rank(C + W) == rank(C) + rank(W)
    ok["C ∩ W^⊥ = D"] = rref(perp_in(C, W, n) or [[0] * n]) == rref(D or [[0] * n])
    ok["D + W = C0"] = rref(D + W) == rref(C0)
    ok["W isotropic (weights ≡ 0 mod 3)"] = all(dot(a, b) == 0 for a in W for b in W)
    ok["Ŵ faithful"] = (not W) or rank([[dot(w, c) for c in rref(C)] for w in W]) == len(W)
    good = all(ok.values())
    print(f"1 {tag}: n = {n}, dim U∩U₀ = {len(I)}, |Ŵ| = 3^{len(W)}{extra}; "
          + ("all checks pass" if good else "FAILED: " + ", ".join(k for k, v in ok.items() if not v)), flush=True)
    return good


_GENS = {}


def chain_gens_cached():
    if not _GENS:
        _GENS.update(QA.chain_gens())
    return _GENS


def chain_codes():
    gens = chain_gens_cached()
    out = []
    for n in (24, 48, 96):
        C = read_code(os.path.join(HERE, "..", "codes", f"q8chain_len{n}.txt"))
        J, K = gens[n]
        orbs, U = to_morita(C, n, J, K)
        r = n // 4
        # the coordinate change y ↦ x (quaternion coordinates per orbit) as a monomial map
        pos, sgn = [0] * n, [1] * n
        pJ, sJ = J; pK, sK = K
        for b, orb in enumerate(orbs):
            o0 = orb[0]; q = pK[o0]
            coords = [(o0, 1), (pJ[o0], sJ[o0]), (q, sK[o0]), (pJ[q], sK[o0] * sJ[q])]
            for a, (p, s) in enumerate(coords):
                pos[p], sgn[p] = 4 * b + a, s
        phi = (tuple(pos), tuple(sgn))
        image = [list(mono_apply(phi, c)) for c in C]
        JM, KM = q8_gens(r)
        same = rref(image) == rref(code_from_U(U, r))
        inter = all(mono_apply(phi, mono_apply(g, e)) == mono_apply(gm, mono_apply(phi, e))
                    for g, gm in ((J, JM), (K, KM)) for e in ([int(i == j) for i in range(n)] for j in range(n)))
        out.append((n, U, J, K, same and inter))
    return out


def part1(rng):
    allok = True
    for n, U, J, K, conv in chain_codes():
        allok &= conv and multi_neighbour(U, n // 4, f"Q8-chain code q8chain_len{n}",
                                          f", Morita conversion (image = F₃²⊗U, J, K ↦ left mult. by i, j) {conv}")
    for r in (6, 12, 18, 24):
        for t in range(3):
            allok &= multi_neighbour(random_lagrangian(r, rng), r, f"random Q8-invariant code #{t + 1}")
    # larger intersections: U = (U₀ on the first s blocks) ⊕ (a random Lagrangian on the other r − s blocks);
    # s = r is C = C₀ (W = 0)
    r = 6
    for s in range(1, r + 1):
        U = [[int(i == 2 * b) for i in range(2 * r)] for b in range(s)]
        if s < r:
            U += [[0] * (2 * s) + u for u in random_lagrangian(r - s, rng)]
        allok &= multi_neighbour(rref(U), r, f"U ⊃ U₀ on {s} of {r} blocks")
    print(f"1 all multi-neighbour checks pass: {allok}", flush=True)


# ------------------------------------------------------------------ Part 2
def cycles(p):
    seen, out = set(), []
    for i in range(len(p)):
        if i not in seen:
            c = [i]
            while p[c[-1]] != i:
                c.append(p[c[-1]])
            seen.update(c); out.append(c)
    return out


def sign_prod(c, s):
    sig = 1
    for i in c:
        sig *= s[i]
    return sig


def frame_shape(g):
    """{k: d_k} with char. polynomial Π_k (x^k − 1)^{d_k}, for a signed permutation g."""
    p, s = g
    d = {}
    for c in cycles(p):
        L = len(c)
        if sign_prod(c, s) == 1:
            d[L] = d.get(L, 0) + 1
        else:
            d[2 * L] = d.get(2 * L, 0) + 1; d[L] = d.get(L, 0) - 1
    return {k: v for k, v in d.items() if v}


def alpha_frame(m, fs):
    """GJF Ex. 4.4 (g fixed-point-free of even order m, Majorana layer 0): α ∈ ℤ_{2m} with α/(2m) ≡ m·ρ_g
    mod 1, where ρ_g = (1/24) Σ_k d_k (k − 1/k) is the weight of the g-twisted module."""
    rho = sum(dk * (Fr(k) - Fr(1, k)) for k, dk in fs.items()) / 24
    a = 2 * m * m * rho
    assert a.denominator == 1
    return int(a) % (2 * m)


def zeta_pow(e, m):
    """ζ_m^e = exp(2πi e/m) as an exact Gaussian integer (re, im), m | 4."""
    return ((1, 0), (0, 1), (-1, 0), (0, -1))[(e * (4 // m)) % 4]


def eig_mults(chi, m):
    """Multiplicity n_j of the eigenvalue ζ_m^j of the generator, for the character t ↦ chi(t) (value on
    the t-th power)."""
    out = []
    for j in range(m):
        re = sum(chi(t) * zeta_pow(-j * t, m)[0] for t in range(m))
        im = sum(chi(t) * zeta_pow(-j * t, m)[1] for t in range(m))
        assert im == 0 and re % m == 0
        out.append(re // m)
    return out


def alpha_fermion(chi, m):
    """α ∈ ℤ_{2m} of ℤ_m on Majorana fermions Fer(ρ), det ρ = 1: a rotation plane of angle 2πq/m
    (0 < q ≤ m/2) has twisted ground-state weight (q/m)²/2, so it contributes α = q² (GJF's generator
    is q = 1)."""
    nj = eig_mults(chi, m)
    assert nj[m // 2] % 2 == 0, "det ρ = −1"
    return (sum(nj[q] * q * q for q in range(1, m // 2)) + (nj[m // 2] // 2) * (m // 2) ** 2) % (2 * m)


def eta_char(group, eps, chi):
    s = Fr(0)
    for g in group:
        if g != QA.ONE:
            s += Fr(eps(g) * chi(g), 1) / (2 - QA.trace_su2(g))
    return -s / len(group)


def anomaly_char(group, eps, chi, dim):
    """½(η(ρ) − dim ρ·η(1)) mod 1 on S³/group (spin structure eps), as in mainq_q8_anomaly.py."""
    a = (eta_char(group, eps, chi) - dim * eta_char(group, eps, lambda q: 1)) / 2
    return a - (a.numerator // a.denominator)


def cyc(q, m):
    """The powers q⁰, …, q^{m−1} in Q₈ ⊂ SU(2)."""
    out, x = [], QA.ONE
    for _ in range(m):
        out.append(x); x = QA.qmul(x, q)
    return out


def two_cos(s, m):
    """2cos(2πs/m) for m ∈ {2, 4}."""
    return {0: 2, m // 2: -2}.get(s % m, 0)


def rot_char(q, m, a=1):
    """Character of the rotation of R² by 2πa/m, as a function on <q> ⊂ SU(2)."""
    pw = cyc(q, m)
    return lambda g: two_cos(a * pw.index(g), m)


Q = {"J": (0, 1, 0, 0), "K": (0, 0, 1, 0), "JK": (0, 0, 0, 1), "−1": QA.MONE}
REG = lambda g: 8 if g == QA.ONE else 0


def compare(name, m, alpha_V, k):
    """α_V (from the code) against 3k·α(Fer(Reg)|<q>) in ℤ_{2m}, and on the lens space S³/<q> (both spin
    structures) α_V·A(gen) against 3k·A_Reg. Returns (α_F, [(lhs, rhs)], ok)."""
    q = Q[name]
    alpha_F = alpha_fermion(lambda t: 8 if t == 0 else 0, m)
    G = cyc(q, m)
    vals = []
    for eps in QA.spin_structures(G):
        lhs = (alpha_V * anomaly_char(G, eps, rot_char(q, m), 2)) % 1
        rhs = (3 * k * anomaly_char(G, eps, REG, 8)) % 1
        vals.append((lhs, rhs))
    return alpha_F, vals, alpha_V == (3 * k * alpha_F) % (2 * m) and all(a == b for a, b in vals)


def part2():
    allok = True
    # (a) the eta machinery against GJF's quadratic rule α(rotation by 2πa/m) = a²·α(generator)
    quad_ok = True
    for name in ("J", "−1"):
        q, m = Q[name], (4 if name == "J" else 2)
        G = cyc(q, m)
        for eps in QA.spin_structures(G):
            A1 = anomaly_char(G, eps, rot_char(q, m), 2)
            for a in range(m):
                quad_ok &= anomaly_char(G, eps, rot_char(q, m, a), 2) == (a * a * A1) % 1
            quad_ok &= anomaly_char(G, eps, REG, 8) == (alpha_fermion(lambda t: 8 if t == 0 else 0, m) * A1) % 1
    print(f"2 eta invariants on S³/<i> and RP³ (both spin structures): A(rotation by 2πa/m) = a²·A(generator) "
          f"and A_Reg = α(Fer(Reg))·A(generator): {quad_ok}", flush=True)
    allok &= quad_ok
    # (b) the chain codes
    gens = chain_gens_cached()
    for n in (24, 48, 96):
        C = read_code(os.path.join(HERE, "..", "codes", f"q8chain_len{n}.txt"))
        J, K = gens[n]
        k = n // 12
        # χ = √3(1,…,1) characteristic: |λ|² ≡ <λ, χ> mod 2 on a basis of Λ(C) (lifts c̃/√3 and √3 e_i)
        charok = all((sum(x * x for x in cl) // 3) % 2 == sum(cl) % 2
                     for cl in ([(x if x < 2 else -1) for x in c] for c in rref(C)))
        print(f"2 q8chain_len{n} (k = {k}): J, K ∈ Aut(C) {is_aut(J, C, n) and is_aut(K, C, n)}; "
              f"χ characteristic {charok}", flush=True)
        allok &= charok
        for name, g in (("J", J), ("K", K), ("JK", mono_mul(J, K)), ("−1", mono_neg(n))):
            p, s = g
            m = mono_order(g)
            fs = frame_shape(g)
            fpf = all(sign_prod(c, s) == -1 for c in cycles(p))
            majorana = (3 * (n - sum(s))) % 4 == 0
            liftok = mono_pow(g, m // 2) == mono_neg(n)
            alpha_V = alpha_frame(m, fs)
            alpha_F, vals, match = compare(name, m, alpha_V, k)
            allok &= fpf and majorana and liftok and match
            print(f"2   {name}: order {m}, Frame shape {' '.join(f'{kk}^{dk}' for kk, dk in sorted(fs.items()))}, "
                  f"fixed-point-free {fpf}, Majorana layer 0 {majorana}, g^(m/2) = −1 {liftok}; "
                  f"α = {alpha_V} ∈ ℤ_{2 * m}, 3k·α(Fer(Reg)) = 3·{k}·{alpha_F} ≡ {(3 * k * alpha_F) % (2 * m)}; "
                  f"on S³/<q>: α·A(gen) vs 3k·A_Reg = {[(str(x), str(y)) for x, y in vals]}; match {match}",
                  flush=True)
    # (c) general k: every Q₈ ⊂ Aut(C) with centre −1 acts freely on coordinates (orbits of size 4), so
    #     J, K, JK are products of n/2 transpositions with sign product −1 (Frame shape 2^(−n/2) 4^(n/2))
    gen_ok = True
    for kk in range(1, 49):
        n = 12 * kk
        for name, m, fs in (("J", 4, {4: n // 2, 2: -(n // 2)}), ("K", 4, {4: n // 2, 2: -(n // 2)}),
                            ("JK", 4, {4: n // 2, 2: -(n // 2)}), ("−1", 2, {2: n, 1: -n})):
            gen_ok &= compare(name, m, alpha_frame(m, fs), kk)[2]
    print(f"2 general k = 1..48 (Frame shapes 2^(−6k) 4^(6k) and 1^(−12k) 2^(12k)): GJF's cyclic anomaly equals "
          f"3k·a restricted to <J>, <K>, <JK>, <−1>, in ℤ_(2m) and on the lens spaces: {gen_ok}", flush=True)
    print(f"2 all cyclic cross-checks pass: {allok and gen_ok}", flush=True)


# ------------------------------------------------------------------ Part 3
def part3():
    # left regular permutation representation of Q₈ on itself: det = sign of the permutation
    def sign(perm):
        seen, sg = set(), 1
        for i in range(len(perm)):
            if i not in seen:
                L, j = 0, i
                while j not in seen:
                    seen.add(j); j = perm[j]; L += 1
                sg *= (-1) ** (L - 1)
        return sg
    idx = {q: t for t, q in enumerate(QA.Q8)}
    dets = {q: sign([idx[QA.qmul(q, h)] for h in QA.Q8]) for q in QA.Q8}
    print(f"3 det Reg(g) for g ∈ Q₈: {sorted(set(dets.values()))} (so w₁(Reg) = 0: the Majorana layer of a vanishes)",
          flush=True)


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        part1(random.Random(81))
        part2()
        part3()
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
