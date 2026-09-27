"""The Q₈-action on the (−1)-twisted sector of V_{Λ(C)}, computed directly (notes/main-question.md §8.3).

Setting: C self-dual of length n = 12k with Q₈ = <J, K> ⊂ Aut(C), J² = K² = −1, acting on V_{Λ(C)} by GJF's
lift (GJF Thm 3.1). The lift of −1 is the lattice involution θ. V_{−1} = S[θ] ⊗ T: the twisted Heisenberg Fock
space times the ground states T.

Part 1 (the ground states, on the Q₈-chain codes n = 24, 48, 96).
        (a) The commutator form c(α, β) = <α,β> + |α|²|β|² mod 2 on Λ(C)/2Λ(C) is nondegenerate, and the frame
            √3ℤⁿ has odd index in Λ(C). So T (dim 2^{n/2}) is the irreducible module of the Clifford algebra
            Cl(n) of the frame zero modes γ_i (one Majorana zero mode per V_{√3ℤ}); it does not depend on C.
        (b) g ∈ Q₈ acts on the frame by the standard signed permutation (GJF Thm 3.1), hence on T by a Pin(n)
            element φ_g with φ_g γ_i φ_g⁻¹ = s_i γ_{p(i)}. φ_J, φ_K are built per transposition and checked.
        (c) Linearisation of the projective action, and the character on T and its supercharacter (parity
            = chirality Γ). T ≅ (H ⊕ 2ψ)^{⊗3k}: on each orbit H in one parity, two 1-dim characters in the other.
        (d) The invariant I = t_{JK}/(t_J t_K) (t = trace of any lifts; independent of the linearisation).
Part 2 (the modular normalisation). The chain S T² S carries the twining character Z(1, J) = 1/η_J
        (Frame shape 2^{−n/2}4^{n/2}; the same for every C) to Z(−1, J^{±1}). This fixes the lift of J on V_{−1}
        with trivial phases. Its trace on T is N(τ) = Z(1,J)(τ/(1−2τ)) / (q^{n/48} Π_{r odd}(1+q^r)^{−n/2}).
        Checked:
        - N is constant and equals 2^{3k}·e^{2πik/8};
        - the chain S T^{−2} S gives the same N iff 4 | k (i.e. iff <J> is non-anomalous);
        - Z(−1, 1) = dim T × Fock character (conventions).
Part 3 (μ). With canonical lifts x̂ = λ_x ρ̃(x) on V_{−1}, Ĵ K̂ = μ·(JK)^ with μ = 1/(N·I). If Q₈ were
        non-anomalous, the orbifold's lifts would be a genuine Q₈-representation restricting to the canonical
        ℤ₄-lifts, so μ = 1. Here μ = e^{−2πik/8}: for k ≡ 4 mod 8 (all cyclic restrictions vanish) μ = −1, so Q₈ is
        anomalous. This is the class 4a of Thm 8.1, obtained directly on V_{Λ(C)}, without Step 1.
        μ is compared with exp(2πi·3k·A_Reg(S³/Q₈)) (Donnelly's eta formula, as in mainq_q8_anomaly.py) for
        k = 1..48.
"""
import cmath, os, sys
from fractions import Fraction as Fr
from existence_common import rref, HERE
from mainq_common import read_code, mono_mul, mono_neg
import mainq_q8_anomaly as QA


# ------------------------------------------------------------------ Clifford algebra (γ_i² = 1), bitmask monomials
def msign(A, B):
    """γ_A γ_B = msign(A, B) γ_{A △ B} (monomials in increasing index order)."""
    s = 0
    while B:
        b = B & -B
        B ^= b
        s += bin(A & ~((b << 1) - 1)).count("1")
    return -1 if s & 1 else 1


def mul(X, Y):
    Z = {}
    for a, x in X.items():
        for b, y in Y.items():
            m = a ^ b
            Z[m] = Z.get(m, 0) + msign(a, b) * x * y
    return {m: v for m, v in Z.items() if abs(v) > 1e-12}


def scal(c, X):
    return {m: c * v for m, v in X.items()}


def gam(i):
    return {1 << i: 1}


def pin_pair(i, j, si, sj):
    """u = 1 ± γ_iγ_j (unnormalised; u⁻¹ = (1 ∓ γ_iγ_j)/2) with u γ_i u⁻¹ = s_i γ_j, u γ_j u⁻¹ = s_j γ_i."""
    for c in (1, -1):
        e = c * msign(1 << i, 1 << j)
        u, ui = {0: 1, (1 << i) | (1 << j): e}, {0: Fr(1, 2), (1 << i) | (1 << j): Fr(-e, 2)}
        if mul(mul(u, gam(i)), ui) == {1 << j: si} and mul(mul(u, gam(j)), ui) == {1 << i: sj}:
            return u, ui
    raise ValueError("no Pin lift")


def pin_lift(g, idx):
    """Pin lift of the signed permutation g (a product of 2-cycles with sign product −1) on the indices idx."""
    p, s = g
    U, Ui, seen = {0: 1}, {0: 1}, set()
    for i in idx:
        if i not in seen:
            j = p[i]
            seen |= {i, j}
            u, ui = pin_pair(i, j, s[i], s[j])
            U, Ui = mul(U, u), mul(ui, Ui)
    return U, Ui


def close(a, b):
    return abs(a - b) < 1e-9


def eqc(X, Y):
    return all(close(X.get(m, 0), Y.get(m, 0)) for m in set(X) | set(Y))


# ------------------------------------------------------------------ Part 1
def commutator_form_ok(C, n):
    """Basis of √3Λ(C) = {x : x mod 3 ∈ C}: lifted rref rows and 3e_i (i non-pivot). Returns (index of 3ℤⁿ is
    3^{n/2}, F₂-rank of c = Gram + q qᵀ on Λ(C)/2Λ(C))."""
    R = rref(C)
    piv = [next(j for j in range(n) if r[j]) for r in R]
    B = [[x if x < 2 else -1 for x in r] for r in R] + [[3 * (j == i) for j in range(n)] for i in range(n) if i not in piv]
    G = [[sum(a * b for a, b in zip(x, y)) // 3 for y in B] for x in B]
    q = [G[i][i] % 2 for i in range(n)]
    M = [[(G[i][j] + q[i] * q[j]) % 2 for j in range(n)] for i in range(n)]
    rk, rows = 0, [r[:] for r in M]
    for c in range(n):
        pr = next((i for i in range(rk, n) if rows[i][c]), None)
        if pr is None:
            continue
        rows[rk], rows[pr] = rows[pr], rows[rk]
        for i in range(n):
            if i != rk and rows[i][c]:
                rows[i] = [(a + b) % 2 for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return len(R) == n // 2 and len(B) == n, rk


Q8L = ["1", "-1", "J", "-J", "K", "-K", "JK", "-JK"]
CHARS = {"1": [1] * 8, "chi_J": [1, 1, 1, 1, -1, -1, -1, -1], "chi_K": [1, 1, -1, -1, 1, 1, -1, -1],
         "chi_JK": [1, 1, -1, -1, -1, -1, 1, 1], "H": [2, -2, 0, 0, 0, 0, 0, 0]}


def decompose(tr):
    """Multiplicities of the irreducible Q₈-characters in the class function tr (on Q8L)."""
    return {nm: sum(c * t for c, t in zip(ch, tr)) / 8 for nm, ch in CHARS.items()}


def orbit_data(J, K, o):
    """On one Q₈-orbit o (4 coordinates): Pin lifts, checks, linearisation, character and supercharacter."""
    FJ, FJi = pin_lift(J, o)
    FK, FKi = pin_lift(K, o)
    conj = all(mul(mul(FJ, gam(i)), FJi) == {1 << J[0][i]: J[1][i]}
               and mul(mul(FK, gam(i)), FKi) == {1 << K[0][i]: K[1][i]} for i in o)
    G = sum(1 << i for i in o)                       # Γ_O = γ_aγ_bγ_cγ_d; Γ_O² = 1
    eps = []
    for X in (FJ, FK, mul(FJ, FK)):
        S2 = mul(X, X)
        assert set(S2) == {G}, "square is not ∝ Γ_O"
        eps.append(S2[G])
    eJ, eK, eJK = eps
    a, b = cmath.sqrt(eK / eJK), cmath.sqrt(eJ / eJK)    # ρ̃(J) = aφ_J, ρ̃(K) = bφ_K: a genuine Q₈
    RJ, RK = scal(a, FJ), scal(b, FK)
    RM = mul(RJ, RJ)                                   # ρ̃(−1)
    rel = eqc(mul(RK, RK), RM) and eqc(mul(mul(RJ, RK), mul(RJ, RK)), RM) and eqc(mul(RM, RM), {0: 1})
    RJK = mul(RJ, RK)
    ops = [{0: 1}, RM, RJ, mul(RM, RJ), RK, mul(RM, RK), RJK, mul(RM, RJK)]
    tr = [4 * X.get(0, 0) for X in ops]                # Tr on the 4-dim module: 2^{4/2} × identity coefficient
    st = [4 * X.get(G, 0) * msign(G, G) for X in ops]  # supertrace: Tr(Γ_O X)
    return conj, rel, [complex(t) for t in tr], [complex(t) for t in st], (FJ, FK)


def part1(gens):
    out = {}
    for n in (24, 48, 96):
        C = read_code(os.path.join(HERE, "..", "codes", f"q8chain_len{n}.txt"))
        J, K = gens[n]
        k = n // 12
        lat_ok, rk = commutator_form_ok(C, n)
        orbs, seen = [], set()
        for i in range(n):
            if i not in seen:
                o = sorted({i, J[0][i], K[0][i], J[0][K[0][i]]})
                seen |= set(o)
                orbs.append(o)
        data = [orbit_data(J, K, o) for o in orbs]
        conj = all(d[0] for d in data)
        rel = all(d[1] for d in data)
        tr, st = [1] * 8, [1] * 8                           # product linearisation over the 3k orbits
        for d in data:
            tr = [x * y for x, y in zip(tr, d[2])]
            st = [x * y for x, y in zip(st, d[3])]
        per = [decompose([(t + s) / 2 for t, s in zip(d[2], d[3])]) for d in data]
        per_m = [decompose([(t - s) / 2 for t, s in zip(d[2], d[3])]) for d in data]
        def shape(p, q):              # p: one parity, q: the other; H in one, 2ψ (a single ψ, twice) in the other
            lin = lambda d: [d[kk].real for kk in d if kk != "H"]
            return (close(p["H"].real, 1) and close(sum(lin(p)), 0) and close(q["H"].real, 0)
                    and close(max(lin(q)), 2) and close(sum(lin(q)), 2))
        orbit_shape = all(shape(p, q) or shape(q, p) for p, q in zip(per, per_m))
        I = tr[6] / (tr[2] * tr[4])
        full = None
        if n == 24:                                      # the trace factorisation, checked on the full Cl(24)
            FJ, FK = {0: 1}, {0: 1}
            for d in data:
                FJ, FK = mul(FJ, d[4][0]), mul(FK, d[4][1])
            tJ, tK = FJ.get(0, 0), FK.get(0, 0)
            tJK = sum(v * FK.get(m, 0) * msign(m, m) for m, v in FJ.items())
            full = tJK / (tJ * tK) / 2 ** (n // 2) * 2 ** (3 * k)   # I·2^{3k}; traces = 2^{n/2} × identity coeff.
        out[n] = I
        print(f"1 q8chain_len{n} (k = {k}): basis of Λ(C) found {lat_ok}; F₂-rank of the commutator form on Λ/2Λ "
              f"= {rk} (of {n}), so dim T = 2^{n // 2}; {len(orbs)} orbits; Pin lifts φ_J, φ_K conjugate γ_i to "
              f"s_i γ_p(i): {conj}; linearised Q₈ relations: {rel}", flush=True)
        print(f"1   per orbit: T_O = H ⊕ (two 1-dim characters) in opposite parities: {orbit_shape}; "
              f"on T: character on (1,−1,±J,±K,±JK) = {[round(t.real) for t in tr[:3]]}.., "
              f"supercharacter at −1 = {round(st[1].real)}; I = t_JK/(t_J t_K) = {I.real:.3e} = 2^{-3 * k}: "
              f"{close(I * 2 ** (3 * k), 1)}" + (f"; on the full Cl(24): I·2^6 = {float(full):.6f}" if full else ""),
              flush=True)
    return out


# ------------------------------------------------------------------ Part 2
def eta(t, M=300):
    q = cmath.exp(2j * cmath.pi * t)
    p = cmath.exp(2j * cmath.pi * t / 24)
    for m in range(1, M):
        p *= 1 - q ** m
    return p


def twining(t, n):
    """Z(1, J)(τ) = 1/η_J(τ) = η(2τ)^{n/2} / η(4τ)^{n/2}."""
    return (eta(2 * t) / eta(4 * t)) ** (n // 2)


def fock_J(t, n):
    """Tr_{S[θ]} J^{±1} q^{L₀−c/24} (without T): q^{n/48} Π_{r odd} (1 + q^r)^{−n/2}."""
    q = cmath.exp(2j * cmath.pi * t)
    p = 1
    for r in range(1, 600, 2):
        p *= 1 + q ** r
    return cmath.exp(2j * cmath.pi * t * n / 48) * p ** (-(n // 2))


def fock_1(t, n):
    """Tr_{S[θ]} q^{L₀−c/24} = q^{n/48} Π_{m ∈ ½+ℤ≥0} (1 − q^m)^{−n}."""
    p = 1
    for r in range(1, 600, 2):
        p *= 1 - cmath.exp(1j * cmath.pi * t * r)          # q^{r/2}, computed without a branch of log q
    return cmath.exp(2j * cmath.pi * t * n / 48) * p ** (-n)


TAUS = (0.5 + 0.8j, 0.37 + 0.93j, 0.61 + 1.1j, 0.13 + 0.7j)


def part2():
    dev, dev2, path, conv = 0, 0, [], 0
    for k in range(1, 9):
        n = 12 * k
        target = 2 ** (3 * k) * cmath.exp(2j * cmath.pi * k / 8)
        for t in TAUS:
            N = twining(t / (1 - 2 * t), n) / fock_J(t, n)
            dev = max(dev, abs(N / target - 1))
            N2 = twining(t / (1 + 2 * t), n) / fock_J(t, n)
            dev2 = max(dev2, abs(N2 / target.conjugate() - 1))
            Zm = 2 ** (n // 2) * (eta(t) / eta(t / 2)) ** n          # Z(−1,1) = Z(1,−1)(−1/τ)
            conv = max(conv, abs(Zm / (2 ** (n // 2) * fock_1(t, n)) - 1))
        path.append((k, k % 4 == 0))
    print(f"2 N(τ) = Z(1,J)(τ/(1−2τ)) / Fock(τ) at {len(TAUS)} points τ, n = 12k, k = 1..8: N = 2^(3k)·e^(2πik/8) "
          f"(max relative deviation {dev:.1e}); chain S T^(−2) S gives 2^(3k)·e^(−2πik/8) (deviation {dev2:.1e}), "
          f"the same as S T² S iff 4 | k (<J> non-anomalous iff 4 | k); Z(−1,1) = dim T × Fock character "
          f"(deviation {conv:.1e}). Z(1,J) and the Fock factor are k-th powers of their n = 12 values, so "
          f"N = (8·e^(2πi/8))^k exactly for every k.", flush=True)
    return dev < 1e-9 and dev2 < 1e-9 and conv < 1e-9


# ------------------------------------------------------------------ Part 3
def part3(I_values):
    eps_list = QA.spin_structures(QA.Q8)
    A = [QA.anomaly(QA.Q8, e, "Reg", 8) for e in eps_list]
    assert len(set(A)) == 1
    A = A[0]
    ok, rows = True, []
    for k in range(1, 49):
        N = (8 * cmath.exp(2j * cmath.pi / 8)) ** k
        I = 2.0 ** (-3 * k)
        mu = 1 / (N * I)
        eta_val = cmath.exp(2j * cmath.pi * float((3 * k * A) % 1))
        ok &= abs(mu - eta_val) < 1e-9
        if k <= 8:
            rows.append(f"k={k}: μ = e^(2πi·{(Fr(-k, 8)) % 1})" + (" = −1" if k % 8 == 4 else " = 1" if k % 8 == 0 else ""))
    for n, I in I_values.items():
        k = n // 12
        N = (8 * cmath.exp(2j * cmath.pi / 8)) ** k
        mu = 1 / (N * I)
        print(f"3 q8chain_len{n} (k = {k}): μ = 1/(N·I) = {mu.real:+.6f}{mu.imag:+.6f}i", flush=True)
    print(f"3 A_Reg(S³/Q₈) = {A} (all 4 spin structures); " + "; ".join(rows), flush=True)
    print(f"3 μ = exp(2πi·3k·A_Reg(S³/Q₈)) for every k = 1..48: {ok}", flush=True)
    print("3 For 4 | k the chain lifts are the canonical ℤ₄-lifts, and μ = (−1)^(k/4). For k ≡ 4 mod 8, μ = −1: the "
          "canonical lifts of J, K, JK on V_(−1) do not form a Q₈-representation, so Q₈ is anomalous on V_Λ(C), "
          "although every cyclic restriction vanishes. For 8 | k, μ = 1.", flush=True)
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
        Iv = part1(QA.chain_gens())
        good2 = part2()
        good3 = part3(Iv)
        print(f"all checks pass: {good2 and good3}", flush=True)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
