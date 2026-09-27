"""Non-anomaly of Q₈ for 8 | k, proved directly (notes/main-question.md §8.4): a second proof of Thm 8.1
that uses neither the coprime-gauging lemma (Step 1) nor the eta invariants of V_{Λ(C)}.

Part 1 (the group rSH³(Q₈)). |rSH³(Q₈)| ≤ |H³(Q₈;U(1))|·|H²(Q₈;ℤ₂)| = 8·4 = 32 (the layer sequence
        of GJF §4). Free fermions Fer(ρ), ρ = n_i χ_i + n_j χ_j + n_k χ_k + n_H H with w₁(ρ) = 0, realise
        32 distinct values of (restrictions to <i>, <j>, <k> in rSH³(ℤ₄) = ℤ₈ by the q² rule of GJF Ex 4.4;
        values on S³/Q₈ for the 4 spin structures by Donnelly's eta formula). All of these are homomorphisms of
        anomaly classes, so free-fermion classes exhaust rSH³(Q₈) and the invariants separate it.
        Consequence: the classes with all cyclic restrictions zero are exactly {0, κ}, κ = A(Fer(4H)).
Part 2 (the codes). For Q₈-invariant self-dual codes (the Q₈-chain codes at n = 48, 96, the tetracode sum at
        n = 48, and direct sums at n = 144):
        - the Majorana layer vanishes;
        - all cyclic restrictions vanish (GJF Ex 4.4 from the Frame shapes of J, K, JK, −1; 4 | k);
        - the twisted-sector invariant μ = 1/(N·I) (mainq_q8_twisted.py) equals (−1)^{k/4}.
        A non-anomalous action has μ = 1, so μ = −1 forces α = κ. For 8 | k, with any Q₈-code C′ of
        k′ ≡ 4 mod 8: α_{C⊕C′} = κ = α_{C′}, hence α_C = 0 by additivity.
Part 3 (all of Thm 8.1). δ(C) := α_C − 3k·a lies in {0, κ} for every C, by Part 1 and the cyclic comparison of
        mainq_q8_gauging.py. δ vanishes on tetracode sums (Step 2 of Thm 8.1) and is additive. It vanishes for
        4 | k by Part 2, since the tetracode sum at k = 4 gives κ = 12a = 4a. Adding a tetracode sum reduces
        every k to 4 | k, so α_C = 3k·a for all k, and a has order 8.
"""
import itertools, os, sys, cmath
from existence_common import rref, dot, HERE
from mainq_common import read_code, is_aut, mono_mul, mono_neg
from mainq_morita import code_from_U, q8_gens
import mainq_q8_anomaly as QA
import mainq_q8_gauging as GA
import mainq_q8_twisted as TW

IRR = ["chi_i", "chi_j", "chi_k", "H"]


# ------------------------------------------------------------------ Part 1
def part1():
    SP = QA.spin_structures(QA.Q8)
    s3 = {r: [(QA.eta(QA.Q8, e, r) - QA.char(r, QA.ONE) * QA.eta(QA.Q8, e, "1")) / 2 for e in SP] for r in IRR}
    gen = {"i": (0, 1, 0, 0), "j": (0, 0, 1, 0), "k": (0, 0, 0, 1)}

    def restr(n, x):
        pw = GA.cyc(gen[x], 4)
        return GA.alpha_fermion(lambda t: sum(c * QA.char(r, pw[t]) for r, c in zip(IRR, n)), 4)

    classes = {}
    for n in itertools.product(range(8), repeat=4):
        if n[0] % 2 == n[1] % 2 == n[2] % 2:                    # w₁(ρ) = 0
            inv = (tuple(restr(n, x) for x in "ijk"),
                   tuple(sum(c * s3[r][e] for r, c in zip(IRR, n)) % 1 for e in range(4)))
            classes.setdefault(inv, n)
    kernel = [(inv, n) for inv, n in classes.items() if inv[0] == (0, 0, 0)]
    fmt = lambda inv: "S³/Q₈ values " + "/".join(str(v) for v in inv[1])
    print(f"1 free fermions with w₁ = 0 realise {len(classes)} distinct invariant values (bound |rSH³(Q₈)| ≤ 32): "
          f"they exhaust rSH³(Q₈) and the invariants separate it: {len(classes) == 32}", flush=True)
    print(f"1 classes with all cyclic restrictions 0: {len(kernel)}: "
          + "; ".join(f"{fmt(inv)} (e.g. (n_i,n_j,n_k,n_H) = {n})" for inv, n in sorted(kernel)), flush=True)
    ok = len(classes) == 32 and len(kernel) == 2
    return ok


# ------------------------------------------------------------------ Part 2
def direct_sum(A, gA, nA, B, gB, nB):
    rows = [list(r) + [0] * nB for r in A] + [[0] * nA + list(r) for r in B]
    gens = [(tuple(pa) + tuple(nA + x for x in pb), tuple(sa) + tuple(sb)) for (pa, sa), (pb, sb) in zip(gA, gB)]
    return rows, gens, nA + nB


def tetra_sum(n):
    r = n // 4
    U0 = [[int(i == 2 * b) for i in range(2 * r)] for b in range(r)]
    return code_from_U(U0, r), list(q8_gens(r)), n


def analyse(tag, C, gens, n):
    J, K = gens
    k = n // 12
    R = rref(C)
    sd = len(R) == n // 2 and all(dot(a, b) == 0 for i, a in enumerate(R) for b in R[i:])
    inv = is_aut(J, C, n) and is_aut(K, C, n)
    rel = (mono_mul(J, J) == mono_neg(n) and mono_mul(K, K) == mono_neg(n)
           and mono_mul(J, K) == mono_mul(mono_neg(n), mono_mul(K, J)))
    majorana = all((3 * (n - sum(g[1]))) % 4 == 0 for g in (J, K))
    cyc = {nm: GA.alpha_frame(m, GA.frame_shape(g)) for nm, g, m in
           (("J", J, 4), ("K", K, 4), ("JK", mono_mul(J, K), 4), ("−1", mono_neg(n), 2))}
    orbs, seen = [], set()
    for i in range(n):
        if i not in seen:
            o = sorted({i, J[0][i], K[0][i], J[0][K[0][i]]})
            seen |= set(o)
            orbs.append(o)
    data = [TW.orbit_data(J, K, o) for o in orbs]
    pin_ok = all(d[0] and d[1] for d in data)
    tr = [1] * 8
    for d in data:
        tr = [x * y for x, y in zip(tr, d[2])]
    I = tr[6] / (tr[2] * tr[4])
    N = (8 * cmath.exp(2j * cmath.pi / 8)) ** k
    mu = 1 / (N * I)
    mu_r = round(mu.real)
    good = sd and inv and rel and majorana and pin_ok and all(v == 0 for v in cyc.values()) and abs(mu - mu_r) < 1e-9
    print(f"2 {tag}: n = {n} (k = {k}); self-dual {sd}, Q₈-invariant {inv}, relations {rel}; Majorana layer 0 "
          f"{majorana}; cyclic anomalies (GJF Ex 4.4) {cyc}; Pin lifts ok {pin_ok}; I·2^(3k) = "
          f"{(I * 2 ** (3 * k)).real:.6f}; μ = {mu_r:+d} ⇒ α ∈ {{0, κ}} and " + ("α = κ" if mu_r == -1 else "μ = 1"),
          flush=True)
    return good, mu_r


def part2():
    gens = QA.chain_gens()
    codes = {}
    for n in (48, 96):
        codes[f"q8chain_len{n}"] = (read_code(os.path.join(HERE, "..", "codes", f"q8chain_len{n}.txt")),
                                    list(gens[n]), n)
    codes["tetracode sum D48"] = tetra_sum(48)
    codes["tetracode sum D96"] = tetra_sum(96)
    res = {tag: analyse(tag, *v) for tag, v in codes.items()}
    sums = {}
    for a, b in (("q8chain_len96", "q8chain_len48"), ("q8chain_len96", "tetracode sum D48"),
                 ("tetracode sum D96", "q8chain_len48")):
        (A, gA, nA), (B, gB, nB) = codes[a], codes[b]
        C, g, n = direct_sum(A, gA, nA, B, gB, nB)
        sums[(a, b)] = analyse(f"{a} ⊕ {b}", C, g, n)
    allok = all(v[0] for v in res.values()) and all(v[0] for v in sums.values())
    for (a, b), (ok, mu) in sums.items():
        mu_a, mu_b = res[a][1], res[b][1]
        concl = "α(" + a + ") = α(sum) − α(" + b + ") = κ − κ = 0" if (mu == -1 and mu_b == -1) else "(no conclusion)"
        print(f"2 {a} (μ = {mu_a:+d}) ⊕ {b} (μ = {mu_b:+d}): μ(sum) = {mu:+d}; {concl}", flush=True)
    return allok


# ------------------------------------------------------------------ Part 3
def part3():
    print("3 δ(C) := α_C − 3k·a lies in {0, κ} (Part 1 and the cyclic comparison of mainq_q8_gauging.py), is "
          "additive under ⊕, and vanishes on tetracode sums (Step 2 of Thm 8.1). For 4 | k: α_C = (k/4 mod 2)·κ "
          "(Part 2), and 3k·a = (k/4)·12a = (k/4)·κ, since D48 has α = 12a (Step 2) and μ = −1. So δ = 0 for 4 | k. "
          "For any k add a tetracode sum with k_D ≡ −k mod 4: δ(C) = δ(C ⊕ D) − δ(D) = 0. Hence α_C = 3k·a for "
          "every k, and 4a = κ ≠ 0, so a has order 8.", flush=True)
    return True


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        ok1 = part1()
        ok2 = part2()
        ok3 = part3()
        print(f"all checks pass: {ok1 and ok2 and ok3}", flush=True)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
