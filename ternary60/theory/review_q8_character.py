"""Review check (2026-09-28, paper/review-2026-09-28.md): the q-series facts behind the Q₈ anomaly argument
(notes/main-question.md §8.5, notes/blueprint/anomalies.md Lemma 4.6 and Prop 4.7), recomputed with fresh
code (stdlib complex arithmetic only; nothing imported from the other scripts).

The point of the check is a shorter proof of Lemma 8.5.1(iii) = [AN] Lemma 4.6(iii): instead of the eta
multipliers of two matrices γ₁, γ₂ (Dedekind sums), use
    (ii)   f|S = g,
    (iii') g(τ+2) = N·F(−1/τ), from η(τ+1) = e^{2πi/24}η(τ), η(−1/τ) = √(−iτ)η(τ) and Euler's
           η(w+½) = e^{2πi/48} η(2w)³/(η(w)η(4w)),
so that f|ST²S = (g|T²)|S = N·F|S² = N·F. Both (iii') and (iii) are checked numerically below, together
with (i), (ii), and the S-defect of the would-be orbifold character
    ch W = Z(1,1)/8 + e/8 + (6/8) f + E/8 + (1/4) T_ψ F + (3/4)(g + g(τ+2)),
    ch W|S − ch W = ¼ (3N − T_ψ)(F − F|S),   T_ψ = 2^{3k} (ψ(J) + ψ(K) + ψ(JK)),
for tetracode sums (Λ = ℤⁿ, Z(1,1) = θ₃ⁿ/ηⁿ) at k = 4 and 8 and all four characters ψ of Q₈.
"""
import cmath
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = []


def log(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def eta(tau, terms=400):
    q = cmath.exp(2j * math.pi * tau)
    p = 1
    qn = 1
    for _ in range(terms):
        qn *= q
        p *= (1 - qn)
        if abs(qn) < 1e-18:
            break
    return cmath.exp(2j * math.pi * tau / 24) * p


def theta3(tau, terms=60):
    return sum(cmath.exp(1j * math.pi * m * m * tau) for m in range(-terms, terms + 1))


def funcs(tau, n):
    """e, f, E, g, F of [AN] Lemma 4.5/4.6 (as eta quotients; E, g, F also as the q-products)."""
    e = (eta(tau) / eta(2 * tau)) ** n
    f = (eta(2 * tau) / eta(4 * tau)) ** (n // 2)
    E = 2 ** (n / 2) * (eta(tau) / eta(tau / 2)) ** n
    g = 2 ** (n / 4) * (eta(tau / 2) / eta(tau / 4)) ** (n // 2)
    F = (eta(tau) * eta(4 * tau) / eta(2 * tau) ** 2) ** (n // 2)
    return e, f, E, g, F


def qprod_checks(tau, n):
    """E, g, F against their defining q-products."""
    q = cmath.exp(2j * math.pi * tau)
    qh = cmath.exp(2j * math.pi * tau / 2)
    qq = cmath.exp(2j * math.pi * tau / 4)
    E = 2 ** (n / 2) * cmath.exp(2j * math.pi * tau * n / 48)
    g = 2 ** (n / 4) * cmath.exp(2j * math.pi * tau * n / 192)
    F = cmath.exp(2j * math.pi * tau * n / 48)
    for j in range(1, 400, 2):
        E /= (1 - qh ** j) ** n
        g /= (1 - qq ** j) ** (n // 2)
        F /= (1 + q ** j) ** (n // 2)
    return E, g, F


def rel(a, b):
    return abs(a - b) / max(abs(a), abs(b), 1e-300)


def main():
    pts = [0.5 + 0.5j, 0.37 + 0.81j, -0.2 + 0.7j, 0.1 + 1.3j]
    worst = 0.0
    for n in (12, 48, 96):
        k = n // 12
        N = (math.sqrt(2) * cmath.exp(2j * math.pi / 48)) ** (n // 2)
        assert abs(N - 2 ** (3 * k) * cmath.exp(2j * math.pi * k / 8)) < 1e-9 * abs(N)
        for tau in pts:
            e, f, E, g, F = funcs(tau, n)
            Eq, gq, Fq = qprod_checks(tau, n)
            S = -1 / tau
            eS, fS, ES, gS, FS = funcs(S, n)
            tp = tau / (1 - 2 * tau)
            _, fp, _, _, _ = funcs(tp, n)
            _, _, _, g2, _ = funcs(tau + 2, n)
            checks = [rel(E, Eq), rel(g, gq), rel(F, Fq),
                      rel(eS, E), rel(fS, g),               # (i), (ii)
                      rel(g2, N * FS),                      # (iii')
                      rel(fp, N * F)]                       # (iii)
            worst = max(worst, max(checks))
    log(f"(i) e|S = E, (ii) f|S = g, (iii') g(τ+2) = N·F|S, (iii) f(τ/(1−2τ)) = N·F, and the q-products of "
        f"E, g, F: n = 12, 48, 96 at {len(pts)} points; max relative error {worst:.1e}")
    assert worst < 1e-9

    # the S-defect of the would-be orbifold character (tetracode sums, Z(1,1) = θ3^n/η^n)
    chars = {"1": (1, 1, 1), "χ_i": (1, -1, -1), "χ_j": (-1, 1, -1), "χ_k": (-1, -1, 1)}
    for n in (48, 96):
        k = n // 12
        N = 2 ** (3 * k) * cmath.exp(2j * math.pi * k / 8)
        for name, (pJ, pK, pJK) in chars.items():
            Tpsi = 2 ** (3 * k) * (pJ + pK + pJK)
            defects = []
            for tau in pts[:2]:
                def chW(t):
                    e, f, E, g, F = funcs(t, n)
                    _, _, _, g2, _ = funcs(t + 2, n)
                    Z = (theta3(t) / eta(t)) ** n
                    return Z / 8 + e / 8 + 6 * f / 8 + E / 8 + Tpsi * F / 4 + 3 * (g + g2) / 4
                lhs = chW(-1 / tau) - chW(tau)
                _, _, _, _, F = funcs(tau, n)
                _, _, _, _, FS = funcs(-1 / tau, n)
                rhs = (3 * N - Tpsi) * (F - FS) / 4
                scale = abs(chW(tau))
                assert abs(lhs - rhs) < 1e-8 * scale, (n, name, lhs, rhs)
                defects.append(abs(lhs) / scale)
            inv = max(defects) < 1e-9
            log(f"k = {k}, ψ = {name:4}: ch W|S − ch W = ¼(3N − T_ψ)(F − F|S) holds; "
                f"S-invariant: {inv} (relative defect {max(defects):.1e})")
            assert inv == (k % 8 == 0 and name == "1")
    log("all checks passed")
    with open(os.path.join(HERE, "review_q8_character.log"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
