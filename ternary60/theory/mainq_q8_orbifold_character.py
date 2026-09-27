"""The facts behind μ, proved: exact modular identities, and the S-invariance of a would-be Q₈-orbifold
(notes/main-question.md §8.5).

V = V_{Λ(C)}, n = 12k, 4 | k, Q₈ = <J, K> as in Thm 8.1. Functions (q = e^{2πiτ}, all with q^{L₀−c/24}):
  e = Z(1,−1)  = η(τ)^n / η(2τ)^n                           (only λ = 0 is fixed by −1)
  f = Z(1,x)   = η(2τ)^{n/2} / η(4τ)^{n/2},  x = ±J, ±K, ±JK  (only λ = 0 is fixed)
  E = ch V(−1) = 2^{n/2} q^{n/48} Π_{m ∈ ½+ℤ≥0} (1 − q^m)^{−n}         (V(−1) = S[θ] ⊗ T, dim T = 2^{n/2})
  g = ch V(x)  = 2^{n/4} q^{n/192} Π_{j odd} (1 − q^{j/4})^{−n/2}      (V(x) = S[x] ⊗ T_x, T_x = spinors of Cl(n/2))
  F = q^{n/48} Π_{r odd} (1 + q^r)^{−n/2}   (trace of x on the Fock space S[θ])
Part 1 (modular covariance, exact).
  (i) e|S = E; (ii) f|S = g; (iii) f|S T² S = N·F with N = (√2·e^{2πi/48})^{n/2} = 2^{3k}·e^{2πik/8}.
  Proof of (iii):
  - η(γτ) = ε(γ)·√(−i(cτ+d))·η(τ), with ε(γ) = exp(πi((a+d)/(12c) − s(d,c))) and s the Dedekind sum.
  - For γ₁ = (−1 0; 1 −1) and γ₂ = (−2 −1; 1 0) both multipliers are e^{−πi/6}, and they cancel.
  - The square roots give √2.
  - η(τ − ½) = e^{−2πi/48} η(2τ)³/(η(τ)η(4τ)).
  The script evaluates the multipliers exactly and checks every step numerically.
Part 2 (the orbifold character). If Q₈ were non-anomalous, the holomorphic SVOA W = V//Q₈ = ⊕_{[g]} V(g)^{C(g)}
  would exist (GJF Thm 4.2), with even, genuine centraliser actions. Their only freedom:
  - on V(−1): ρ = ψ ⊗ ρ̃ for some ψ ∈ Hom(Q₈, ±1) (Schur and Lemma 8.3); Tr ρ̃(−1)|_T = 0 and Tr ρ̃(x)|_T = t_x;
  - on V(x): ρ_x(x) = ε·e^{2πiL₀}·P, so odd powers have trace 0 (sdim T_x = 0); ε² = 1 by spin–statistics in W.
  So ch W = Z(1,1)/8 + e/8 + (6/8)f + E/8 + (1/4)(Σ_x ψ(x)t_x)·F + (3/4)(g + g(τ+2)), and Z(1,1) is S-invariant.
  By (i)–(iii), and since F and g(τ+2) are linearly independent, S-invariance of ch W ⟺ Σ_x ψ(x) t_x = 3N.
  With t_x = 2^{3k} (Clifford computation on the chain codes) this reads ψ(J)+ψ(K)+ψ(JK) = 3e^{2πik/8}.
  That is possible iff 8 | k (and then only for ψ = 1). This is the statement "non-anomalous ⇒ μ = 1", with the
  trivial phases derived rather than assumed. The script also evaluates the reduced S-defect numerically for each ψ.
"""
import cmath, os, sys
from fractions import Fraction as Fr
from existence_common import HERE
from mainq_common import read_code
import mainq_q8_anomaly as QA
import mainq_q8_twisted as TW

eta = TW.eta
TAUS = (0.31 + 1.02j, 0.47 + 0.88j, 0.12 + 1.21j)


def dedekind(d, c):
    """s(d, c) = Σ_{r=1}^{c−1} ((r/c))((dr/c)), exact."""
    def saw(x):
        x = Fr(x)
        return Fr(0) if x.denominator == 1 else x - (x.numerator // x.denominator) - Fr(1, 2)
    return sum((saw(Fr(r, c)) * saw(Fr(d * r, c)) for r in range(1, c)), Fr(0))


def eta_multiplier(a, b, c, d):
    """ε(γ) as a fraction x with ε = e^{πi x}, for c > 0."""
    assert c > 0 and a * d - b * c == 1
    return Fr(a + d, 12 * c) - dedekind(d % c, c)


def e_fn(t, n):
    return (eta(t) / eta(2 * t)) ** n


def f_fn(t, n):
    return TW.twining(t, n)


def E_fn(t, n):
    return 2 ** (n // 2) * TW.fock_1(t, n)


def F_fn(t, n):
    return TW.fock_J(t, n)


def g_fn(t, n):
    p = 1
    for j in range(1, 1200, 2):
        p *= 1 - cmath.exp(2j * cmath.pi * t * j / 4)
    return 2 ** (n // 4) * cmath.exp(2j * cmath.pi * t * n / 192) * p ** (-(n // 2))


def part1():
    m1, m2 = eta_multiplier(-1, 0, 1, -1), eta_multiplier(-2, -1, 1, 0)
    dev = {"eta(t-1/2)": 0, "(i) e|S = E": 0, "(ii) f|S = g": 0, "(iii) f|ST²S = N·F": 0, "sqrt ratio": 0}
    for t in TAUS:
        lhs = eta(t - 0.5)
        rhs = cmath.exp(-2j * cmath.pi / 48) * eta(2 * t) ** 3 / (eta(t) * eta(4 * t))
        dev["eta(t-1/2)"] = max(dev["eta(t-1/2)"], abs(lhs / rhs - 1))
        r = cmath.sqrt(-1j * (2 * t - 1)) / cmath.sqrt(-1j * (t - 0.5))
        dev["sqrt ratio"] = max(dev["sqrt ratio"], abs(r - 2 ** 0.5))
        for k in (4, 8):
            n = 12 * k
            N = 2 ** (3 * k) * cmath.exp(2j * cmath.pi * k / 8)
            dev["(i) e|S = E"] = max(dev["(i) e|S = E"], abs(e_fn(-1 / t, n) / E_fn(t, n) - 1))
            dev["(ii) f|S = g"] = max(dev["(ii) f|S = g"], abs(f_fn(-1 / t, n) / g_fn(t, n) - 1))
            dev["(iii) f|ST²S = N·F"] = max(dev["(iii) f|ST²S = N·F"],
                                           abs(f_fn(t / (1 - 2 * t), n) / (N * F_fn(t, n)) - 1))
    ok = m1 == m2 == Fr(-1, 6) and all(v < 1e-9 for v in dev.values())
    print(f"1 eta multipliers (exact, Dedekind sums): ε(γ₁) = e^(πi·{m1}), ε(γ₂) = e^(πi·{m2}) — they cancel; "
          f"√(−i(2τ−1))/√(−i(τ−½)) = √2; η(τ−½) = e^(−2πi/48)η(2τ)³/(η(τ)η(4τ)). Hence "
          f"η(2τ′)/η(4τ′) = √2·e^(2πi/48)·η(τ)η(4τ)/η(2τ)² for τ′ = τ/(1−2τ), and N = (√2·e^(2πi/48))^(n/2) "
          f"= 2^(3k)·e^(2πik/8) exactly.", flush=True)
    print("1 numerical confirmation (max relative deviation over 3 points τ, n = 48, 96): "
          + "; ".join(f"{kk} {v:.1e}" for kk, v in dev.items()) + f"; all ok: {ok}", flush=True)
    return ok


def part2():
    gens = QA.chain_gens()
    rows, ok = [], True
    for k in (4, 8, 12, 16):
        n = 12 * k
        if n in (48, 96):                                   # traces from the Clifford computation on the codes
            J, K = gens[n]
            orbs, seen = [], set()
            for i in range(n):
                if i not in seen:
                    o = sorted({i, J[0][i], K[0][i], J[0][K[0][i]]})
                    seen |= set(o)
                    orbs.append(o)
            tr = [1] * 8
            for o in orbs:
                d = TW.orbit_data(J, K, o)
                tr = [x * y for x, y in zip(tr, d[2])]
            t = {"J": tr[2], "K": tr[4], "JK": tr[6]}
            ok &= abs(tr[1]) < 1e-9 and all(abs(tr[2 * i + 3] - tr[2 * i + 2]) < 1e-9 for i in range(3))
            src = "Clifford on q8chain_len%d" % n
        else:
            t = {"J": 2 ** (3 * k), "K": 2 ** (3 * k), "JK": 2 ** (3 * k)}
            src = "universal (Lemma 8.3)"
        N = 2 ** (3 * k) * cmath.exp(2j * cmath.pi * k / 8)
        passing = []
        for sj, sk in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
            psi = {"J": sj, "K": sk, "JK": sj * sk}
            T = sum(psi[x] * t[x] for x in t)
            cond = abs(T - 3 * N) < 1e-6 * abs(N)
            # reduced S-defect of (1/4)[3 g(τ+2) + T·F] (the other terms are S-invariant by (i), (ii))
            dmax = 0
            for tau in TAUS:
                red = lambda s: 0.25 * (3 * g_fn(s + 2, n) + T * F_fn(s, n))
                dmax = max(dmax, abs(red(-1 / tau) - red(tau)) / abs(0.25 * 3 * g_fn(tau + 2, n)))
            if cond:
                passing.append(psi)
            ok &= cond == (dmax < 1e-8)
            rows.append(f"k={k}, ψ(J,K,JK)=({sj:+d},{sk:+d},{sj * sk:+d}): Σψ(x)t_x/2^(3k) = "
                        f"{(T / 2 ** (3 * k)).real:+.0f}, 3N/2^(3k) = {3 * N / 2 ** (3 * k):.3f}; reduced S-defect "
                        f"{dmax:.1e}")
        print(f"2 k = {k} (t_x from {src}): characters ψ with S-invariant ch W: "
              f"{[tuple(p.values()) for p in passing] or 'none'} ⇒ " +
              ("Q₈ anomalous" if not passing else "consistent (ψ = 1)"), flush=True)
        ok &= (len(passing) == 0) == (k % 8 == 4) and all(p == {"J": 1, "K": 1, "JK": 1} for p in passing)
    for r in rows:
        print("2   " + r, flush=True)
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
        a = part1()
        b = part2()
        print(f"all checks pass: {a and b}", flush=True)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
