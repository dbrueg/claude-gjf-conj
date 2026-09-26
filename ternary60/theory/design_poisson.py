"""Finite Poisson proof of the off-diagonal signed 2-design (◆) (ternary-code-index.md §2, Proof II′).

g_ij(x) := Π_{k≠i,j} φ(x_k) · [x_i≠0][x_j≠0],  G_ij(X) := Σ_{x∈X} g_ij(x).
For a self-dual C, G_ij(C) = Σ_{ε∈F} s(ε) ε_i ε_j, the off-diagonal entry of (◆).

Claim [P]: ĝ_ij(u) = (i√3)^{n−2} Π_{k≠i,j} φ(u_k) (3[u_i=0]−1)(3[u_j=0]−1).  For a self-orthogonal D whose
words have weight ≡ 0 mod 3, the words that are full weight off {i,j} but vanish at i or j have weight n−1
or n−2 and do not exist when 3 | n. So Poisson gives, for 12 | n:
    G(C) = −G(C)/3 for C self-dual  ⇒  G(C) = 0,        G(D^⊥) = −G(D) for dim D = n/2 − 1.
Checks:
 1. the Fourier formula for ĝ_ij, brute force over all x, u ∈ F₃ⁿ at n = 4, 8 (all i < j);
 2. G_ij(C) = 0 for all i < j, and Σ_{u∈C} ĝ_ij(u) = |C|·G_ij(C) (Poisson), exactly (ℤ[ω] via integer
    formula) on random self-dual C at n = 12, 24;
 3. neighbour propagation: random neighbours C, C′ with D = C ∩ C′ at n = 12, 24: G(D^⊥) = −G(D),
    G(C) + G(C′) = 0, and how often G(D) ≠ 0 (so the D-identity is not vacuous);
 4. the vanishing classes: no word of C is full weight off {i,j} with a zero at i or j.
"""
import itertools, os, random, cmath
from existence_common import PHI, dot, nbr, rand_iso, HERE
from ternary import random_self_dual

OUT = []


def say(s):
    print(s, flush=True); OUT.append(s)


def span(B, n):
    words = [tuple([0] * n)]
    for g in B:
        g1 = tuple(x % 3 for x in g); g2 = tuple((2 * x) % 3 for x in g)
        words = words + [tuple((a + b) % 3 for a, b in zip(w, g1)) for w in words] \
                      + [tuple((a + b) % 3 for a, b in zip(w, g2)) for w in words]
    return words


def g(x, i, j):
    if not x[i] or not x[j]:
        return 0
    p = 1
    for k, a in enumerate(x):
        if k != i and k != j:
            p *= PHI[a]
            if not p:
                return 0
    return p


def ghat_formula(u, i, j, n):
    """ĝ(u) / (i√3)^{n−2} as an integer (the power is a common factor)."""
    p = (3 * (u[i] == 0) - 1) * (3 * (u[j] == 0) - 1)
    for k, a in enumerate(u):
        if k != i and k != j:
            p *= PHI[a]
            if not p:
                return 0
    return p


def check1():
    w = cmath.exp(2j * cmath.pi / 3)
    worst = 0.0; N = 0
    for n in (4, 8):
        allx = list(itertools.product(range(3), repeat=n))
        c = (1j * 3 ** 0.5) ** (n - 2)
        for i, j in itertools.combinations(range(n), 2):
            gx = [(x, g(x, i, j)) for x in allx]
            gx = [(x, v) for x, v in gx if v]
            for u in allx:
                lhs = sum(v * w ** (dot(u, x)) for x, v in gx)
                worst = max(worst, abs(lhs - c * ghat_formula(u, i, j, n))); N += 1
    say(f"1 Fourier formula for ĝ_ij: max error {worst:.1e} over {N} (n, i, j, u) at n = 4, 8 (brute force)")


def check2(rng):
    for n, trials in ((12, 6), (24, 3)):
        okG = okP = 0; tot = 0; bad4 = 0; nonzero_index = 0
        for _ in range(trials):
            B, _ = random_self_dual(n, rng)
            W = span(B, n)
            full = [x for x in W if all(x)]
            nonzero_index += bool(sum((-1) ** sum(1 for a in x if a == 1) for x in full))
            pairs = list(itertools.combinations(range(n), 2))
            if n == 24:
                pairs = rng.sample(pairs, 12)
            for i, j in pairs:
                tot += 1
                G = sum(g(x, i, j) for x in W)
                okG += G == 0
                # Poisson: Σ_{u∈C} ĝ(u) = |C| G(C); ĝ = (i√3)^{n−2}·formula, (i√3)^{n−2} = −3^{n/2−1} for 4 | n
                S = sum(ghat_formula(u, i, j, n) for u in W)
                okP += (-(3 ** (n // 2 - 1)) * S == len(W) * G)
                bad4 += sum(1 for u in W if (u[i] == 0 or u[j] == 0)
                            and all(u[k] for k in range(n) if k not in (i, j)))
        say(f"2 n = {n}: G_ij(C) = 0 on {okG}/{tot} (C, i, j); Poisson identity on {okP}/{tot}; "
            f"{trials} random codes, {nonzero_index} with Index ≠ 0")
        say(f"4 n = {n}: words full weight off {{i,j}} with a zero at i or j: {bad4}")


def check3(rng):
    for n, trials in ((12, 30), (24, 6)):
        okD = okC = 0; tot = 0; nzD = 0
        for _ in range(trials):
            B, _ = random_self_dual(n, rng)
            x = rand_iso(B, n, rng)
            B2 = nbr(B, x)
            # D = C ∩ C′ = C ∩ x^⊥ ; D^⊥ = C + C′
            s = [dot(r, x) for r in B]
            p = next(k for k, t in enumerate(s) if t)
            D = [[(a - ((s[k] * (1 if s[p] == 1 else 2)) % 3) * b) % 3 for a, b in zip(B[k], B[p])]
                 for k in range(len(B)) if k != p]
            Dperp = D + [B[p], list(x)]
            WD, WDp, WC, WC2 = span(D, n), span(Dperp, n), span(B, n), span(B2, n)
            assert len(set(WDp)) == 3 ** (n // 2 + 1)
            pairs = list(itertools.combinations(range(n), 2))
            if n == 24:
                pairs = rng.sample(pairs, 8)
            for i, j in pairs:
                tot += 1
                gD = sum(g(v, i, j) for v in WD)
                gDp = sum(g(v, i, j) for v in WDp)
                okD += gDp == -gD
                okC += sum(g(v, i, j) for v in WC) + sum(g(v, i, j) for v in WC2) == 0
                nzD += gD != 0
        say(f"3 n = {n}: G(D^⊥) = −G(D) on {okD}/{tot}; G(C) + G(C′) = 0 on {okC}/{tot}; G(D) ≠ 0 on {nzD}/{tot} "
            f"({trials} random neighbour pairs)")


if __name__ == "__main__":
    rng = random.Random(5)
    check1(); check2(rng); check3(rng)
    with open(os.path.join(HERE, "design_poisson.log"), "w") as fh:
        fh.write("\n".join(OUT) + "\n")
