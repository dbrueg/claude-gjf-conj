"""Critical check of the finite proof of 24 | Index (paper/divisibility.tex, Variant C; notes §2 Step 1′).

Independent of design_poisson.py. All arithmetic is exact: Z[ω] as pairs (a, b) = a + bω with ω² = −1 − ω,
and i√3 = ω − ω² = 1 + 2ω.

 1. One-coordinate transforms, exactly: φ̂ = (i√3)φ, (1_{≠0})^ = 3δ₀ − 1, (i√3)² = −3.
 2. The crux, POINTWISE and by brute force (no product formula): ĝ_ij(u) = −3^{n/2−1} g_ij(u) for every u ∈ C,
    at n = 12 (Golay, code2, a random code), several pairs (i, j).
 3. Hypotheses are needed: for random 6-dim C ⊂ F₃¹² that are NOT self-orthogonal, the general Poisson identity
    3·G(C^⊥) = −[G(C) − 2(A₀ₙ + Aₙ₀) + 4A₀₀] holds exactly, the correction terms A are nonzero, and G(C^⊥) ≠ 0 occurs.
 4. Beyond two points: with K = {a,b,c,d} the same computation predicts Σ_F s(ε)ε_aε_bε_cε_d = −W_K, where W_K is the
    φ-signed count of codewords vanishing on exactly three points of K and nowhere else. Checked on Golay (all 495 K),
    code2, and random codes at n = 24; also shows the 4-point sums are not determined by Index (no 4-design).
 5. Steps 2–3 exactly on random codes at n = 24: Σ_{ε_a=ε_b=ε_c} s = Index/4, Σ s(ε·x)² = Index·|x|² with 9 | LHS for
    x = ε₀ + 3y, y ∈ {0, ±e₁}, and some such x with v₃(|x|²) = 1.
 6. Golay: the 12 maximal words up to sign form a Hadamard matrix (HHᵀ = 12I), the n = 12 case of the design.
 7. The Rust `design` check (exact (◆), triple count, Step 3) at n = 36, 48, 60, including P(17), P(23), XQR(47),
    P(29), XQR(59).
"""
import itertools, os, random, subprocess
from collections import Counter
from existence_common import PHI, dot, GOLAY, CODE2, HERE, BIN
from ternary import random_self_dual, nullspace, rref

OUT = []


def say(s):
    print(s, flush=True); OUT.append(s)


# ---------------------------------------------------------------- exact Z[ω]
def zadd(p, q): return (p[0] + q[0], p[1] + q[1])
def zmul(p, q):
    a, b = p; c, d = q
    return (a * c - b * d, a * d + b * c - b * d)
def zscale(k, p): return (k * p[0], k * p[1])
OMP = [(1, 0), (0, 1), (-1, -1)]            # ω^0, ω^1, ω^2
ISQ3 = (1, 2)                                # i√3


def zpow(p, e):
    r = (1, 0)
    for _ in range(e):
        r = zmul(r, p)
    return r


def span(B, n):
    words = [tuple([0] * n)]
    for g in B:
        g1 = tuple(x % 3 for x in g); g2 = tuple((2 * x) % 3 for x in g)
        words = words + [tuple((a + b) % 3 for a, b in zip(w, g1)) for w in words] \
                      + [tuple((a + b) % 3 for a, b in zip(w, g2)) for w in words]
    return words


def f(x):
    p = 1
    for a in x:
        p *= PHI[a]
        if not p:
            return 0
    return p


def prod_off(x, K):
    p = 1
    for k, a in enumerate(x):
        if k not in K:
            p *= PHI[a]
            if not p:
                return 0
    return p


def check1():
    ok_phi = all(sum_z([zscale(PHI[a], OMP[(a * b) % 3]) for a in range(3)]) == zscale(PHI[b], ISQ3) for b in range(3))
    ok_ind = all(sum_z([OMP[(a * b) % 3] for a in (1, 2)]) == (3 * (b == 0) - 1, 0) for b in range(3))
    say(f"1 exact one-coordinate transforms: φ̂ = (i√3)φ {ok_phi}; (1_≠0)^ = 3δ₀ − 1 {ok_ind}; (i√3)² = {zmul(ISQ3, ISQ3)} (= −3)")


def sum_z(lst):
    r = (0, 0)
    for p in lst:
        r = zadd(r, p)
    return r


def check2(rng):
    n = 12
    B3, _ = random_self_dual(n, rng)
    codes = [("Golay", GOLAY), ("code2", CODE2), ("random", B3)]
    supp = list(itertools.product((1, 2), repeat=n))      # support of g_ij (all coordinates nonzero)
    for name, B in codes:
        W = span(B, n)
        pairs = [(0, 1), (2, 7), (5, 11)]
        okp = 0; tot = 0; G = []
        for i, j in pairs:
            gx = [(x, prod_off(x, (i, j))) for x in supp]
            target = -(3 ** (n // 2 - 1))
            for u in W:
                cnt = [0, 0, 0]
                for x, v in gx:
                    cnt[(u[0]*x[0]+u[1]*x[1]+u[2]*x[2]+u[3]*x[3]+u[4]*x[4]+u[5]*x[5]+u[6]*x[6]+u[7]*x[7]
                         +u[8]*x[8]+u[9]*x[9]+u[10]*x[10]+u[11]*x[11]) % 3] += v
                ghat = (cnt[0] - cnt[2], cnt[1] - cnt[2])          # cnt0 + cnt1 ω + cnt2 ω²
                gu = prod_off(u, (i, j)) if u[i] and u[j] else 0
                okp += ghat == (target * gu, 0); tot += 1
            G.append(sum(prod_off(x, (i, j)) for x in W if all(x)))
        mx = sum(1 for x in W if all(x))
        say(f"2 n = 12 {name} ({mx} maximal words): ĝ_ij(u) = −3^5·g_ij(u) pointwise on C, brute force in Z[ω]: {okp}/{tot} "
            f"(pairs {pairs}); G_ij(C) = {G}")


def check3(rng):
    n = 12; tried = 0; okP = 0; corr_nz = 0; G_nz = 0; with_max = 0
    while tried < 40:
        B = rref([[rng.randrange(3) for _ in range(n)] for _ in range(n // 2)], n)[0]
        if len(B) < n // 2 or all(dot(a, b) == 0 for a in B for b in B):
            continue
        tried += 1
        Bp = nullspace(B, n)
        WC, WP = span(B, n), span(Bp, n)
        i, j = rng.sample(range(n), 2)
        GP = sum(prod_off(x, (i, j)) for x in WP if all(x))
        GC = A0n = An0 = A00 = 0
        for u in WC:
            p = prod_off(u, (i, j))
            if not p:
                continue
            if u[i] and u[j]: GC += p
            elif u[i] and not u[j]: An0 += p
            elif u[j] and not u[i]: A0n += p
            else: A00 += p
        okP += 3 * GP == -(GC - 2 * (A0n + An0) + 4 * A00)
        corr_nz += (A0n, An0, A00) != (0, 0, 0)
        G_nz += GP != 0
        with_max += any(all(x) for x in WP)
    say(f"3 non-self-orthogonal 6-dim C ⊂ F₃¹² ({tried}): general Poisson 3G(C^⊥) = −[G(C) − 2(A₀ₙ+Aₙ₀) + 4A₀₀] exact on {okP}/{tried}; "
        f"correction terms nonzero on {corr_nz}; G(C^⊥) ≠ 0 on {G_nz} (C^⊥ has maximal words on {with_max})")


def four_point(W, n, K):
    Kset = set(K)
    G = sum(prod_off(x, Kset) for x in W if all(x))
    Wk = 0
    for u in W:
        zeros = [k for k in range(n) if not u[k]]
        if len(zeros) == 3 and set(zeros) <= Kset:
            Wk += prod_off(u, Kset)
    return G, Wk


def check4(rng):
    for name, B, n, sample in (("Golay", GOLAY, 12, None), ("code2", CODE2, 12, None)):
        W = span(B, n)
        Ks = list(itertools.combinations(range(n), 4))
        ok = 0; vals = Counter()
        for K in Ks:
            G, Wk = four_point(W, n, K)
            ok += G == -Wk; vals[G] += 1
        I = sum(f(x) for x in W)
        say(f"4 {name}: Σ_F s ε_aε_bε_cε_d = −W_K on {ok}/{len(Ks)} 4-sets; values {dict(sorted(vals.items()))}; Index = {I}")
    n = 24
    for t in range(2):
        B, _ = random_self_dual(n, rng)
        W = span(B, n)
        ok = 0; vals = Counter(); N = 25
        for _ in range(N):
            K = tuple(sorted(rng.sample(range(n), 4)))
            G, Wk = four_point(W, n, K)
            ok += G == -Wk; vals[G] += 1
        say(f"4 random n = 24 #{t}: Σ_F s ε_aε_bε_cε_d = −W_K on {ok}/{N} random 4-sets; values {dict(sorted(vals.items()))}; "
            f"Index = {sum(f(x) for x in W)}")


def check5(rng):
    n = 24; done = 0; tries = 0
    while done < 3 and tries < 20:
        tries += 1
        B, _ = random_self_dual(n, rng)
        W = span(B, n)
        F = [x for x in W if all(x)]
        eps = [[1 if a == 1 else -1 for a in x] for x in F]         # ε_k = −φ(x_k)
        s = [f(x) for x in F]
        I = sum(s)
        if I == 0:
            continue
        done += 1
        offmax = max(abs(sum(sv * e[i] * e[j] for sv, e in zip(s, eps))) for i, j in itertools.combinations(range(n), 2))
        trip = sum(sv for sv, e in zip(s, eps) if e[0] == e[1] == e[2])
        e0 = eps[0]; res = []
        for y in (0, 1, -1):
            x = list(e0); x[0] += 3 * y
            lhs = sum(sv * (sum(a * b for a, b in zip(e, x))) ** 2 for sv, e in zip(s, eps))
            x2 = sum(a * a for a in x)
            res.append((lhs == I * x2, lhs % 9 == 0, x2, (x2 % 3 == 0 and x2 % 9 != 0)))
        say(f"5 n = 24 code with Index {I} ({len(F)} maximal): max_i<j |Σ s ε_iε_j| = {offmax}; Σ_(ε0=ε1=ε2) s = {trip} "
            f"(Index/4 = {I // 4}, even: {trip % 2 == 0}); Step 3 (identity, 9|LHS, |x|², v₃=1) for y = 0, e₁, −e₁: {res}")


def check6():
    W = span(GOLAY, 12)
    F = [x for x in W if all(x)]
    reps = []
    for x in F:
        if tuple((-a) % 3 for a in x) not in reps:
            reps.append(x)
    H = [[1 if a == 1 else -1 for a in x] for x in reps]
    HHt = [[sum(a * b for a, b in zip(r, c)) for c in H] for r in H]
    ok = all(HHt[i][j] == (12 if i == j else 0) for i in range(12) for j in range(12))
    say(f"6 Golay: {len(F)} maximal words, {len(reps)} up to sign, all even: {all(f(x) == 1 for x in F)}; HHᵀ = 12I: {ok}")


def check7():
    for args in (["36", "4", "11"], ["48", "3", "11"], ["60", "2", "11"]):
        out = subprocess.run([BIN, "design", *args], capture_output=True, text=True).stdout.strip().splitlines()
        for line in out:
            say("7 rust design " + " ".join(args[:1]) + ": " + line)


if __name__ == "__main__":
    rng = random.Random(2026)
    check1(); check2(rng); check3(rng); check4(rng); check5(rng); check6(); check7()
    with open(os.path.join(HERE, "divisibility_check.log"), "w") as fh:
        fh.write("\n".join(OUT) + "\n")
