"""The "72-rule" of notes/main-question.md §8.1 for Q₈ × ℤ/3-invariant codes, via the Morita form
C = F₃² ⊗ U (mainq_morita.py; notes §9).

Setting: n = 12k, Q₈ = <J, K> with J² = K² = −1 (3k orbits = blocks), h a fixed-point-free order-3
permutation of the blocks commuting with Q₈. I = Index(C), T = T_h = Index of the collapsed fixed code.
The 72-rule said: T ≡ 0 mod 72 ⇒ I ≡ 0 mod 72 (and T = ±24 ⇒ I ≡ 0 or T mod 72).

Part 1: `sl2words` (normalised SL₂-words, ψ-configurations) against the direct enumeration `rsigma`,
        sign-exact, for the index and random systems of Q₈-orbit blocks, n = 12, 24, 36.
Part 2: exact law for free lifts at k = 1 and 2 (all of them): U = R·{e + uA₁f + u²(A₁+S)f} over a
        Lagrangian Ū (R = F₃[u]/u³, A₁ skew, S symmetric). k = 1: I = 24·S. k = 2: I/24 ≡ −A₁² mod 3
        if Ū = ℓ₁ ⊕ ℓ₂ is split (collapsed code = two tetracodes), I/24 ≡ 0 mod 3 otherwise.
Part 3: k = 3, sampled lifts over random Ū of each type: I/24 ≡ t·A₁(P)² mod 3 with t = T/24 and P ⊂ Ū
        the plane spanned by the lines m_s = Ū ∩ (zero on block s) (Golay type, T = ±24); I ≡ 0 mod 72
        when T = 0. Hence the 72-rule for free U at n = 36.
Part 4: random G-invariant codes: the rule at k = 3 (holds) and k = 6 (FAILS: T = 0 with I ≢ 0 mod 72);
        a counterexample is saved to ../codes/q8z3_len72_T0.txt (U in q8z3_len72_T0.U.txt), with |I|
        re-checked by `ternary60 index`. Also: β ≥ 1 (U not free over R) ⇒ T ≡ 0 mod 72 [P], and
        I ≡ 0 mod 72 in every sample [C].
"""
import itertools, os, random, sys
from collections import Counter
from existence_common import rref, rust_index, HERE
from mainq_common import rust_R, write_code
from mainq_morita import (rand_U, code_from_U, fixed_U, collapse, h_blocks, lagrangians, complement,
                          lift, skews, syms, rsys, omega)


def T_of(U, k):
    """T_h = Σ over the collapsed fixed code F₃² ⊗ π(U^h) (length 4k), sign-exact."""
    D = collapse(fixed_U(U, h_blocks(k)), k)
    return rust_R(code_from_U(D, k), [], "72T") if D else 0


def part1(rng):
    bad = 0; tot = 0
    for k in (1, 2, 3):
        for _ in range(6):
            U = None
            while U is None:
                U = rand_U(k, rng)
            r = 3 * k
            sig = sorted(rng.sample(range(r), rng.randrange(1, r + 1)))
            a = rsys(U, [[], sig], "72p1")
            C = code_from_U(U, r)
            b = [rust_R(C, [], "72p1I"), rust_R(C, [list(range(4 * x, 4 * x + 4)) for x in sig], "72p1R")]
            tot += 1; bad += a != b
    print(f"1 sl2words vs rsigma (index and a random orbit-block R_σ), n = 12, 24, 36: {tot - bad}/{tot} "
          f"agree sign-exactly", flush=True)


def part2():
    # k = 1: every free lift
    res = Counter()
    for L in lagrangians(1):
        F = complement(L, 1)
        for S in syms(1):
            I = rsys(lift(L, F, [[0]], S, 1), [[]], "72p2")[0]
            res[(S[0][0], I)] += 1
    print(f"2 k = 1 (all 4·3 free lifts): (S, Index) counts {dict(sorted(res.items()))}", flush=True)
    # k = 2: every free lift over every Lagrangian of F_3^4
    split_ok = other_ok = 0; nsplit = nother = 0
    for L in lagrangians(2):
        F = complement(L, 2)
        split = any(all(v[i] == 0 for i in (2, 3)) for v in (L[0], L[1], [(x + y) % 3 for x, y in zip(*L)],
                                                            [(x - y) % 3 for x, y in zip(*L)]))
        for A1 in skews(2):
            for S in syms(2):
                a = (rsys(lift(L, F, A1, S, 2), [[]], "72p2")[0] // 24) % 3
                if split:
                    nsplit += 1; split_ok += a == (-A1[0][1] ** 2) % 3
                else:
                    nother += 1; other_ok += a == 0
    print(f"2 k = 2 (all 40 Lagrangians × 81 free lifts): split Ū: I/24 ≡ −A₁² mod 3 on {split_ok}/{nsplit}; "
          f"non-split Ū: I ≡ 0 mod 72 on {other_ok}/{nother}", flush=True)


def kernel_plane(L, k):
    """Coefficient vectors (in the basis L) of m_s = Ū ∩ (zero on block s), and their span."""
    ms = []
    for s in range(k):
        for c in itertools.product(range(3), repeat=k):
            v = [sum(ci * u[i] for ci, u in zip(c, L)) % 3 for i in range(2 * k)]
            if any(v) and v[2 * s] == 0 and v[2 * s + 1] == 0:
                ms.append(list(c)); break
    return ms


def part3(rng, n_ubar=4, n_lift=40):
    k = 3
    stats = Counter()
    seen_types = Counter()
    while sum(seen_types.values()) < n_ubar * 3:
        B = []
        while len(B) < k:
            v = [rng.randrange(3) for _ in range(2 * k)]
            if any(v) and all(omega(v, b) == 0 for b in B) and len(rref(B + [v])) > len(B):
                B.append(v)
        L = rref(B)
        F = complement(L, k)
        T = T_of(lift(L, F, [[0] * k] * k, [[0] * k] * k, k), k)
        ms = kernel_plane(L, k)
        typ = ("T=%d" % T, "kernel lines %d" % len(ms))
        key = "golay" if T else "T0"
        if seen_types[key] >= (n_ubar * 2 if key == "golay" else n_ubar):
            continue
        seen_types[key] += 1
        P = rref(ms) if len(ms) == 3 else None
        if T:
            # gauge check: B_s = ω_s|_Ū annihilates P, and span(B_s) is 2-dimensional
            Bs = [[[(L[i][2 * s] * L[j][2 * s + 1] - L[i][2 * s + 1] * L[j][2 * s]) % 3 for j in range(k)]
                   for i in range(k)] for s in range(k)]
            gauge_ok = (len(P) == 2 and all(sum(P[0][i] * Bm[i][j] * P[1][j] for i in range(k) for j in range(k)) % 3 == 0
                                          for Bm in Bs) and len(rref([[Bm[0][1], Bm[0][2], Bm[1][2]] for Bm in Bs])) == 2)
            stats[("gauge", gauge_ok)] += 1
        for _ in range(n_lift):
            A1 = [[0] * k for _ in range(k)]; S = [[0] * k for _ in range(k)]
            for i in range(k):
                S[i][i] = rng.randrange(3)
                for j in range(i + 1, k):
                    A1[i][j] = rng.randrange(3); A1[j][i] = (-A1[i][j]) % 3
                    S[i][j] = S[j][i] = rng.randrange(3)
            U = lift(L, F, A1, S, k)
            a = (rsys(U, [[]], "72p3")[0] // 24) % 3
            if T:
                assert P is not None and len(P) == 2
                lam = sum(P[0][i] * A1[i][j] * P[1][j] for i in range(k) for j in range(k)) % 3
                ok = a == ((T // 24) * lam * lam) % 3
            else:
                ok = a == 0
            stats[(typ, ok)] += 1
    for (typ, ok), c in sorted(stats.items(), key=str):
        if typ == "gauge":
            print(f"3 k = 3, Golay-type Ū: B_s(P) = 0 for s = 0, 1, 2 and dim span(B_s) = 2: {ok} on {c} Ū", flush=True)
        else:
            print(f"3 k = 3, Ū with {typ[0]}, {typ[1]}: law {'holds' if ok else 'FAILS'} on {c} lifts", flush=True)


def part4(rng, n3=150, n6=30):
    for k, N in ((3, n3), (6, n6)):
        cnt = Counter(); viol = []
        done = 0
        while done < N:
            U = rand_U(k, rng)
            if U is None:
                continue
            done += 1
            beta = len(fixed_U(U, h_blocks(k))) - k
            I = rsys(U, [[]], "72p4")[0]
            T = T_of(U, k)
            rule = (T % 72 != 0) or (I % 72 == 0)
            cnt[(beta, T % 72, I % 72)] += 1
            if not rule:
                viol.append((U, I, T))
        print(f"4 k = {k}: {N} random codes; (β, T mod 72, I mod 72) counts {dict(sorted(cnt.items()))}", flush=True)
        print(f"4   violations of 'T ≡ 0 mod 72 ⇒ I ≡ 0 mod 72': {len(viol)}; β ≥ 1 always has T ≡ I ≡ 0 mod 72: "
              f"{all(t == 0 and i == 0 for (b, t, i) in cnt if b >= 1)}", flush=True)
        if k == 6:
            ex = next((v for v in viol if v[2] == 0), None)
            if ex:
                U, I, T = ex
                C = code_from_U(U, 3 * k)
                base = os.path.join(HERE, "..", "codes", "q8z3_len72_T0")
                write_code(base + ".txt", C); write_code(base + ".U.txt", U)
                print(f"4   saved {os.path.basename(base)}.txt: T_h = {T}, Index = {I} (sl2words, sign-exact), "
                      f"|Index| = {abs(rust_index(C, '72ex'))} (ternary60 index); Index mod 72 = {I % 72}",
                      flush=True)


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    rng = random.Random(72)
    with contextlib.redirect_stdout(Tee()):
        part1(rng)
        part2()
        part3(rng)
        part4(rng)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
