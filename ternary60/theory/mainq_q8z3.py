"""Q₈ × ℤ/3 and k ≡ 0 mod 24 (notes/main-question.md §8.1).

G = Q₈ × <h> on 36 coordinates: nine Q₈-orbits (s, t) of size 4 (s = 0..2, t ∈ ℤ/3), h: (s, t, a) ↦ (s, t+1, a)
(fixed-point-free, order 3, commuting with Q₈). A G-invariant code with Index ±24 and T_h = 0 at k ≡ 0 mod 24
would give index 1 (the anomaly vanishes there, §8), and a G-equivariant chain from k = 3 needs a G-stable
9-block system σ with R_σ = ±24 and R_σ̄(D) = 0 (k: 3 → 12 → 24 → …).

Part 1: random G-invariant self-dual codes: the joint distribution of (Index mod 144, T_h).
        Observed [C]: T_h = 0 or ±72 forces Index ≡ 0 mod 72; T_h = ±24 forces Index ≡ 0 or T_h mod 72.
Part 2: the 19 G-stable 9-block systems on random codes with Index ≡ 24 mod 48: min |R_σ| over systems
        with R_σ̄(D) = 0 (a chain from such σ has T_h = 0 and Index R_σ, so the rule predicts 72 | R_σ).
"""
import itertools, os, random, sys, time
from collections import Counter
from existence_common import rref, span
from existence_quadruple import R
from mainq_common import closure, fixed_code, rust_R, signed_count
from mainq_q8chain import q8, rand_group_code
from mainq_equivariant import choose_splits

N = 36
J4, K4 = q8(4)


def idx(s, t, a):
    return 4 * (3 * s + t) + a


def group():
    Jp = [0] * N; Js = [1] * N; Kp = [0] * N; Ks = [1] * N; hp = [0] * N; hs = [1] * N
    for s in range(3):
        for t in range(3):
            for a in range(4):
                i = idx(s, t, a)
                Jp[i] = idx(s, t, J4[0][a]); Js[i] = J4[1][a]
                Kp[i] = idx(s, t, K4[0][a]); Ks[i] = K4[1][a]
                hp[i] = idx(s, (t + 1) % 3, a)
    return (tuple(Jp), tuple(Js)), (tuple(Kp), tuple(Ks)), (tuple(hp), tuple(hs))


J, K, H = group()
HORB = sorted({tuple(sorted({idx(s, t, a) for t in range(3)})) for s in range(3) for a in range(4)})
ORB = {x: k for k, o in enumerate(HORB) for x in o}


def collapsed(C):
    Fx = fixed_code(C, N, H)
    return rref([[r[o[0]] for o in HORB] for r in Fx]) if Fx else []


def systems():
    G = closure([J, K, H], N)
    jp = sorted({tuple(sorted((a, J4[0][a]))) for a in range(4)})
    orbit_block = lambda s, t: tuple(idx(s, t, a) for a in range(4))
    out = [[orbit_block(s, t) for s in range(3) for t in range(3)]]
    for s0 in range(3):
        s1, s2 = [s for s in range(3) if s != s0]
        for c in range(3):
            for m in range(2):
                bl = [orbit_block(s0, t) for t in range(3)]
                for t in range(3):
                    for pi in range(2):
                        bl.append(tuple(idx(s1, t, a) for a in jp[pi]) + tuple(idx(s2, (t + c) % 3, a) for a in jp[pi ^ m]))
                out.append(bl)
    return [choose_splits(G, bl) for bl in out]


def part1(samples):
    rng = random.Random(5)
    cnt = Counter()
    for _ in range(samples):
        C = rand_group_code([J, K, H], N, rng)
        if C is None:
            continue
        I = rust_R(C, [], "z3I"); T = signed_count(collapsed(C), 12)
        cnt[(T, I % 144)] += 1
    by_T = {}
    for (T, r), v in cnt.items():
        by_T.setdefault(T, Counter())[r] += v
    for T in sorted(by_T):
        print(f"1 T_h = {T:4d}: Index mod 144 ∈ {dict(sorted(by_T[T].items()))}", flush=True)
    ok = all((T % 72 == 0 and r % 72 == 0) or (T % 72 != 0 and r % 72 in (0, T % 72))
             for (T, r) in cnt)
    print(f"1 {sum(cnt.values())} codes; rule 'T ≡ 0 mod 72 ⇒ 72 | Index; T = ±24 ⇒ Index ≡ 0 or T mod 72' "
          f"holds on all: {ok}", flush=True)


def part2(codes):
    S = systems()
    rng = random.Random(12)
    tried = 0; best = None; nR = 0; t0 = time.time()
    while tried < codes:
        C = rand_group_code([J, K, H], N, rng)
        if C is None or abs(rust_R(C, [], "z3I")) % 48 != 24:
            continue
        tried += 1
        DW = span(collapsed(C), 12)
        for sy in S:
            sbar = sorted({tuple(sorted({ORB[x] for x in b})) for b in sy})
            if R(DW, sbar, 12) != 0:
                continue
            r = rust_R(C, sy, "z3R"); nR += 1
            best = abs(r) if best is None else min(best, abs(r))
    print(f"2 {len(S)} G-stable 9-block systems; {tried} codes with Index ≡ 24 mod 48; {nR} systems with "
          f"R_σ̄(D) = 0; min |R_σ| among them = {best}  [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        part1(300)
        part2(40)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
