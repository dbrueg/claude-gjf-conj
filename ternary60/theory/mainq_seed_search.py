"""Seeds for the Z/12-equivariant chains (notes/main-question.md §4.4).

g on 36 coordinates: six signed 6-cycles e_{6j+i} ↦ e_{6j+i+1} (i < 5), e_{6j+5} ↦ −e_{6j}; ord g = 12,
g⁶ = −1, J = g³ (J² = −1), h = g⁴ (order 3, cycle shape 3¹²).

Part 1 (GJF's method): random g-invariant self-dual codes (grown from g-orbits of random vectors);
        tally (Index, T_h) and keep Index = ±24, T_h = 0. Seeds found are written to
        ../codes/z12seed_len36_<i>.txt only with --write (the committed seeds came from seed 1, 300 samples).
Part 2: on the committed seeds 3 and 4, all g-stable block systems made of J-stable blocks (two J-pairs
        from different 6-cycles, h-orbits of 3 blocks): b = 3 (45 systems) and b = 6 (405). Report the
        systems with R_σ(E) = ±24 and R_σ̄(D) = 0 (D = collapsed h-fixed code, σ̄ = collapsed blocks).
"""
import itertools, os, random, sys
from collections import Counter
from existence_common import HERE, rref, span
from existence_quadruple import R
from mainq_common import (mono_pow, mono_neg, mono_order, is_aut, read_code, write_code, fixed_code,
                          rust_R, twined_count_rust)
from mainq_obstruction import rand_invariant_code, signed_cycles

N = 36
G = signed_cycles(N, 6)
J = mono_pow(G, 3)
H = mono_pow(G, 4)


def h_orbits():
    orbits, seen = [], set()
    for i in range(N):
        if i not in seen:
            o = [i, H[0][i], H[0][H[0][i]]]
            seen.update(o); orbits.append(o)
    return orbits, {x: k for k, o in enumerate(orbits) for x in o}


def systems():
    Jpairs = sorted({tuple(sorted((i, J[0][i]))) for i in range(N)})
    S3, keys = [], set()
    for P, Q in itertools.combinations(Jpairs, 2):
        if P[0] // 6 == Q[0] // 6:
            continue
        bl = [P + Q]
        for _ in range(2):
            bl.append(tuple(H[0][x] for x in bl[-1]))
        key = frozenset(frozenset(b) for b in bl)
        if key not in keys:
            keys.add(key); S3.append(bl)
    S6 = [a + b for a, b in itertools.combinations(S3, 2)
          if not ({x for bb in a for x in bb} & {x for bb in b for x in bb})]
    return S3, S6


def part1(samples, write):
    rng = random.Random(1)
    cnt = Counter(); good = 0
    for _ in range(samples):
        C = rand_invariant_code(G, N, rng, 12)
        if C is None:
            continue
        I = rust_R(C, [], "seedI"); T = twined_count_rust(C, N, H)
        cnt[(I, T)] += 1
        if abs(I) == 24 and T == 0:
            good += 1
            if write:
                write_code(os.path.join(HERE, "..", "codes", f"z12seed_len36_{good}.txt"), C)
    top = sorted(cnt.items(), key=lambda kv: -kv[1])[:12]
    print(f"1 {samples} random g-invariant codes: {good} with Index = ±24 and T_h = 0; most common (Index, T_h): {top}",
          flush=True)


def part2(seeds):
    orbits, orb = h_orbits()
    S3, S6 = systems()
    for sd in seeds:
        E = read_code(os.path.join(HERE, "..", "codes", f"z12seed_len36_{sd}.txt"))
        assert is_aut(G, E, N)
        Fx = fixed_code(E, N, H)
        D = rref([[r[o[0]] for o in orbits] for r in Fx]); DW = span(D, len(orbits))
        for name, S in (("b = 3", S3), ("b = 6", S6)):
            hits = []
            for bl in S:
                sbar = [tuple(sorted(orb[x] for x in bl[j])) for j in range(0, len(bl), 3)]
                if R(DW, sbar, len(orbits)) != 0:
                    continue
                r = rust_R(E, bl, "seedR")
                if abs(r) == 24:
                    hits.append((r, bl))
            print(f"2 seed {sd}: Index {rust_R(E, [], 'seedI')}, T_h {twined_count_rust(E, N, H)}; {name}: "
                  f"{len(hits)} of {len(S)} systems with R_σ = ±24 and R_σ̄(D) = 0; first: {hits[:1]}", flush=True)


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        print(f"0 g: ord {mono_order(G)}, g⁶ = −1 {mono_pow(G, 6) == mono_neg(N)}", flush=True)
        part1(int(os.environ.get("SEED_SAMPLES", "300")), "--write" in sys.argv)
        part2([3, 4])
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
