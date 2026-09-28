"""Review: GJF's own k = 3 code (GJF Ex 5.7) as a Z/6-seed for the chains of notes/main-question.md §4.

Question: can the searched length-36 Z/12 seed (`z12seed_len36_3`, Thm 4.4) be replaced by GJF's published
k = 3 example E = ../codes/gjf_ex57_len36.txt with its shift h: e_i ↦ e_{i+12 mod 36} and the group
<g> = <−h> = <−1> × <h> ≅ Z/6 (g = −h: order 6, g³ = −1, g⁴ = h)?
- The h-orbits of coordinates are {j, j+12, j+24}, j < 12. An h-stable block system is a union of block
  orbits {β, hβ, h²β} with β meeting each coordinate orbit at most once (else β ∩ hβ ≠ ∅); such a triple
  covers 4 coordinate orbits. So there are C(12,4)·3⁴/3 = 13365 three-block systems and
  C(12,4)·C(8,4)/2·27² = 12,629,925 six-block systems.
- h is fixed-point-free of order 3 on every stage, so it stabilises no 4-set: every block stabiliser in <g>
  is {±1}, any split and tetracode placement can be transported (Lemma 4.1), and the chain is equivariant.
- Lemma 4.3: T_h(Q_σ E) = R_σ̄(D) (D = collapsed h-fixed code, σ̄ = one collapsed block per block orbit), and
  Index(Q_σ E) = R_σ(E) ([I] Lemma 5.8). A system is *good* if R_σ(E) = ±24 and R_σ̄(D) = 0.
- <g> ≅ Z/6 has no element of order 12, and Aut(E) = <−1, h> (mainq_automorphisms.log). So this chain can
  serve gcd(k,24) ∈ {3, 6} only (m = 3: h; m = 6: g, with g³ = −1 and g² = h² of shape 3^{n/3}); m = 12
  (k ≡ 12 mod 24) still needs an order-12 g with g⁶ = −1, e.g. chain A of `mainq_z12chain.py`.

Part 1: the seed: self-dual; h ∈ Aut (plain permutation, no signs), order 3, shape 3¹²; Index(E) sign-exact
        (Rust `rsigma`, full enumeration, and `rsigma_is`, information sets); T_h(E); collapsed fixed code D
        against ../codes/gjf_ex57_len36_fixed12.txt (GJF's printed fixed code).
Part 2: all 13365 three-block systems: R_σ̄(D) on the 495 orbit 4-sets, R_σ(E) (`rsigma_is`) on all systems;
        distribution on the admissible ones (R_σ̄(D) = 0) and the good ones.
Part 3: six-block systems: R_σ̄(D) on all 17325 orbit pairs; R_σ(E) on a uniform random sample of admissible
        systems ($SAMPLES6, default 2000; random.Random(6)), with a 95% Wilson interval for the rate of ±24.
Part 4: the chains, built with `mainq_equivariant.quad_eq` (gens [g], refine = the block orbit of step-1
        block 0): n = 72 (k = 6) from the first good 3-block system with R_σ = +24, n = 108 (k = 9) from the
        first sampled good 6-block system with R_σ = +24 (else −24). Self-duality; g ∈ Aut, ord g = 6, g³ = −1;
        h = g⁴ a fixed-point-free permutation of order 3; block stabilisers; T_h by enumerating the
        collapsed fixed code (Python at n = 72, Rust at n = 108); Index at n = 72 by Rust `index` (|I|) and
        `rsigma_is` (sign-exact); at n = 108 Index = R_σ(E) by Lemma 5.8. Control: on a non-admissible
        system, T_h(Q_σ E) = R_σ̄(D) ≠ 0 at n = 72 (sign-exact).
        Codes: ../codes/gjf36_z6chain_len{72,108}.txt, g and h in gjf36_z6chain_len{72,108}.gens.txt.
Part 5: one more step of each chain (n = 144 from 72, n = 180 from 108; codes not saved): self-duality,
        invariance, T_h = 0 (`rsigma_is` on the collapsed fixed code). Skip with --no-part5. Then a summary.

Rust runs with at most $THREADS (default 2) threads: `rsigma_is` gets the count as an argument, `ternary60`
(which uses every core it may run on) is pinned with `taskset`. Runtime ≈ 14 min with 2 threads on a shared
4-core machine (Part 3 ≈ 9 min, the n = 72 index checks ≈ 4 min).
"""
import itertools, os, random, re, shutil, subprocess, sys, time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from math import gcd
from existence_common import HERE, BIN, _TMPDIR, rref, span
from existence_quadruple import R
from mainq_common import (read_code, write_code, write_gens, mono_mul, mono_pow, mono_neg, mono_id, mono_order,
                          mono_apply, cycle_type, is_aut, closure, fixed_code, signed_count, to_bits, badd, bneg)
from mainq_equivariant import quad_eq, choose_splits, block_image

CODES = os.path.join(HERE, "..", "codes")
SEED = os.path.join(CODES, "gjf_ex57_len36.txt")
FIXED12 = os.path.join(CODES, "gjf_ex57_len36_fixed12.txt")
RSIS = os.path.join(HERE, "..", "target", "release", "rsigma_is")
THREADS = int(os.environ.get("THREADS", "2"))
SAMPLES6 = int(os.environ.get("SAMPLES6", "2000"))
N0 = 36


# ------------------------------------------------------------------ Rust wrappers


def _cpus():
    try:
        cpus = sorted(os.sched_getaffinity(0))
    except AttributeError:
        return None
    return ",".join(map(str, cpus[:THREADS]))


def _pinned(cmd):
    """Pin `ternary60` (which runs one thread per available core) to THREADS cores, if taskset exists."""
    cpus = _cpus()
    if cpus and shutil.which("taskset"):
        return ["taskset", "-c", cpus] + cmd
    return cmd


def spec_of(blocks):
    return ";".join(",".join(map(str, b)) for b in blocks) if blocks else "-"


def code_file(rows, tag):
    fn = os.path.join(_TMPDIR, tag + ".txt")
    write_code(fn, rows)
    return fn


def rs_is(path, blocks, threads=1, info=False):
    """R_σ by `rsigma_is` (information sets, sign-exact); with info=True also its 'patterns' line."""
    out = subprocess.run([RSIS, path, spec_of(blocks), str(threads)], capture_output=True, text=True,
                         check=True).stdout
    kv = dict(ln.split(" ", 1) for ln in out.strip().split("\n"))
    r = int(kv["R"])
    return (r, kv["patterns"], kv["seconds"]) if info else r


def rs_full(path, blocks):
    """R_σ by `ternary60 rsigma` (full enumeration, meet in the middle; sign-exact)."""
    out = subprocess.run(_pinned([BIN, "rsigma", path, spec_of(blocks)]), capture_output=True, text=True,
                         check=True).stdout
    return int(out.split("=")[1])


def rust_abs_index(path):
    """|Index| by `ternary60 index` (its sign is not meaningful)."""
    out = subprocess.run(_pinned([BIN, "index", path]), capture_output=True, text=True, check=True).stdout
    return abs(int(re.search(r" I=(-?\d+)", out).group(1)))


def batch_rs_is(path, systems):
    """R_σ(E) for many block systems: THREADS single-threaded `rsigma_is` processes at a time."""
    with ThreadPoolExecutor(THREADS) as ex:
        return list(ex.map(lambda bl: rs_is(path, bl, 1), systems))


# ------------------------------------------------------------------ fast linear algebra on bit-sliced rows


def bdot(x, y):
    return (bin(x[0] & y[0]).count("1") + bin(x[1] & y[1]).count("1")
            - bin(x[0] & y[1]).count("1") - bin(x[1] & y[0]).count("1")) % 3


def selfdual(rows, n):
    B = rref(rows)
    bits = [to_bits(r) for r in B]
    return len(B) == n // 2 and all(bdot(x, y) == 0 for i, x in enumerate(bits) for y in bits[i:])


def is_aut_fast(g, rows, n):
    """g(C) ⊂ C: reduce each image of a basis row against the RREF basis (pivot coefficients)."""
    B = rref(rows)
    piv = [next(j for j in range(n) if r[j]) for r in B]
    bits = [to_bits(r) for r in B]
    for r in B:
        v = to_bits(mono_apply(g, r))
        w = v
        for p, b in zip(piv, bits):
            c = 1 if (v[0] >> p) & 1 else 2 if (v[1] >> p) & 1 else 0
            if c == 1:
                w = badd(w, bneg(b))
            elif c == 2:
                w = badd(w, b)
        if w[0] | w[1]:
            return False
    return True


def signed_count_py(rows, N):
    """Σ_{x ∈ span(rows)} f(x), bit-sliced meet in the middle (dimension ≤ ~14)."""
    B = [to_bits(r) for r in rows]
    half = len(B) // 2

    def sp(rs):
        out = [(0, 0)]
        for r in rs:
            nr = bneg(r)
            out = [y for x in out for y in (x, badd(x, r), badd(x, nr))]
        return out
    A, C = sp(B[:half]), sp(B[half:])
    full = (1 << N) - 1
    tot = 0
    for x in A:
        for y in C:
            z = badd(x, y)
            if (z[0] | z[1]) == full:
                tot += -1 if bin(z[0]).count("1") & 1 else 1
    return tot


# ------------------------------------------------------------------ h, orbits, collapse


def shift_h(n=N0):
    return (tuple((i + 12) % n for i in range(n)), (1,) * n)


def h_orbits(h, n):
    orbits, seen = [], set()
    for i in range(n):
        if i not in seen:
            o = [i, h[0][i], h[0][h[0][i]]]
            seen.update(o); orbits.append(o)
    return orbits


def collapsed_fixed(rows, n, h):
    """The h-fixed subcode, one coordinate per h-orbit (h a plain permutation). Returns (rref rows, N)."""
    assert set(h[1]) == {1}, "h must be a plain permutation"
    orbits = h_orbits(h, n)
    Fx = fixed_code(rows, n, h)
    return (rref([[r[o[0]] for o in orbits] for r in Fx]) if Fx else []), len(orbits)


def orbit_blocks(S, a):
    """The block orbit {β, hβ, h²β} on 36 coordinates, β = (S0, S1 + 12a0, S2 + 12a1, S3 + 12a2)."""
    beta = (S[0],) + tuple(S[i + 1] + 12 * a[i] for i in range(3))
    return [tuple((x + 12 * t) % N0 for x in beta) for t in range(3)]


def stab_is_pm1(G, blocks, n):
    """Every block's stabiliser in G is exactly {1, −1}."""
    pm = {mono_id(n), mono_neg(n)}
    return all({g for g in G if frozenset(block_image(g, b)[0]) == frozenset(b)} == pm for b in blocks)


def hist(c):
    return "{" + ", ".join(f"{k}: {v}" for k, v in sorted(c.items())) + "}"


# ------------------------------------------------------------------ parts


def part1():
    print("== Part 1: the seed E = gjf_ex57_len36 (GJF Ex 5.7, k = 3)", flush=True)
    E = read_code(SEED); n = N0
    h = shift_h(); g = mono_mul(mono_neg(n), h)
    print(f"1 E: {len(E)} rows, self-dual {selfdual(E, n)}", flush=True)
    print(f"1 h = shift by 12 (plain permutation, all signs +1): h ∈ Aut(E) {is_aut(h, E, n)}, ord h = {mono_order(h)}, "
          f"cycle shape {cycle_type(h[0])}, fixed coordinates {sum(1 for i in range(n) if h[0][i] == i)}", flush=True)
    print(f"1 g = −h: g ∈ Aut(E) {is_aut(g, E, n)}, ord g = {mono_order(g)}, g³ = −1 {mono_pow(g, 3) == mono_neg(n)}, "
          f"g⁴ = h {mono_pow(g, 4) == h}, g² = h² {mono_pow(g, 2) == mono_pow(h, 2)}", flush=True)
    i_full, i_is = rs_full(SEED, []), rs_is(SEED, [], THREADS)
    print(f"1 Index(E) = {i_full} (ternary60 rsigma, full enumeration of 3^18 words) = {i_is} (rsigma_is, 2^18 "
          f"information-set patterns): sign-exact", flush=True)
    Fx = fixed_code(E, n, h)
    T = signed_count(Fx, n)
    D, N = collapsed_fixed(E, n, h)
    Dg = rref(read_code(FIXED12))
    DW = span(D, N)
    ev = sum(1 for x in DW if 0 not in x and x.count(1) % 2 == 0)
    od = sum(1 for x in DW if 0 not in x and x.count(1) % 2 == 1)
    print(f"1 h-fixed subcode: dim {len(Fx)}; T_h(E) = {T} (3^{len(Fx)} fixed words enumerated)", flush=True)
    print(f"1 collapsed fixed code D (coordinate j = orbit {{j, j+12, j+24}}): length {N}, dim {len(D)}, self-dual "
          f"{selfdual(D, N)}; equals GJF's printed fixed code (gjf_ex57_len36_fixed12.txt, same RREF) {D == Dg}; "
          f"maximal words: {ev} even, {od} odd, Index(D) = {signed_count(D, N)}", flush=True)
    return E, h, g, D, N


def part2(E, D, N):
    print("\n== Part 2: all h-stable 3-block systems {β, hβ, h²β}", flush=True)
    # enumeration check: every β (495 orbit sets × 3⁴ point choices) gives a system; each system arises 3 times
    allsys = set()
    for S in itertools.combinations(range(12), 4):
        for a4 in itertools.product(range(3), repeat=4):
            beta = [x + 12 * t for x, t in zip(S, a4)]
            allsys.add(frozenset(frozenset((x + 12 * t) % N0 for x in beta) for t in range(3)))
    systems = [(S, a) for S in itertools.combinations(range(12), 4) for a in itertools.product(range(3), repeat=3)]
    normal = {frozenset(frozenset(b) for b in orbit_blocks(S, a)) for S, a in systems}
    disjoint = all(len({x for b in orbit_blocks(S, a) for x in b}) == 12 for S, a in systems)
    print(f"2 {len(allsys)} distinct systems from all 495·81 blocks β; normal forms (a₀ = 0): {len(systems)}, "
          f"distinct {len(normal)}, the same set {normal == allsys}; blocks disjoint {disjoint}", flush=True)
    DW = span(D, N)
    Rbar = {S: R(DW, [S], N) for S in itertools.combinations(range(12), 4)}
    print(f"2 R_σ̄(D) on the 495 orbit 4-sets: {hist(Counter(Rbar.values()))}", flush=True)
    t0 = time.time()
    vals = batch_rs_is(SEED, [orbit_blocks(S, a) for S, a in systems])
    print(f"2 R_σ(E) on all {len(systems)} systems ({time.time() - t0:.0f}s, rsigma_is): all ≡ 24 mod 48 "
          f"{all(v % 48 == 24 for v in vals)}; min {min(vals)}, max {max(vals)}", flush=True)
    by_bar = Counter(Rbar[S] for (S, a), v in zip(systems, vals) if abs(v) == 24)
    print(f"2 systems with R_σ(E) = ±24, by R_σ̄(D): {hist(by_bar)}", flush=True)
    adm = [((S, a), v) for (S, a), v in zip(systems, vals) if Rbar[S] == 0]
    c = Counter(v for _, v in adm)
    good = [(s, v) for s, v in adm if abs(v) == 24]
    print(f"2 admissible (R_σ̄(D) = 0): {len(adm)} systems = {sum(1 for S in Rbar if Rbar[S] == 0)} orbit sets × 27", flush=True)
    print(f"2 R_σ(E) on the admissible systems: {len(c)} values, min {min(c)}, max {max(c)}; histogram {hist(c)}",
          flush=True)
    print(f"2 good (R_σ = ±24, R_σ̄(D) = 0): {len(good)} of {len(adm)} ({100 * len(good) / len(adm):.1f}%): "
          f"R_σ = −24: {c[-24]}, R_σ = +24: {c[24]}; orbit 4-sets with a good system: "
          f"{len({s[0] for s, _ in good})} of {sum(1 for S in Rbar if Rbar[S] == 0)}", flush=True)
    sA = next(s for s, v in good if v == 24)
    sM = next(s for s, v in good if v == -24)
    rng = random.Random(2)
    extra = rng.sample(range(len(systems)), 3)
    checks = [(sA, 24), (sM, -24)] + [(systems[j], vals[j]) for j in extra]
    ok = all(rs_full(SEED, orbit_blocks(*s)) == v for s, v in checks)
    print(f"2 cross-check with ternary60 rsigma (full enumeration) on {len(checks)} systems (first +24, first −24, "
          f"3 random): agree {ok}", flush=True)
    ctrl = next((S, a) for S, a in systems if Rbar[S] != 0)
    print(f"2 chosen for chain A: orbit set {sA[0]}, a = {sA[1]}: σ_A = {orbit_blocks(*sA)}, R_σ(E) = +24, R_σ̄(D) = 0",
          flush=True)
    return orbit_blocks(*sA), (orbit_blocks(*ctrl), Rbar[ctrl[0]], ctrl)


def wilson(k, n, z=1.96):
    """95% Wilson score interval for a binomial rate k/n."""
    if n == 0:
        return 0.0, 1.0
    p = k / n
    c = (p + z * z / (2 * n)) / (1 + z * z / n)
    w = z * ((p * (1 - p) / n + z * z / (4 * n * n)) ** 0.5) / (1 + z * z / n)
    return max(0.0, c - w), min(1.0, c + w)


def part3(E, D, N):
    print("\n== Part 3: h-stable 6-block systems (two block orbits on disjoint orbit 4-sets)", flush=True)
    DW = span(D, N)
    pairs = []
    for S1 in itertools.combinations(range(12), 4):
        rest = [x for x in range(12) if x not in S1]
        for S2 in itertools.combinations(rest, 4):
            if S1 < S2:
                pairs.append((S1, S2))
    t0 = time.time()
    Rbar2 = {p: R(DW, list(p), N) for p in pairs}
    adm_pairs = [p for p in pairs if Rbar2[p] == 0]
    print(f"3 {len(pairs)} orbit pairs × 729 point choices = {len(pairs) * 729} systems; R_σ̄(D) on the pairs "
          f"({time.time() - t0:.0f}s): {hist(Counter(Rbar2.values()))}; admissible: {len(adm_pairs)} pairs "
          f"= {len(adm_pairs) * 729} systems ({100 * len(adm_pairs) / len(pairs):.1f}%)", flush=True)
    rng = random.Random(6)
    sample, seen = [], set()
    while len(sample) < SAMPLES6:
        p = rng.choice(adm_pairs)
        a1 = tuple(rng.randrange(3) for _ in range(3)); a2 = tuple(rng.randrange(3) for _ in range(3))
        if (p, a1, a2) in seen:
            continue
        seen.add((p, a1, a2)); sample.append((p, a1, a2))
    t0 = time.time()
    vals = batch_rs_is(SEED, [orbit_blocks(p[0], a1) + orbit_blocks(p[1], a2) for p, a1, a2 in sample])
    c = Counter(vals)
    good = [(s, v) for s, v in zip(sample, vals) if abs(v) == 24]
    print(f"3 uniform sample of {len(sample)} admissible systems (random.Random(6)); R_σ(E) by rsigma_is "
          f"({time.time() - t0:.0f}s): all ≡ 24 mod 48 {all(v % 48 == 24 for v in vals)}; {len(c)} values, "
          f"min {min(vals)}, max {max(vals)}; |R| ≤ 120: {hist(Counter(v for v in vals if abs(v) <= 120))}", flush=True)
    q = sorted(abs(v) for v in vals)
    lo, hi = wilson(len(good), len(sample))
    print(f"3 |R_σ(E)| quartiles {q[len(q) // 4]}, {q[len(q) // 2]}, {q[3 * len(q) // 4]}", flush=True)
    print(f"3 good (R_σ = ±24): {len(good)} of {len(sample)} = {100 * len(good) / len(sample):.2f}% (95% Wilson "
          f"interval {100 * lo:.2f}–{100 * hi:.2f}%): −24: {c[-24]}, +24: {c[24]}", flush=True)
    for (p, a1, a2), v in good:
        print(f"3   R_σ = {v:+d}: orbit sets {p[0]}, {p[1]}; a = {a1}, {a2}", flush=True)
    pick = next(((s, v) for s, v in good if v == 24), None) or next(iter(good), None)
    if pick is None:
        print("3 no good system in the sample: chain B not built", flush=True)
        return None
    (p, a1, a2), v = pick
    sB = orbit_blocks(p[0], a1) + orbit_blocks(p[1], a2)
    print(f"3 chosen for chain B (first R_σ = {v:+d} in the sample): σ_B = {sB}; ternary60 rsigma (full enumeration) "
          f"R_σ(E) = {rs_full(SEED, sB)}, R_σ̄(D) = {Rbar2[p]}", flush=True)
    return sB, v


def build(E, m, blocks0, gens, label, pre, resplit=True):
    """One <g>-equivariant partial quadrupling step; returns (rows, n, next blocks, extended gens). The seed
    systems get G-equivariant splits from choose_splits (as in mainq_z12chain); later stages use the σ″
    returned by quad_eq as it is."""
    G = closure(gens, m)
    blocks = choose_splits(G, blocks0) if resplit else blocks0
    st = stab_is_pm1(G, blocks, m)
    rows, n, newb, gens2 = quad_eq(E, m, blocks, gens, refine="orbit0")
    G2 = closure(gens2, n)
    print(f"{pre} {label}: length {m} → {n} (k = {n // 12}); σ = {blocks}; block stabilisers in <g> = {{±1}}: "
          f"σ {st}, next σ″ {stab_is_pm1(G2, newb, n)} (b = {len(newb)}): σ″ = {newb}", flush=True)
    return rows, n, newb, gens2


def check_code(rows, n, gq, label, pre, enum_py):
    hq = mono_pow(gq, 4)
    ok = (selfdual(rows, n), is_aut_fast(gq, rows, n), mono_order(gq) == 6, mono_pow(gq, 3) == mono_neg(n),
          set(hq[1]) == {1} and cycle_type(hq[0]) == (3,) * (n // 3), is_aut_fast(hq, rows, n),
          is_aut_fast(mono_neg(n), rows, n))
    print(f"{pre} {label} n = {n}: self-dual {ok[0]}; g ∈ Aut {ok[1]}, ord g = 6 {ok[2]}, g³ = −1 {ok[3]}; h = g⁴ a "
          f"permutation of shape 3^{n // 3} (no fixed coordinate) {ok[4]}, h ∈ Aut {ok[5]}; −1 ∈ Aut {ok[6]}",
          flush=True)
    Dq, Nq = collapsed_fixed(rows, n, hq)
    if enum_py:
        T = signed_count_py(Dq, Nq)
        how = f"Python enumeration of 3^{len(Dq)} words"
    else:
        fn = code_file(Dq, f"fix{n}")
        T, pat, sec = rs_is(fn, [], THREADS, info=True)
        how = f"rsigma_is, {pat} patterns, {sec}s"
        if len(Dq) <= 18:
            how += f"; = {rs_full(fn, [])} by ternary60 rsigma, full enumeration of 3^{len(Dq)} words"
    print(f"{pre} {label} n = {n}: collapsed h-fixed code: length {Nq}, dim {len(Dq)}, self-dual "
          f"{selfdual(Dq, Nq)}; T_h = {T} ({how})", flush=True)
    return all(ok), T


def gjf_line(n, T, pre):
    k = n // 12; m = gcd(k, 24)
    if m == 3:
        s = f"m = 3: h (order 3, shape 3^{n // 3}, T_h = {T})"
    elif m == 6:
        s = f"m = 6: g (order 6, g³ = −1, g² = h² of shape 3^{n // 3}, T_(h²) = T_h = {T})"
    else:
        s = f"m = {m}: NOT served by <g> ≅ Z/6 (needs an element of order {m})"
    return f"{pre}   GJF Thm 5.6 at k = {k}: " + s


def part4(E, g, D, N, sA, ctrl, sBv):
    print("\n== Part 4: the Z/6-chains (quad_eq, gens [g = −h])", flush=True)
    out, summ = {}, []
    # chain A: n = 72
    rows, n, newb, gens2 = build(E, N0, sA, [g], "chain A (σ_A, b = 3)", "4")
    gq = gens2[0]
    ok, T = check_code(rows, n, gq, "chain A", "4", True)
    fn = os.path.join(CODES, "gjf36_z6chain_len72.txt")
    write_code(fn, rows)
    write_gens(os.path.join(CODES, "gjf36_z6chain_len72.gens.txt"), {"g": gq, "h": mono_pow(gq, 4)})
    t0 = time.time()
    ai = rust_abs_index(fn)
    t1 = time.time()
    si, pat, _ = rs_is(fn, [], THREADS, info=True)
    print(f"4 chain A n = 72: |Index| = {ai} (ternary60 index, {t1 - t0:.0f}s); Index = {si} sign-exact "
          f"(rsigma_is, {pat} patterns, {time.time() - t1:.0f}s); R_σ_A(E) = +24 (Lemma 5.8)", flush=True)
    print(gjf_line(n, T, "4"), flush=True)
    summ.append(f"n = 72 (k = 6): checks {ok}, T_h = {T}, |Index| = {ai}, Index = {si}")
    out["A"] = (rows, n, newb, gens2)
    # control: a non-admissible system, T_h(Q_σ E) = R_σ̄(D) ≠ 0
    cbl, cbar, cs = ctrl
    r2, n2, _, g2 = build(E, N0, cbl, [g], f"control (orbit set {cs[0]}, a = {cs[1]}, R_σ̄(D) = {cbar})", "4")
    Dq, Nq = collapsed_fixed(r2, n2, mono_pow(g2[0], 4))
    Tc = signed_count_py(Dq, Nq)
    print(f"4 control n = {n2}: g ∈ Aut {is_aut_fast(g2[0], r2, n2)}; T_h = {Tc} (Python enumeration) = "
          f"R_σ̄(D) = {cbar}: {Tc == cbar} (Lemma 4.3, sign-exact)", flush=True)
    # chain B: n = 108
    if sBv is not None:
        sB, vB = sBv
        rows, n, newb, gens2 = build(E, N0, sB, [g], "chain B (σ_B, b = 6)", "4")
        gq = gens2[0]
        ok, T = check_code(rows, n, gq, "chain B", "4", False)
        write_code(os.path.join(CODES, "gjf36_z6chain_len108.txt"), rows)
        write_gens(os.path.join(CODES, "gjf36_z6chain_len108.gens.txt"), {"g": gq, "h": mono_pow(gq, 4)})
        print(f"4 chain B n = 108: Index = R_σ_B(E) = {vB:+d} by Lemma 5.8 (not computed: 2^54 patterns)",
              flush=True)
        print(gjf_line(n, T, "4"), flush=True)
        summ.append(f"n = 108 (k = 9): checks {ok}, T_h = {T}, Index = {vB:+d} (Lemma 5.8)")
        out["B"] = (rows, n, newb, gens2, vB)
    return out, summ


def part5(chains, summ):
    print("\n== Part 5: one more chain step (codes not saved)", flush=True)
    for key in ("A", "B"):
        if key not in chains:
            continue
        rows, m, newb, gens = chains[key][:4]
        v = chains[key][4] if key == "B" else 24
        t0 = time.time()
        r2, n2, nb2, g2 = build(rows, m, newb, gens, f"chain {key} step 2", "5", resplit=False)
        ok, T = check_code(r2, n2, g2[0], f"chain {key}", "5", False)
        print(f"5 chain {key} n = {n2}: Index = {v:+d} by Lemma 5.8 (not computed); {time.time() - t0:.0f}s",
              flush=True)
        print(gjf_line(n2, T, "5"), flush=True)
        summ.append(f"n = {n2} (k = {n2 // 12}): checks {ok}, T_h = {T}, Index = {v:+d} (Lemma 5.8)")


def main():
    t0 = time.time()
    print(f"THREADS = {THREADS}, SAMPLES6 = {SAMPLES6}", flush=True)
    E, h, g, D, N = part1()
    sA, ctrl = part2(E, D, N)
    sBv = part3(E, D, N)
    chains, summ = part4(E, g, D, N, sA, ctrl, sBv)
    if "--no-part5" not in sys.argv:
        part5(chains, summ)
    print("\n== Summary", flush=True)
    for s in summ:
        print("  " + s, flush=True)
    print("  <g> = <−h> ≅ Z/6 serves gcd(k,24) = 3 (h) and 6 (g) along both chains; gcd(k,24) = 12 "
          "(k ≡ 12 mod 24) needs an element of order 12 with g⁶ = −1, which <g> does not contain "
          "(and Aut(E) = <−1, h>, mainq_automorphisms.log).", flush=True)
    print(f"\ntotal {time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        main()
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
