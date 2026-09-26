"""Seeds at length 72 for a Q₈ × ℤ/3-equivariant chain to k ≡ 0 mod 24 (notes/main-question.md §9.4).

G = Q₈ × <h> on 72 coordinates in Morita form (mainq_morita.py): 18 Q₈-orbits (blocks), h cycling them
in six triples. A G-stable system σ of b₀ = 6 orbit blocks is a union of two h-triples (15 systems).
The chain Q_σ, Q_σ″, … (Lemma 4.1, G = Q₈ × <h>) has k = 12, 24, 36, …, Index = R_σ(E) [I Lemma 5.8]
and T_h = R_σ̄(D) (Lemma 4.3), D = collapsed fixed code (length 24, σ̄ = the two collapsed blocks).
A seed with R_σ = ±24 and R_σ̄(D) = 0 would give index 1 at every k ≡ 0 mod 24.

Part 1: random G-invariant codes (free over R = F₃[u]/u³): distribution of R_σ over the systems with
        R_σ̄(D) = 0 (their residues mod 72 and smallest |R_σ|).
Part 2: targeted: reductions Ū whose collapsed code has R_σ̄ = 0 for all 15 systems (and some R_σ ≢ 0
        mod 72 in part 1), with random free lifts (A₁, S); every system is then admissible.
Part 3: the chain pipeline in the Morita layout, checked where it is computable: from k = 3 seeds and
        one h-triple (n = 36 → 72), |Index(Q_σ E)| = |R_σ(E)| (ternary60 index) and T_h(Q_σ E) =
        R_σ̄(D) (enumeration of the fixed code).
A hit is saved to ../codes/q8z3_seed72_<i>.txt (U in .U.txt) with its system.
"""
import itertools, json, os, random, sys, time
from collections import Counter
from existence_common import rref, rust_index, dot, HERE
from mainq_common import closure, fixed_code, is_aut, rust_R, write_code
from mainq_equivariant import quad_eq, choose_splits
from mainq_morita import (rand_U, code_from_U, fixed_U, collapse, h_blocks, h_gen, q8_gens, complement,
                          lift, rsys)

K6 = 6
PAIRS = list(itertools.combinations(range(6), 2))
SYS = [sorted(b for s in pr for b in (3 * s, 3 * s + 1, 3 * s + 2)) for pr in PAIRS]
SYSBAR = [list(pr) for pr in PAIRS]


def evaluate(U, tag):
    """(Index, [R_σ], T_h, [R_σ̄(D)]) for a free h-invariant Lagrangian U at k = 6."""
    Ub = collapse(fixed_U(U, h_blocks(K6)), K6)
    assert len(Ub) == K6, "U is not free over R"
    Rb = rsys(Ub, [[]] + SYSBAR, tag + "b")
    R = rsys(U, [[]] + SYS, tag)
    return R[0], R[1:], Rb[0], Rb[1:]


def save_hit(U, i, R, n_hits):
    base = os.path.join(HERE, "..", "codes", f"q8z3_seed72_{n_hits}")
    write_code(base + ".txt", code_from_U(U, 18)); write_code(base + ".U.txt", U)
    with open(base + ".sys.txt", "w") as fh:
        fh.write(",".join(map(str, SYS[i])) + "\n")
    print(f"  HIT saved {os.path.basename(base)}: σ = h-triples {PAIRS[i]}, R_σ = {R}", flush=True)


def random_free(rng):
    while True:
        U = rand_U(K6, rng)
        if U is not None and len(fixed_U(U, h_blocks(K6))) == K6:
            return U


def part1(rng, N):
    vals, reds, hits = [], [], 0
    t0 = time.time()
    for _ in range(N):
        U = random_free(rng)
        I, R, T, Rb = evaluate(U, "s72a")
        z = [i for i in range(15) if Rb[i] == 0]
        vals += [R[i] for i in z]
        if len(z) == 15 and any(R[i] % 72 for i in z):
            reds.append(collapse(fixed_U(U, h_blocks(K6)), K6))
        for i in z:
            if abs(R[i]) == 24:
                hits += 1; save_hit(U, i, R[i], hits)
    print(f"1 {N} random free codes: {len(vals)} systems with R_σ̄(D) = 0; R_σ mod 72: "
          f"{dict(sorted(Counter(v % 72 for v in vals).items()))}; smallest |R_σ|: "
          f"{sorted(abs(v) for v in vals)[:8]}; hits {hits}; {len(reds)} reductions with R_σ̄ ≡ 0 "
          f"[{time.time() - t0:.0f}s]", flush=True)
    return reds, hits


def part2(rng, reds, N, hits):
    if not reds:
        print("2 no reductions from part 1", flush=True); return
    Fs = [complement(L, K6) for L in reds]
    vals = []
    t0 = time.time()
    for it in range(N):
        L, F = reds[it % len(reds)], Fs[it % len(reds)]
        A1 = [[0] * K6 for _ in range(K6)]; S = [[0] * K6 for _ in range(K6)]
        for i in range(K6):
            S[i][i] = rng.randrange(3)
            for j in range(i + 1, K6):
                A1[i][j] = rng.randrange(3); A1[j][i] = (-A1[i][j]) % 3
                S[i][j] = S[j][i] = rng.randrange(3)
        U = rref(lift(L, F, A1, S, K6))
        I, R, T, Rb = evaluate(U, "s72b")
        assert T == 0 and all(x == 0 for x in Rb)
        vals += R
        for i in range(15):
            if abs(R[i]) == 24:
                hits += 1; save_hit(U, i, R[i], hits)
    print(f"2 {N} free lifts over {len(reds)} reductions (all 15 systems admissible): R_σ mod 72 "
          f"{dict(sorted(Counter(v % 72 for v in vals).items()))}; smallest |R_σ|: "
          f"{sorted(abs(v) for v in vals)[:8]}; hits {hits} [{time.time() - t0:.0f}s]", flush=True)


def part3(rng, N=3):
    k = 3
    ok = 0
    for _ in range(N):
        U = None
        while U is None:
            U = rand_U(k, rng)
        E = code_from_U(U, 9); J, K = q8_gens(9); H = h_gen(3)
        G = closure([J, K, H], 36)
        s0 = rng.randrange(3)
        sig = [3 * s0, 3 * s0 + 1, 3 * s0 + 2]
        blocks = choose_splits(G, [tuple(range(4 * b, 4 * b + 4)) for b in sig])
        R = rsys(U, [sig], "s72c")[0]
        D = collapse(fixed_U(U, h_blocks(k)), k)
        Rbar = rust_R(code_from_U(D, k), [list(range(4 * s0, 4 * s0 + 4))], "s72cb")
        rows, n, newb, g2 = quad_eq(E, 36, blocks, [J, K, H], refine="orbit0")
        sd = len(rows) == n // 2 and all(dot(a, b) == 0 for a in rows for b in rows)
        inv = all(is_aut(g, rows, n) for g in g2)
        I = abs(rust_index(rows, "s72ci"))
        Th = rust_R(fixed_code(rows, n, g2[2]), [], "s72ct")
        good = sd and inv and I == abs(R) and Th == Rbar
        ok += good
        print(f"3 k = 3 seed, σ = triple {s0}: R_σ = {R}, |Index(Q_σ E)| = {I}; R_σ̄(D) = {Rbar}, T_h = {Th}; "
              f"self-dual {sd}, G-invariant {inv}; next system has {len(newb)} blocks", flush=True)
    print(f"3 pipeline consistent on {ok}/{N}", flush=True)


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    n1 = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    n2 = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    rng = random.Random(7224)
    with contextlib.redirect_stdout(Tee()):
        reds, hits = part1(rng, n1)
        part2(rng, reds, n2, hits)
        part3(rng)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
