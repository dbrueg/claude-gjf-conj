"""An independent second computation of R_σ(E₇₂) = 24 (notes/main-question.md §10; blueprint README §3).

Until now the value that decides k ≡ 0 mod 24 rested on one program: `ternary60 sl2words` (two code paths,
normalisation blocks 0 and 9, and SL2_SLOW), which evaluates the good-plane formula of the Morita form
([MQ] Cor 9.2). This script checks it with a different method and different code:

  `ternary60/src/bin/rsigma_is.rs` (binary `rsigma_is`) computes R_σ(E) = Σ_{x∈E} Π_{i∉∪σ} φ(x_i) Π_β λ(wt x|_β)
  straight from the definition, by information-set enumeration. It shares no code with src/main.rs. Since
  φ(0) = 0, only words that are nonzero outside the blocks contribute. Gaussian elimination (verified: each
  input row is re-expanded in the systematic rows) picks an information set I preferring coordinates outside
  the blocks. On E₇₂ all 36 information coordinates lie outside σ, so the sum runs over 2³⁶ ≈ 6.9·10¹⁰ sign
  patterns, walked in Gray-code order (≈ 1 min on 4 threads). It uses no Morita form, no SL₂-words and no
  symmetry.

Part 1 (the binary's selftest). Bit-sliced F₃ arithmetic; 200 random codes (n ≤ 16) against its own brute
        force, at four Gray-walk depths.
Part 2 (independent brute force). 40 random linear codes, n = 12…20, random 4-block systems, some forcing
        information coordinates into the blocks, against a Python brute force over all codewords.
Part 3 (against both existing methods). Random h-invariant Lagrangians U at n = 36 (r = 9), E = F₃² ⊗ U,
        several block systems each: rsigma_is = `ternary60 sl2words` (Morita form) = `ternary60 rsigma`
        (full enumeration of 3¹⁸ words).
Part 4 (E₇₂). The file q8z3_seed72.txt spans F₃² ⊗ U for U = q8z3_seed72.U.txt, and:
        - σ = orbit blocks 0–5 (the h-triples 0 and 1, coordinates 0–23): R_σ(E₇₂) = +24;
        - σ = ∅: Index(E₇₂) = −1608;
        - further block systems, compared with sl2words.
Part 5 (E₇₂, transformed). A random monomial copy dPE₇₂ with the transported σ: a different information set,
        and R changes by Π_{i∉σ} d_i exactly (λ is sign-blind, φ is odd).
Needs `cargo build --release` in ternary60/ (both binaries). Runtime ≈ 6 min.
"""
import os, sys, random, subprocess, time
from existence_common import rref, HERE, BIN, _TMPDIR
from mainq_common import read_code, write_code, rust_R
from mainq_morita import code_from_U, rand_U, rsys, h_blocks

CODES = os.path.join(HERE, "..", "codes")
BIN_IS = os.path.join(HERE, "..", "target", "release", "rsigma_is")
PHI = (0, -1, 1)
LAM = (0, -2, 0, 0, 1)


def run_is(rows, blocks, tag="is"):
    fn = os.path.join(_TMPDIR, tag + ".txt")
    write_code(fn, rows)
    spec = ";".join(",".join(map(str, b)) for b in blocks) if blocks else "-"
    out = subprocess.run([BIN_IS, fn, spec, "4"], capture_output=True, text=True, check=True).stdout
    d = dict(ln.split(" ", 1) for ln in out.splitlines())
    return int(d["R"]), d


def orbit_blocks(bs):
    return [[4 * b + i for i in range(4)] for b in bs]


def brute(rows, n, blocks):
    inb = {}
    for t, b in enumerate(blocks):
        for i in b:
            inb[i] = t
    B = rref(rows)
    words = [[0] * n]
    for r in B:
        words = [[(w[i] + c * r[i]) % 3 for i in range(n)] for w in words for c in range(3)]
    tot = 0
    for w in words:
        v, bw = 1, [0] * len(blocks)
        for i in range(n):
            if i in inb:
                bw[inb[i]] += w[i] != 0
            else:
                v *= PHI[w[i]]
                if not v:
                    break
        if v:
            for c in bw:
                v *= LAM[c]
            tot += v
    return tot


def part1():
    out = subprocess.run([BIN_IS, "selftest"], capture_output=True, text=True, check=True).stdout.strip()
    print("1 " + out, flush=True)
    return out.startswith("selftest ok")


def part2():
    rng = random.Random(20260927)
    ok, nz, forced = True, 0, 0
    for t in range(40):
        n = rng.randrange(12, 21)
        k = rng.randrange(3, 10)
        rows = [[rng.randrange(3) for _ in range(n)] for _ in range(k)]
        perm = list(range(n)); rng.shuffle(perm)
        nb = rng.randrange(0, n // 4 + 1)
        blocks = [sorted(perm[4 * i:4 * i + 4]) for i in range(nb)]
        want = brute(rows, n, blocks)
        got, d = run_is(rows, blocks)
        ok &= want == got
        nz += want != 0
        forced += d["info_in_blocks"] != "0"
    print(f"2 40 random linear codes (n = 12…20), Python brute force = rsigma_is: {ok} ({nz} with R ≠ 0, "
          f"{forced} with information coordinates in blocks)", flush=True)
    return ok


def part3():
    rng = random.Random(9)
    ok, rows_out, cnt = True, [], 0
    systems = [[], [0, 1, 2], [0, 1, 2, 3, 4, 5], [0, 3, 6], [1, 4, 7, 2], [0, 1, 2, 3, 4, 5, 6, 7, 8]]
    while cnt < 4:
        U = rand_U(3, rng)
        if U is None:
            continue
        cnt += 1
        E = code_from_U(U, 9)
        sl = rsys(U, systems, tag="e72p3")
        vals = []
        for s, v in zip(systems, sl):
            bl = orbit_blocks(s)
            a, _ = run_is(E, bl)
            b = rust_R(E, bl, tag="e72p3r")
            ok &= a == v == b
            vals.append(a)
        rows_out.append(vals)
    print(f"3 4 random h-invariant Lagrangians U (n = 36) × {len(systems)} systems (∅, 3, 6, 3, 4, 9 orbit blocks): "
          f"rsigma_is = sl2words = rsigma (full enumeration): {ok}; values {rows_out}", flush=True)
    return ok


def part4():
    U = read_code(os.path.join(CODES, "q8z3_seed72.U.txt"))
    E = read_code(os.path.join(CODES, "q8z3_seed72.txt"))
    same = rref(E) == rref(code_from_U(U, 18)) and len(rref(E)) == 36
    print(f"4 q8z3_seed72.txt spans F₃² ⊗ U (dimension 36): {same}; h-triples {[h_blocks(6)[b] for b in range(6)]} "
          f"(h on blocks 0–5)", flush=True)
    ok = same
    cands = [[0, 1, 2, 3, 4, 5], [], [0, 1, 2, 6, 7, 8], [3, 4, 5, 6, 7, 8], [0, 3, 6, 9, 12, 15], [0, 1, 2]]
    sl = rsys(U, cands, tag="e72p4")
    results = {}
    for s, v in zip(cands, sl):
        t0 = time.time()
        r, d = run_is(E, orbit_blocks(s))
        results[tuple(s)] = r
        ok &= r == v
        what = "R_σ(E₇₂), σ = h-triples 0, 1" if s == [0, 1, 2, 3, 4, 5] else ("Index(E₇₂)" if not s else f"R for blocks {s}")
        print(f"4   {what}: rsigma_is {r:+d} ({d['patterns']} patterns, {time.time() - t0:.0f}s), sl2words {v:+d}: "
              f"{r == v}", flush=True)
    ok &= results[(0, 1, 2, 3, 4, 5)] == 24 and results[()] == -1608
    return ok, E


def part5(E):
    rng = random.Random(72)
    n = 72
    perm = list(range(n)); rng.shuffle(perm)            # coordinate i goes to perm[i]
    d = [rng.choice((1, -1)) for _ in range(n)]
    F = []
    for r in E:
        v = [0] * n
        for i in range(n):
            v[perm[i]] = r[i] * (1 if d[i] == 1 else 2) % 3
        F.append(v)
    sig = orbit_blocks([0, 1, 2, 3, 4, 5])
    tb = [sorted(perm[i] for i in b) for b in sig]
    inside = {i for b in sig for i in b}
    sgn = 1
    for i in range(n):
        if i not in inside:
            sgn *= d[i]
    r, dd = run_is(F, tb, tag="e72p5")
    ok = r == sgn * 24
    print(f"5 random monomial copy dPE₇₂, σ transported: rsigma_is {r:+d}, expected Π_(i∉σ) d_i · 24 = {sgn * 24:+d}: "
          f"{ok}", flush=True)
    return ok


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    t0 = time.time()
    with contextlib.redirect_stdout(Tee()):
        a = part1()
        b = part2()
        c = part3()
        d, E = part4()
        e = part5(E)
        print(f"parts pass: 1 {a}, 2 {b}, 3 {c}, 4 {d}, 5 {e}; all checks pass: {a and b and c and d and e} "
              f"[{time.time() - t0:.0f}s]", flush=True)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
