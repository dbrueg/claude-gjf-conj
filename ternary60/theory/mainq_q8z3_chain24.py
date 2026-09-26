"""The Main Question for k ≡ 0 mod 24 (notes/main-question.md §10): a Q₈ × ℤ/3-equivariant chain from a
length-72 seed.

Seed: ../codes/q8z3_seed72.U.txt (a Lagrangian U ⊂ F₃³⁶ in Morita form, found by the targeted search of
mainq_q8z3_seed72.py part 2), E = F₃² ⊗ U of length 72, G = Q₈ × <h> with J, K = left multiplication by
i, j on each of the 18 Q₈-orbits and h cycling them in six triples (mainq_morita.py). σ = the six
orbit blocks of h-triples 0 and 1.

Part 1 (seed): U Lagrangian, h-invariant and free over F₃[u]/u³; E self-dual; J, K, h ∈ Aut(E) with
        J² = K² = −1, JK = −KJ, h³ = 1, h fixed-point-free and commuting with J, K. Index(E) sign-exact
        (sl2words) and |Index(E)| by `ternary60 index` (binary-word count, independent). R_σ(E) = 24 by
        sl2words with two normalisation blocks and by the older enumeration (SL2_SLOW). On the collapsed
        fixed code D (length 24): T_h(E) = Index(D) and R_σ̄(D) by direct enumeration (rsigma).
Part 2 (chain): Lemma 4.1 with G, refining the G-orbit of one step-1 block at each step:
        n = 72 → 144 (k = 12) → 288 (k = 24). At each length: self-duality, J, K, h ∈ Aut, the relations,
        h fixed-point-free with cycle shape 3^{n/3}. At n = 144: |T_h| by `ternary60 index` on the
        collapsed fixed code (length 48). Index = R_σ(E) = 24 at every length by [I Lemma 5.8], and
        T_h = R_σ̄(D) = 0 by Lemma 4.3. Codes saved to ../codes/q8z3_chain_len<n>.txt (+ .gens.txt).
"""
import os, subprocess, sys, time
from existence_common import rref, dot, rust_index, HERE, BIN, _TMPDIR
from mainq_common import (closure, is_aut, mono_mul, mono_neg, mono_id, mono_pow, cycle_type, fixed_code,
                          rust_R, read_code, write_code)
from mainq_equivariant import quad_eq, choose_splits
from mainq_morita import code_from_U, fixed_U, collapse, h_blocks, h_gen, q8_gens, omega, happly, rsys

CODES = os.path.join(HERE, "..", "codes")
SIGMA = [0, 1, 2, 3, 4, 5]          # h-triples 0 and 1


def shape(p):
    from collections import Counter
    return " ".join(f"{L}^{c}" for L, c in sorted(Counter(cycle_type(p)).items()))


def self_dual(rows, n):
    R = rref(rows)
    return len(R) == n // 2 and all(dot(a, b) == 0 for i, a in enumerate(R) for b in R[i:])


def relations(J, K, H, n):
    neg, one = mono_neg(n), mono_id(n)
    return (mono_mul(J, J) == neg and mono_mul(K, K) == neg and mono_mul(J, K) == mono_mul(neg, mono_mul(K, J))
            and mono_pow(H, 3) == one and mono_mul(H, J) == mono_mul(J, H) and mono_mul(H, K) == mono_mul(K, H))


def rsys_b0(U, systems, b0, slow=False):
    fn = os.path.join(_TMPDIR, "c24.u"); sf = os.path.join(_TMPDIR, "c24.sys")
    with open(fn, "w") as fh:
        fh.write("\n".join("".join(map(str, r)) for r in U) + "\n")
    with open(sf, "w") as fh:
        fh.write("\n".join(",".join(map(str, s)) if s else "-" for s in systems) + "\n")
    env = dict(os.environ)
    if slow:
        env["SL2_SLOW"] = "1"
    out = subprocess.run([BIN, "sl2words", fn, str(b0), sf], capture_output=True, text=True, check=True,
                         env=env).stdout
    vals = dict((int(a), int(b)) for _, a, b in (ln.split() for ln in out.splitlines() if ln.startswith("R ")))
    return [vals[i] for i in range(len(systems))]


def save_gens(path, gens):
    with open(path, "w") as fh:
        for name, (p, s) in zip("JKH", gens):
            fh.write(f"{name} perm: {' '.join(map(str, p))}\n{name} sign: {' '.join(map(str, s))}\n")


def part1():
    U = read_code(os.path.join(CODES, "q8z3_seed72.U.txt"))
    k, r, n = 6, 18, 72
    hb = h_blocks(k)
    iso = all(omega(a, b) == 0 for a in U for b in U) and len(rref(U)) == r
    hinv = len(rref(U + [happly(hb, u) for u in U])) == r
    free = len(fixed_U(U, hb)) == k
    E = code_from_U(U, r)
    write_code(os.path.join(CODES, "q8z3_seed72.txt"), E)
    J, K = q8_gens(r); H = h_gen(k)
    print(f"1 seed U: Lagrangian {iso}, h-invariant {hinv}, free over F_3[u]/u^3 {free}; E = F_3^2 (x) U self-dual "
          f"{self_dual(E, n)}; J, K, h in Aut(E) {all(is_aut(g, E, n) for g in (J, K, H))}; relations "
          f"{relations(J, K, H, n)}; h cycle shape {shape(H[0])}", flush=True)
    t0 = time.time()
    I, R0, R9 = rsys_b0(U, [[], SIGMA], 0)[0], rsys_b0(U, [SIGMA], 0)[0], rsys_b0(U, [SIGMA], 9)[0]
    Rslow = rsys_b0(U, [SIGMA], 0, slow=True)[0]
    Iabs = abs(rust_index(E, "c24I"))
    print(f"1 Index(E) = {I} (sl2words), |Index(E)| = {Iabs} (ternary60 index); R_σ(E) = {R0} (b0 = 0), "
          f"{R9} (b0 = 9), {Rslow} (older enumeration)  [{time.time() - t0:.0f}s]", flush=True)
    Ub = collapse(fixed_U(U, hb), k)
    D = code_from_U(Ub, k)
    T = rust_R(D, [], "c24T")
    Rbar = rust_R(D, [list(range(0, 4)), list(range(4, 8))], "c24Rb")
    print(f"1 collapsed fixed code D (length 24, self-dual {self_dual(D, 24)}): T_h(E) = Index(D) = {T}, "
          f"R_σ̄(D) = {Rbar} (direct enumeration)", flush=True)
    return E, [J, K, H], R0, Rbar


def part2(E, gens, R, Rbar):
    m = 72
    G = closure(gens, m)
    blocks = choose_splits(G, [tuple(range(4 * b, 4 * b + 4)) for b in SIGMA])
    for step in (1, 2):
        t0 = time.time()
        rows, n, newb, g2 = quad_eq(E, m, blocks, gens, refine="orbit0")
        J, K, H = g2
        sd = self_dual(rows, n)
        aut = all(is_aut(g, rows, n) for g in g2)
        rel = relations(J, K, H, n)
        fpf = all(H[0][i] != i for i in range(n))
        msg = (f"2 n = {n} (k = {n // 12}): self-dual {sd}, J, K, h in Aut {aut}, relations {rel}, h fixed-point-free "
               f"{fpf} (cycle shape {shape(H[0])}); next system {len(newb)} blocks")
        if n == 144:
            Fx = fixed_code(rows, n, H)
            reps, seen = [], set()
            for i in range(n):
                if i not in seen:
                    orb = [i, H[0][i], H[0][H[0][i]]]; seen.update(orb); reps.append(i)
            D1 = [[v[i] for i in reps] for v in Fx]
            msg += (f"; collapsed fixed code: length {len(reps)}, self-dual {self_dual(D1, len(reps))}, "
                    f"|T_h| = {abs(rust_index(D1, 'c24T1'))} (ternary60 index)")
        msg += f"; Index = R_σ(E) = {R} and T_h = R_σ̄(D) = {Rbar} by [I Lemma 5.8], Lemma 4.3  [{time.time() - t0:.0f}s]"
        print(msg, flush=True)
        write_code(os.path.join(CODES, f"q8z3_chain_len{n}.txt"), rref(rows))
        save_gens(os.path.join(CODES, f"q8z3_chain_len{n}.gens.txt"), g2)
        E, m, blocks, gens = rows, n, newb, g2


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        E, gens, R, Rbar = part1()
        part2(E, gens, R, Rbar)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
