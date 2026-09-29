"""Check of the computable claims of paper/conj14.tex, from the data printed in the paper (2026-09-29).

The seed data are parsed from the .tex itself: the tetracode, the Golay matrix (§5), J, K with their signs, σ_Q,
β, β₁, β₂ (§7), the generator matrix of E₃₆ (App. A.1), and the Lagrangian U with the Morita coordinates and the
block actions of J, K (App. A.2). So a typo in a printed matrix or permutation makes this script fail.

The chains of Theorems B and C are built by a fresh implementation of Construction 6.3: the extension g ↦ g♯
(partners follow with the same sign), tetracodes invariant under the block stabilisers and transported along G,
step-one blocks B_π = π ⊔ π* split into π and π*, and σ″ = the refinement of the G-orbit of the first step-one
block, with blocks π ⊔ π** and π* ⊔ π***. On every code of every chain the claims of Lemma 6.4 and Proposition
6.6 are checked (self-duality, g♯ ∈ Aut, relations, fixed coordinates, compatibility and block types, |𝓑_j|).

Heavy sums (2^24 to 2^36 sign patterns: Index at n = 48, 72, R_σQZ(E₇₂), the 11,178 R_σ(E₃₆) of §7.2, T_h at
n = 144, 180) use the reviewed Rust information-set enumerator `rsigma_is` (ternary60/src/bin/rsigma_is.rs) when
it is built; with --fast (or without the binary) they are skipped and reported as skipped. Everything else is
stdlib Python (helpers from review_conj14_check.py and review_seed_verify.py).

Parts (paper numbering):
 1 §2    tetracode facts; exactly 8 self-dual codes of length 4, the monomial images of T; (T); (2.1).
 2 §3    Theorem 3.1 on Golay and random self-dual codes (n = 12, 24); Remark 3.4 (1), (2).
 3 §4    Lemmas 4.1, 4.2 exhaustively; λ̂ = 9λ; Lemmas 4.5, 4.6 by enumeration on random codes (self-dual or
         not, random tetracodes and splits, all subsets 𝓑); the gadget of Remark 4.7.
 4 §5    Golay facts; Proposition 5.1 and its distributions; Lemma 5.4 on all 5775 partitions; Remark 5.3 (1)
         at n = 24; the chains of Theorem B to n = 84 (Index sign-exact at 24, 36, 48).
 5 §6    Lemma 6.2 for every group of each type; the non-admissible actions after Lemma 6.4; the τ_Q facts.
 6 §7.1  J, K ∈ Aut(G12) and relations; the 1320 Q₈ (one conjugacy class); Proposition 7.1 for all of them;
         σ_Q; Proposition 7.2's chain to n = 96 (Index at 48).
 7 §7.2  E₃₆ = codes/gjf_ex57_len36.txt; h; Index, T_h; σ_A, σ_B (Proposition 7.3); the 13,365 systems and the
         803 good ones; both Z/6-chains to n = 144, 180 (T_h = 0; Index at 72).
 8 §7.3  the quaternion model and the Morita coordinates; U Lagrangian; E₇₂ = codes/q8z3_seed72.txt; J, K, h;
         R^h_σQZ = 0, R_σQZ = 24; the Q₈ × Z/3-chain to n = 288 (T_h = 0 at 144).
 9 §8-9  Theorem D (48 | Index, the four-code identity (8.1) and the induction step) on random g-invariant codes;
         Lemma 9.2, Remark 9.3, Propositions 9.4, 9.5 on random codes and neighbours.

Usage: python3 conj14_paper_check.py [--fast]      (log: conj14_paper_check.log)
"""
import concurrent.futures
import itertools
import os
import random
import re
import subprocess
import sys
import tempfile
import time

from review_conj14_check import (vec, unvec, vadd, vneg, vscale, pc, vdot, rref, codewords, R_sigma,
                                 index_count, PLACE, psi, kappa, Q_sigma)
from review_seed_verify import R_infoset, twined_R, left_kernel, fixed_subcode, read_rows

HERE = os.path.dirname(os.path.abspath(__file__))
TEX = os.path.normpath(os.path.join(HERE, "..", "..", "paper", "conj14.tex"))
CODES = os.path.normpath(os.path.join(HERE, "..", "codes"))
RSIGMA = os.path.normpath(os.path.join(HERE, "..", "target", "release", "rsigma_is"))
LAM = (0, -2, 0, 0, 1)
LOG = []
T0 = time.time()
FAST = "--fast" in sys.argv
RUST = (not FAST) and os.path.exists(RSIGMA)


def log(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.append(s)


def need(cond, what):
    if not cond:
        raise AssertionError(what)


def stamp():
    return f"[{time.time() - T0:.0f}s]"


# ================================================================ parsing the paper
def parse_tex(T):
    d = {}
    m = re.search(r"The \\emph\{tetracode\}\s+\$T\\subseteq\\F\^4\$\s+is\s+spanned\s+by\s+"
                  r"\$\((\d),(\d),(\d),(\d)\)\$\s+and\s+\$\((\d),(\d),(\d),(\d)\)\$", T)
    v = [int(x) for x in m.groups()]
    d["T"] = [v[:4], v[4:]]
    need(r"\lambda(0)=0,\quad\lambda(1)=-2,\quad\lambda(2)=\lambda(3)=0,\quad\lambda(4)=1" in T, "λ as printed")
    m = re.search(r"Let \$G_\{12\}.*?\\begin\{pmatrix\}(.*?)\\end\{pmatrix\}", T, re.S)
    d["golay"] = [[int(x) for x in line.strip().rstrip("\\").split("&")]
                  for line in m.group(1).strip().splitlines()]
    for name, sname in (("J", "s"), ("K", "t")):
        m = re.search(name + r"&=((?:\(\d+\\,\d+\))+), & " + sname + r"&=\(([-+,]+)\)", T)
        p = list(range(12))
        for a, b in re.findall(r"\((\d+)\\,(\d+)\)", m.group(1)):
            p[int(a)], p[int(b)] = int(b), int(a)
        d[name] = (tuple(p), tuple(1 if c == "+" else -1 for c in m.group(2).split(",")))
    m = re.search(r"\\sigma_Q=\\bigl\\\{(.*?)\\bigr\\\}", T)
    d["sigmaQ"] = [((int(a), int(b)), (int(c), int(e))) for a, b, c, e in
                   re.findall(r"\\\{(\d+),(\d+)\\\}\\sqcup\\\{(\d+),(\d+)\\\}", m.group(1))]
    m = re.search(r"\\beta=\\\{([\d,]+)\\\},\\qquad\\beta_1=\\\{([\d,]+)\\\},\\qquad\\beta_2=\\\{([\d,]+)\\\}", T)
    d["betas"] = [tuple(int(x) for x in g.split(",")) for g in m.groups()]
    need(r"$\{4b,4b+1\}\sqcup\{4b+2,4b+3\}$, $0\le b\le5$" in T, "σ_QZ as printed")
    verb = re.findall(r"\\begin\{verbatim\}(.*?)\\end\{verbatim\}", T, re.S)
    d["E36"], d["U"] = [[[int(c) for c in line.strip()] for line in blk.strip().splitlines()] for blk in verb]
    m = re.search(r"\$p\((\d),(\d),(\d),(\d)\)\+q\((\d),(\d),(\d),(\d)\)\+r\((\d),(\d),(\d),(\d)\)"
                  r"\+s\((\d),(\d),(\d),(\d)\)\$", T)
    v = [int(x) for x in m.groups()]
    d["morita"] = [v[0:4], v[4:8], v[8:12], v[12:16]]
    for name in ("J", "K"):
        m = re.search(name + r"\(e_0,e_1,e_2,e_3\)=\(([^)]*)\)", T)
        p, s = [0] * 4, [0] * 4
        for i, tok in enumerate(m.group(1).split(",")):
            p[i], s[i] = int(tok[-1]), (-1 if tok.startswith("-") else 1)
        d["blk" + name] = (tuple(p), tuple(s))
    need(r"i\mapsto\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)" in T and
         r"j\mapsto\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)" in T, "quaternion model as printed")
    m = re.search(r"It maps \$\((\d),(\d),(\d),(\d)\)\$ and \$\((\d),(\d),(\d),(\d)\)\$ to\s+"
                  r"\$\((\d),(\d),(\d),(\d)\)\$ and \$\((\d),(\d),(\d),(\d)\)\$", T)
    v = [int(x) for x in m.groups()]
    d["tauJ"] = [v[0:4], v[4:8], v[8:12], v[12:16]]
    return d


# ================================================================ signed permutations: g e_i = s_i e_{p(i)}
def sp_id(n):
    return (tuple(range(n)), (1,) * n)


def sp_neg(n):
    return (tuple(range(n)), (-1,) * n)


def sp_mul(g, h):
    """g∘h."""
    pg, sg = g
    ph, sh = h
    return (tuple(pg[j] for j in ph), tuple(sh[i] * sg[ph[i]] for i in range(len(ph))))


def sp_inv(g):
    p, s = g
    q, t = [0] * len(p), [0] * len(p)
    for i in range(len(p)):
        q[p[i]], t[p[i]] = i, s[i]
    return (tuple(q), tuple(t))


def sp_apply(g, x):
    p, s = g
    y = [0] * len(x)
    for i, v in enumerate(x):
        y[p[i]] = (s[i] * v) % 3
    return y


def closure(gens):
    n = len(gens[0][0])
    G = {sp_id(n)}
    frontier = [sp_id(n)]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = sp_mul(g, x)
                if y not in G:
                    G.add(y)
                    new.append(y)
        frontier = new
    return sorted(G)


def fixed_coords(g):
    return [i for i in range(len(g[0])) if g[0][i] == i]


# ================================================================ codes via bit-sliced systematic form
def bs_rref(vs, n):
    rows = list(vs)
    out = []
    for col in range(n):
        bit = 1 << col
        k = next((t for t, (A, B) in enumerate(rows) if (A | B) & bit), None)
        if k is None:
            continue
        r = rows.pop(k)
        if r[1] & bit:
            r = vneg(r)
        mr = vneg(r)

        def elim(x):
            if x[0] & bit:
                return vadd(x, mr)
            if x[1] & bit:
                return vadd(x, r)
            return x
        rows = [elim(x) for x in rows]
        out = [(c, elim(x)) for c, x in out]
        out.append((col, r))
    return out


class Code:
    def __init__(self, rows, n):
        self.n = n
        self.rows = [list(r) for r in rows]
        self.piv = bs_rref([vec(r) for r in rows], n)
        self.dim = len(self.piv)

    def reduce(self, x):
        for col, r in self.piv:
            bit = 1 << col
            if x[0] & bit:
                x = vadd(x, vneg(r))
            elif x[1] & bit:
                x = vadd(x, r)
        return x

    def contains(self, x):
        return self.reduce(vec(x)) == (0, 0)

    def self_dual(self):
        vs = [r for _, r in self.piv]
        return 2 * self.dim == self.n and all(vdot(a, b) == 0 for i, a in enumerate(vs) for b in vs[i:])

    def is_aut(self, g):
        return all(self.contains(sp_apply(g, r)) for r in self.rows)

    def basis(self):
        return [unvec(r, self.n) for _, r in self.piv]

    def key(self):
        return tuple(r for _, r in self.piv)


def f_of(x):
    """f(x) = prod φ(x_i) for a list x."""
    s = 1
    for v in x:
        if v % 3 == 0:
            return 0
        if v % 3 == 1:
            s = -s
    return s


# ================================================================ the Rust information-set enumerator
def rust_R(rows, n, blocks, threads=4):
    """R_σ via rsigma_is (blocks: list of 4-sets; [] gives F(E), the index if E is self-dual)."""
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "code.txt")
        with open(path, "w") as fh:
            fh.write("\n".join("".join(str(v % 3) for v in r) for r in rows) + "\n")
        spec = ";".join(",".join(str(i) for i in sorted(b)) for b in blocks) if blocks else "-"
        out = subprocess.run([RSIGMA, path, spec, str(threads)], capture_output=True, text=True, check=True).stdout
    for line in out.splitlines():
        if line.startswith("R "):
            return int(line.split()[1])
    raise RuntimeError(out)


def F_code(rows, n, heavy_bits):
    """F(E) sign-exactly; Python information-set enumeration if the pattern count is small, else Rust."""
    if heavy_bits <= 20:
        return R_infoset(rows, n, []), "Python"
    if RUST:
        return rust_R(rows, n, []), "rsigma_is"
    return None, "skipped"


# ================================================================ Construction 6.3
def extend_gen(g, partner, n_new):
    p, s = g
    P = list(p) + [None] * (n_new - len(p))
    S = list(s) + [None] * (n_new - len(p))
    for i, i2 in partner.items():
        need(p[i] in partner, "g maps block coordinates to block coordinates")
        P[i2], S[i2] = partner[p[i]], s[i]
    return (tuple(P), tuple(S))


def invariant_tetracodes(Y, stab):
    """The tetracodes on the 4-tuple Y (words in the order of Y) invariant under stab (in PLACE order)."""
    pos = {y: t for t, y in enumerate(Y)}
    out = []
    for P in PLACE:
        words = set(tuple(w) for w in P)
        good = True
        for p, s in stab:
            for w in words:
                img = [0] * 4
                for t, y in enumerate(Y):
                    img[pos[p[y]]] = (s[y] * w[t]) % 3
                if tuple(img) not in words:
                    good = False
                    break
            if not good:
                break
        if good:
            out.append(words)
    return out


def hadamard(rows, pairs):
    for r in rows:
        for i, j in pairs:
            a, b = r[i], r[j]
            r[i], r[j] = (a + b) % 3, (a - b) % 3


def step(rows, n, blocks, gens):
    """One Hadamard step: partners n, n+1, ... for the coordinates of the 4-tuples in `blocks`; tetracodes on the
    partner sets invariant under the stabilisers (Construction 6.3 (iii)), transported along G♯; then (x, y) ↦
    (x + y, x − y) on every pair. Returns (rows, n', partner, gens♯, G♯)."""
    partner = {}
    for Y in blocks:
        for y in Y:
            partner[y] = n + len(partner)
    n2 = n + len(partner)
    gens2 = [extend_gen(g, partner, n2) for g in gens]
    G2 = closure(gens2)
    T_of = {}
    for Y in blocks:
        Ys = tuple(partner[y] for y in Y)
        key = frozenset(Ys)
        if key in T_of:
            continue
        stab = [g for g in G2 if frozenset(g[0][y] for y in Ys) == key]
        inv = invariant_tetracodes(Ys, stab)
        need(inv, f"an invariant tetracode on {Ys} (Lemma 6.2)")
        words = inv[0]
        for p, s in G2:                                          # T_{gβ} = g♯ T_β, well defined
            img_key = frozenset(p[y] for y in Ys)
            cs = sorted(img_key)
            code = set()
            for w in words:
                img = {p[y]: (s[y] * w[t]) % 3 for t, y in enumerate(Ys)}
                code.add(tuple(img[c] for c in cs))
            code = frozenset(code)
            if img_key in T_of:
                need(T_of[img_key] == code, "T_{gβ} independent of g (Lemma 6.4 (1))")
            else:
                T_of[img_key] = code
    need(all(frozenset(partner[y] for y in Y) in T_of for Y in blocks), "every block got a tetracode")
    out = [list(r) + [0] * (n2 - n) for r in rows]
    for key, code in T_of.items():
        cs = sorted(key)
        basis = rref([list(w) for w in code], 4)
        need(len(basis) == 2, "tetracode of dimension 2")
        for bv in basis:
            r = [0] * n2
            for t, c in enumerate(cs):
                r[c] = bv[t]
            out.append(r)
    hadamard(out, list(partner.items()))
    return out, n2, partner, gens2, G2


def quad(rows, n, sigma, gens):
    """Q_σ(E) with the choices of Construction 6.3; sigma = list of blocks (π1, π2)."""
    rows1, n1, star, gens1, _ = step(rows, n, [a + b for a, b in sigma], gens)
    S1 = []
    for a, b in sigma:
        for pi in (a, b):
            S1.append((pi, (star[pi[0]], star[pi[1]])))            # B_π = π ⊔ π*, split into π and π*
    rows2, n2, dstar, gens2, G2 = step(rows1, n1, [a + b for a, b in S1], gens1)
    return dict(rows=rows2, n=n2, gens=gens2, G=G2, S1=S1, star=star, dstar=dstar, n1=n1)


def refine(Q, B0):
    """σ″ for the G♯-orbit of the step-one block B0: blocks π ⊔ π** and π* ⊔ π***, split as (iv)."""
    d = Q["dstar"]
    by_set = {frozenset(a + b): (a, b) for a, b in Q["S1"]}
    orbit, seen = [], set()
    for p, s in Q["G"]:
        img = frozenset(p[y] for y in B0[0] + B0[1])
        if img not in seen:
            seen.add(img)
            a, b = by_set[img]
            need(frozenset(p[y] for y in B0[0]) == frozenset(a), "g maps π to the pair π of B_{gπ}")
            orbit.append((a, b))
    sigma = []
    for pi, pis in orbit:
        sigma.append((pi, (d[pi[0]], d[pi[1]])))
        sigma.append((pis, (d[pis[0]], d[pis[1]])))
    return sigma, len(orbit)


def classify(rho, pairs):
    one, neg = sp_id(4), sp_neg(4)
    rho = set(rho)
    if rho == {one, neg}:
        return "τ0"
    sq = [j for j in rho if sp_mul(j, j) == neg]
    if len(rho) == 4:
        for j in sq:
            if rho == {one, neg, j, sp_mul(neg, j)} and all(frozenset(j[0][t] for t in P) == P for P in pairs):
                return "τJ"
    if len(rho) == 8:
        for j in sq:
            if {frozenset((t, j[0][t])) for t in range(4)} != set(pairs):
                continue
            for k in sq:
                if sp_mul(k, j) == sp_mul(neg, sp_mul(j, k)) and set(closure([j, k])) == rho:
                    return "τQ"
    return None


def block_types(sigma, G):
    """σ-compatibility (blocks onto blocks, pairs onto pairs) and the type of each block (Definition 6.1)."""
    pairsets = {frozenset(a + b): {frozenset(a), frozenset(b)} for a, b in sigma}
    for p, s in G:
        for a, b in sigma:
            img = frozenset(p[y] for y in a + b)
            need(img in pairsets and {frozenset(p[y] for y in a), frozenset(p[y] for y in b)} == pairsets[img],
                 "σ-compatible")
    types = []
    for a, b in sigma:
        Y = a + b
        pos = {y: t for t, y in enumerate(Y)}
        rho = set()
        for p, s in G:
            if frozenset(p[y] for y in Y) == frozenset(Y):
                rho.add((tuple(pos[p[y]] for y in Y), tuple(s[y] for y in Y)))
        types.append(classify(rho, (frozenset((0, 1)), frozenset((2, 3)))))
    return types


def check_code(rows, n, gens, relations, fpf_names=()):
    """Self-duality, generators in Aut, the relations, and fixed-point-freeness of the named elements."""
    C = Code(rows, n)
    sd = C.self_dual()
    aut = all(C.is_aut(g) for g in gens.values())
    rel = all(fn(gens, n) for fn in relations)
    fpf = all(not fixed_coords(gens[name]) for name in fpf_names)
    return sd, aut, rel, fpf


def collapsed_T(rows, n, h, heavy_ok=True):
    """T_h for a coordinate permutation h of order 3 without fixed coordinates: E^h collapsed to one coordinate
    per h-orbit (f(x) = f(x̄), as φ³ = φ), then F of that code."""
    need(all(v == 1 for v in h[1]), "h is a plain permutation")
    F = fixed_subcode(rows, n, h)
    reps = sorted({min(i, h[0][i], h[0][h[0][i]]) for i in range(n)})
    D = [[r[i] for i in reps] for r in F]
    dim = len(F)
    if dim <= 20:
        return R_infoset(D, len(reps), []), dim, "Python"
    if RUST and heavy_ok:
        return rust_R(D, len(reps), []), dim, "rsigma_is"
    return None, dim, "skipped"


def rel_Q8(gens, n):
    J, K, neg = gens["J"], gens["K"], sp_neg(n)
    return sp_mul(J, J) == neg and sp_mul(K, K) == neg and sp_mul(K, J) == sp_mul(neg, sp_mul(J, K))


def rel_h(gens, n):
    h = gens["h"]
    return sp_mul(h, sp_mul(h, h)) == sp_id(n) and h != sp_id(n)


def rel_hJK(gens, n):
    h = gens["h"]
    return all(sp_mul(h, gens[x]) == sp_mul(gens[x], h) for x in ("J", "K"))


def run_chain(label, rows, n, sigma0, gens, steps, relations, fpf_names, expect_types0, expect_orbit):
    """Proposition 6.6: E_1 = Q_σ0(E_0), then refine the G-orbit of the first step-one block and repeat.
    gens: dict name -> signed permutation. Returns the list of stages."""
    names = list(gens)
    G0 = closure(list(gens.values()))
    types0 = block_types(sigma0, G0)
    need(types0 == expect_types0, f"{label}: types of σ0 {types0}")
    need(sp_neg(n) in G0, f"{label}: −1 ∈ G")
    fixed0 = {x: bool(fixed_coords(g)) for x, g in gens.items()}
    stages = []
    cur_rows, cur_n, cur_sigma, cur_gens = rows, n, sigma0, [gens[x] for x in names]
    for j in range(1, steps + 1):
        Q = quad(cur_rows, cur_n, cur_sigma, cur_gens)
        g = dict(zip(names, Q["gens"]))
        sd, aut, rel, fpf = check_code(Q["rows"], Q["n"], g, relations, fpf_names)
        need(sd and aut and rel and fpf, f"{label} n = {Q['n']}: self-dual {sd}, Aut {aut}, relations {rel}, "
                                         f"fixed-point-free {fpf}")
        need(len(Q["G"]) == len(G0), f"{label}: G acts faithfully")
        need(sp_neg(Q["n"]) in Q["G"], f"{label}: (−1)♯ = −1")
        need({x: bool(fixed_coords(v)) for x, v in g.items()} == fixed0, f"{label}: fixed coordinates")
        sigma, orb = refine(Q, Q["S1"][0])
        types = block_types(sigma, Q["G"])
        need(all(t in ("τ0", "τJ") for t in types), f"{label}: σ″ types {types}")
        need(orb == expect_orbit, f"{label}: |𝓑_{j}| = {orb}")
        stages.append(dict(n=Q["n"], rows=Q["rows"], gens=g, sigma=sigma, orbit=orb, types=types))
        log(f"  {label} E_{j}: n = {Q['n']}, self-dual, {', '.join(names)} ∈ Aut, relations, fixed coordinates as "
            f"on E_0, |G| = {len(Q['G'])}; next σ: {len(sigma)} blocks of types {sorted(set(types))}, |𝓑_{j}| = {orb}")
        cur_rows, cur_n, cur_sigma, cur_gens = Q["rows"], Q["n"], sigma, Q["gens"]
    return stages


# ================================================================ Part 1: §2
def part1(d):
    log("Part 1 (§2): tetracode, Fourier facts, (2.1)")
    T = d["T"]
    TC = Code(T, 4)
    words = codewords(T, 4)
    wts = sorted(pc(A | B) for A, B in words)
    supp3 = {}
    for A, B in words:
        if pc(A | B) == 3:
            supp3[A | B] = supp3.get(A | B, 0) + 1
    need(TC.self_dual() and wts == [0] + [3] * 8 and sorted(supp3.values()) == [2] * 4, "tetracode facts")
    # all self-dual codes of length 4: pairs of vectors
    allv = [list(v) for v in itertools.product(range(3), repeat=4)]
    sd = set()
    for a, b in itertools.combinations(allv, 2):
        C = Code([a, b], 4)
        if C.dim == 2 and C.self_dual():
            sd.add(C.key())
    mono = {Code([list(w) for w in P], 4).key() for P in PLACE}
    need(len(sd) == 8 and sd == mono and Code(T, 4).key() in mono, "8 tetracodes = monomial images of T")
    # (T)
    import cmath
    w = cmath.exp(2j * cmath.pi / 3)
    isq = w - w ** 2
    phi = (0, -1, 1)
    ok_phi = all(abs(sum(phi[x] * w ** (u * x) for x in range(3)) - isq * phi[u]) < 1e-12 for u in range(3))
    ok_iota = all(abs(sum(w ** (b * x) for x in (1, 2)) - (3 * (b == 0) - 1)) < 1e-12 for b in range(3))
    rng = random.Random(1)
    ok_f = True
    for n in (4, 8):
        for _ in range(5):
            u = [rng.randrange(3) for _ in range(n)]
            fh = sum(f_of(x) * w ** (sum(a * b for a, b in zip(u, x)) % 3) for x in itertools.product(range(3), repeat=n))
            ok_f &= abs(fh - 3 ** (n // 2) * f_of(u)) < 1e-6
    need(ok_phi and ok_iota and ok_f, "(T)")
    ok_sign = True
    for _ in range(200):
        n = 12
        g = (tuple(rng.sample(range(n), n)), tuple(rng.choice((1, -1)) for _ in range(n)))
        x = [rng.randrange(3) for _ in range(n)]
        eps = 1
        for v in g[1]:
            eps *= v
        ok_sign &= f_of(sp_apply(g, x)) == eps * f_of(x)
    need(ok_sign, "(2.1)")
    log(f"  T = span{T}: self-dual, weights 0/3, each 3-set the support of two words; exactly {len(sd)} self-dual "
        f"codes of length 4, = the 8 monomial images of T; φ̂ = √−3·φ, ι̂ = 3[b=0] − 1, f̂ = 3^(n/2) f (n = 4, 8); "
        f"f(gx) = ε(g) f(x) on 200 random (g, x)  {stamp()}")


# ================================================================ random codes
def random_self_dual(n, rng, steps=30):
    """Random Kneser walk from a sum of tetracodes (linear algebra only)."""
    T = [[1, 1, 1, 0], [0, 1, 2, 1]]
    rows = []
    for j in range(n // 4):
        for t in T:
            r = [0] * n
            r[4 * j:4 * j + 4] = t
            rows.append(r)
    C = Code(rows, n)
    for _ in range(steps):
        C = random_neighbour(C, rng)
    return C


def random_neighbour(C, rng):
    n = C.n
    while True:
        x = [rng.randrange(3) for _ in range(n)]
        if sum(v * v for v in x) % 3 == 0 and not C.contains(x):
            break
    xv = vec(x)
    vs = [r for _, r in C.piv]
    k = next(t for t, v in enumerate(vs) if vdot(v, xv))
    pv, dpx = vs[k], vdot(vs[k], xv)
    new = []
    for t, v in enumerate(vs):
        if t == k:
            continue
        dv = vdot(v, xv)
        if dv:
            v = vadd(v, vscale(-dv * (1 if dpx == 1 else 2), pv))
        new.append(unvec(v, n))
    C2 = Code(new + [x], n)
    need(C2.self_dual(), "neighbour is self-dual")
    return C2


def all_words(C):
    return codewords(C.basis(), C.n)


# ================================================================ Part 2: §3
def design_sums(W, n):
    full = (1 << n) - 1
    mx = [(A, B) for A, B in W if (A | B) == full]
    M = {}
    for i in range(n):
        for j in range(i, n):
            bi, bj = 1 << i, 1 << j
            tot = 0
            for A, B in mx:
                s = -1 if pc(A) & 1 else 1
                same = bool(A & bi) == bool(A & bj)
                tot += s if same else -s
            M[i, j] = tot
    return M, mx


def part2(d, rng):
    log("Part 2 (§3): signed 2-design, Remark 3.4")
    G12 = d["golay"]
    W = codewords(G12, 12)
    M, mx = design_sums(W, 12)
    idx = index_count(W, 12)[0]
    need(all(M[i, j] == (idx if i == j else 0) for (i, j) in M), "Theorem 3.1 on Golay")
    # Remark 3.4 (1): the 12 maximal words up to sign form a Hadamard matrix
    reps, seen = [], set()
    for A, B in mx:
        if (B, A) not in seen:
            seen.add((A, B))
            reps.append([1 if A >> i & 1 else -1 for i in range(12)])
    had = len(reps) == 12 and all(sum(a * b for a, b in zip(reps[r], reps[s])) == (12 if r == s else 0)
                                  for r in range(12) for s in range(12))
    need(had and idx == 24, "Remark 3.4 (1)")
    # Remark 3.4 (2): four marked coordinates
    vals = set()
    for K in itertools.combinations(range(12), 4):
        lhs = 0
        for A, B in mx:
            s = -1 if pc(A) & 1 else 1
            e = 1
            for k in K:
                e *= 1 if A >> k & 1 else -1
            lhs += s * e
        km = sum(1 << k for k in K)
        out = ((1 << 12) - 1) & ~km
        rhs = 0
        for A, B in W:
            sup = A | B
            if sup & out == out and pc(sup & km) == 1:
                rhs -= -1 if pc(A & out) & 1 else 1
        need(lhs == rhs, f"Remark 3.4 (2) at K = {K}")
        vals.add(lhs)
    need(vals == {8, -8}, f"Golay 4-point sums {vals}")
    nrand = 0
    rand_idx = []
    for n in (12, 12, 24, 24):
        C = random_self_dual(n, rng)
        Wc = all_words(C)
        Mc, _ = design_sums(Wc, n)
        ic = index_count(Wc, n)[0]
        need(all(Mc[i, j] == (ic if i == j else 0) for (i, j) in Mc), "Theorem 3.1 on a random code")
        rand_idx.append(ic)
        for K in [tuple(sorted(rng.sample(range(n), 4))) for _ in range(5)]:
            km = sum(1 << k for k in K)
            out = ((1 << n) - 1) & ~km
            lhs = rhs = 0
            for A, B in Wc:
                sup = A | B
                if sup == (1 << n) - 1:
                    s = -1 if pc(A) & 1 else 1
                    e = 1
                    for k in K:
                        e *= 1 if A >> k & 1 else -1
                    lhs += s * e
                elif sup & out == out and pc(sup & km) == 1:
                    rhs -= -1 if pc(A & out) & 1 else 1
            need(lhs == rhs, "Remark 3.4 (2) on a random code")
        nrand += 1
    log(f"  Golay: Σ s ε_i ε_j = 24 δ_ij; the 12 maximal words up to sign form a Hadamard matrix; the 4-point "
        f"identity Σ s ε_aε_bε_cε_d = −Σ_u Π_(k∉K) φ(u_k) on all 495 K, with values {sorted(vals)}; Theorem 3.1 and "
        f"the 4-point identity (5 K each) on {nrand} random self-dual codes (n = 12, 12, 24, 24; indices {rand_idx})  "
        f"{stamp()}")


# ================================================================ Part 3: §4
def part3(rng):
    log("Part 3 (§4): local identities, main lemma, gadget")
    psi_tab = {(a, b): psi(a, b) for a in range(3) for b in range(3)}
    kap_tab = {(a, b): kappa(a, b) for a in range(3) for b in range(3)}
    need(all(psi_tab[a, b] == (1 if a and not b else (-1 if b and not a else 0)) for a, b in psi_tab), "ψ")
    need(all(kap_tab[a, b] == (2 if bool(a) != bool(b) else (1 if a else 0)) for a, b in kap_tab), "κ")
    SPL = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
    for P in PLACE:
        for u in itertools.product(range(3), repeat=4):
            wt = sum(1 for v in u if v)
            need(sum(psi(u[0], t[0]) * psi(u[1], t[1]) * psi(u[2], t[2]) * psi(u[3], t[3]) for t in P) == LAM[wt],
                 "Lemma 4.1")
            for (p, q), (r, s) in SPL:
                need(sum(LAM[kappa(u[p], t[p]) + kappa(u[q], t[q])] * LAM[kappa(u[r], t[r]) + kappa(u[s], t[s])]
                         for t in P) == LAM[wt], "Lemma 4.2")
    # λ̂ = 9λ (as a function on F_3^4, x ↦ λ(wt x)), in Z[ω] with ω² = −1 − ω: pairs (a, b) = a + bω
    def wpow(e):
        return [(1, 0), (0, 1), (-1, -1)][e % 3]
    ok_hat = True
    for u in itertools.product(range(3), repeat=4):
        a = b = 0
        for x in itertools.product(range(3), repeat=4):
            lam = LAM[sum(1 for v in x if v)]
            if lam:
                c, e = wpow(sum(p * q for p, q in zip(u, x)))
                a, b = a + lam * c, b + lam * e
        ok_hat &= (a, b) == (9 * LAM[sum(1 for v in u if v)], 0)
    need(ok_hat, "λ̂ = 9λ")
    # main lemma by enumeration: self-dual E (n = 12 → 24) and arbitrary E (m = 8, dim 3 → n = 20)
    cases = nonzeroR = 0
    for kind, m, reps in (("self-dual", 12, 5), ("random", 8, 12), ("random", 12, 3)):
        for _ in range(reps):
            if kind == "self-dual":
                E = random_self_dual(m, rng).basis()
            else:
                while True:
                    E = [[rng.randrange(3) for _ in range(m)] for _ in range(3)]
                    if len(rref(E, m)) == 3:
                        break
            coords = list(range(m))
            rng.shuffle(coords)
            blocks = [tuple(coords[:4])]
            RE = R_sigma(codewords(rref(E, m), m), m, [set(b) for b in blocks])
            rows, n, step1, dstar = Q_sigma(E, m, blocks, rng)
            WQ = codewords(rref(rows, n), n)
            if kind == "self-dual":
                need(Code(rows, n).self_dual(), "Lemma 4.5")
            need(R_sigma(WQ, n, []) == RE, "Lemma 4.6: F(Q) = R")
            for r in range(len(step1) + 1):
                for sub in itertools.combinations(step1, r):
                    bl = []
                    for B in sub:
                        bl.append({B[0], B[1], dstar[B[0]], dstar[B[1]]})
                        bl.append({B[2], B[3], dstar[B[2]], dstar[B[3]]})
                    need(R_sigma(WQ, n, bl) == RE, "Lemma 4.6: R_σ″(Q) = R")
            cases += 1
            nonzeroR += RE != 0
    # the gadget (Remark 4.7)
    Q = quad([], 4, [((0, 1), (2, 3))], [sp_neg(4)])
    Gam = Code(Q["rows"], 16)
    gw = codewords(Gam.basis(), 16)

    def H(u):
        v = list(u) + [0] * 4
        hadamard([v], list(Q["star"].items()))
        v += [0] * 8
        hadamard([v], list(Q["dstar"].items()))
        return v
    so = all(vdot(a, b) == 0 for a in [vec(r) for r in Gam.basis()] for b in [vec(r) for r in Gam.basis()])
    need(Gam.dim == 6 and so, "Γ self-orthogonal of dimension 6")
    Us = list(itertools.product(range(3), repeat=4))
    iso = all(sum(a * b for a, b in zip(H(u), H(v))) % 3 == sum(a * b for a, b in zip(u, v)) % 3
              for u in Us for v in Us[::7])
    perp = all(vdot(vec(H(u)), g) == 0 for u in Us for g in [vec(r) for r in Gam.basis()])
    inj = all(not Gam.contains(H(u)) for u in Us if any(u))
    cnt = all(sum(f_of(unvec(vadd(vec(H(u)), g), 16)) for g in gw) == LAM[sum(1 for x in u if x)] for u in Us)
    need(iso and perp and inj and cnt, "Remark 4.7")
    log(f"  ψ, κ as stated; Lemmas 4.1, 4.2 for all 8 tetracodes × 81 u (× 3 splits); λ̂ = 9λ on F_3^4; "
        f"Lemmas 4.5, 4.6 by enumeration on {cases} (E, σ) (5 self-dual of length 12, 15 arbitrary of dimension 3; "
        f"R_σ(E) ≠ 0 on {nonzeroR}), "
        f"random tetracodes and splits, all subsets 𝓑; gadget: Γ self-orthogonal of dimension 6, u ↦ H(u) + Γ an "
        f"isometry of F_3^4 onto Γ^⊥/Γ, coset counts λ(wt u)  {stamp()}")


# ================================================================ Part 4: §5
def partitions3():
    for A in itertools.combinations(range(1, 12), 3):
        A = (0,) + A
        rest = [i for i in range(12) if i not in A]
        for B in itertools.combinations(rest[1:], 3):
            B = (rest[0],) + B
            C = tuple(i for i in rest if i not in B)
            yield (A, B, C)


def part4(d, rng):
    log("Part 4 (§5): Golay, Proposition 5.1, Lemma 5.4, Theorem B")
    G12 = d["golay"]
    C = Code(G12, 12)
    W = codewords(G12, 12)
    enum = {}
    for A, B in W:
        enum[pc(A | B)] = enum.get(pc(A | B), 0) + 1
    need(C.self_dual() and enum == {0: 1, 6: 264, 9: 440, 12: 24}, "Golay weight enumerator")
    hexads = {}
    for A, B in W:
        if pc(A | B) == 6:
            hexads[A | B] = hexads.get(A | B, 0) + 1
    zero9 = {}
    for A, B in W:
        if pc(A | B) == 9:
            z = ((1 << 12) - 1) & ~(A | B)
            zero9[z] = zero9.get(z, 0) + 1
    steiner = all(sum(1 for h in hexads if h & m == m) == 1
                  for m in (sum(1 << i for i in c) for c in itertools.combinations(range(12), 5)))
    four = {sum(1 for h in hexads if h & m == m)
            for m in (sum(1 << i for i in c) for c in itertools.combinations(range(12), 4))}
    ev, od = index_count(W, 12)[1:]
    need(len(hexads) == 132 and set(hexads.values()) == {2} and steiner and four == {4}, "hexads")
    need(len(zero9) == 220 and set(zero9.values()) == {2} and (ev, od) == (24, 0), "weight 9, maximal words")
    s1 = [{0, 1, 2, 3}]
    s2 = [{0, 1, 2, 3}, {4, 5, 6, 8}]
    r1, r2 = R_sigma(W, 12, s1), R_sigma(W, 12, s2)
    need(r1 == 24 and r2 == 24, "Proposition 5.1")
    single = {}
    for b in itertools.combinations(range(12), 4):
        v = R_sigma(W, 12, [set(b)])
        single[v] = single.get(v, 0) + 1
    two = {}
    for a in itertools.combinations(range(12), 4):
        for b in itertools.combinations([i for i in range(12) if i not in a], 4):
            if a < b:
                v = R_sigma(W, 12, [set(a), set(b)])
                two[v] = two.get(v, 0) + 1
    n24 = sum(c for v, c in two.items() if abs(v) == 24)
    need(set(single) <= {24, -24} and sum(single.values()) == 495, f"single blocks {single}")
    need(sum(two.values()) == 17325 and n24 == 13365 and set(two) <= {24, -24, 72, -72}, f"two blocks {two}")
    dist = {}
    for P in partitions3():
        v = R_sigma(W, 12, [set(b) for b in P])
        ms = [sum(1 << i for i in b) for b in P]
        Hs = 0
        for h in hexads:
            for t in range(3):
                if h & ms[t] == ms[t] and all(pc(h & ms[u]) == 1 for u in range(3) if u != t):
                    Hs += 1
        need(v == 8 * Hs - 24, f"Lemma 5.4 at {P}")
        dist[v] = dist.get(v, 0) + 1
    need(dist == {-24: 495, 24: 3960, 72: 1320}, f"5775 partitions {dist}")
    log(f"  G12 as printed: self-dual, weight enumerator {enum}, 132 hexads (a Steiner system S(5,6,12), every 4-set in "
        f"4 hexads), two words ±c per hexad, every 3-set the zero set of two weight-9 words, 24 maximal words, all even; "
        f"R_σ1 = {r1}, R_σ2 = {r2}; single blocks {dict(sorted(single.items()))}; two-block systems "
        f"{dict(sorted(two.items()))} ({n24} with ±24); all 5775 partitions: R = 8H − 24, distribution "
        f"{dict(sorted(dist.items()))}  {stamp()}")
    # Theorem B chains: G = {±1}
    g = {"m": sp_neg(12)}
    out = {}
    for name, sig in (("σ1", [((0, 1), (2, 3))]), ("σ2", [((0, 1), (2, 3)), ((4, 5), (6, 8))])):
        st = run_chain(f"Thm B from {name}", G12, 12, sig, g, 3, [], (), ["τ0"] * len(sig), 1)
        out[name] = st
    lengths = sorted(s["n"] for st in out.values() for s in st)
    need(lengths == [24, 36, 48, 60, 72, 84], f"lengths {lengths}")
    E24 = out["σ1"][0]
    W24 = codewords(Code(E24["rows"], 24).basis(), 24)
    i24 = index_count(W24, 24)[0]
    w3 = sum(1 for A, B in W24 if 0 < pc(A | B) < 6)
    r24 = R_sigma(W24, 24, [set(a + b) for a, b in E24["sigma"]])
    E36 = out["σ2"][0]
    i36 = R_infoset(E36["rows"], 36, [])
    r36 = R_infoset(E36["rows"], 36, [set(a + b) for a, b in E36["sigma"]])
    E48 = out["σ1"][1]
    i48, how48 = F_code(E48["rows"], 48, 24)
    need(i24 == 24 and i36 == 24 and r24 == 24 and r36 == 24 and w3 == 0 and i48 in (24, None),
         f"Theorem B indices {i24}, {i36}, {i48}")
    log(f"  Theorem B: lengths {lengths}; Index(E_24) = {i24} (all 3^12 words), no nonzero words of weight < 6 "
        f"(Remark 5.3 (1)); R_σ″(E_24) = {r24}; Index(E_36) = {i36}, R_σ″(E_36) = {r36} (information sets); "
        f"Index(E_48) = {i48} ({how48})  {stamp()}")


# ================================================================ Part 5: §6
def part5(d):
    log("Part 5 (§6): Lemma 6.2 for all groups of the three types")
    one, neg = sp_id(4), sp_neg(4)
    pairs = (frozenset((0, 1)), frozenset((2, 3)))
    allsp = [(p, s) for p in itertools.permutations(range(4)) for s in itertools.product((1, -1), repeat=4)]
    js = [g for g in allsp if sp_mul(g, g) == neg and all(frozenset(g[0][t] for t in P) == P for P in pairs)]
    tauJ = {frozenset(closure([j])) for j in js}
    tauQ = set()
    for j in js:
        for k in allsp:
            if sp_mul(k, k) == neg and sp_mul(k, j) == sp_mul(neg, sp_mul(j, k)):
                tauQ.add(frozenset(closure([j, k])))
    Y = (0, 1, 2, 3)
    nJ = sorted({len(invariant_tetracodes(Y, H)) for H in tauJ})
    nQ = sorted({len(invariant_tetracodes(Y, H)) for H in tauQ})
    need(all(classify(H, pairs) == "τJ" for H in tauJ) and all(classify(H, pairs) == "τQ" for H in tauQ), "types")
    need(min(nJ) >= 1 and nQ == [4], f"invariant tetracodes {nJ} {nQ}")
    # τ_Q: j, k, jk induce the three fixed-point-free involutions; simply transitive on ±e_p
    invols = {((1, 0, 3, 2)), ((2, 3, 0, 1)), ((3, 2, 1, 0))}
    st = True
    for H in tauQ:
        perms = {g[0] for g in H if g not in (one, neg)}
        st &= perms == invols
        orbit = {(g[0][0], g[1][0]) for g in H}
        st &= len(orbit) == 8
    need(st, "τ_Q permutation facts")
    # the τ_J tetracode of the proof
    a, b, c, e = d["tauJ"]
    jj = ((1, 0, 3, 2), (1, -1, 1, -1))             # j(x_p,x_q,x_r,x_s) = (−x_q, x_p, −x_s, x_r)
    need(sp_apply(jj, [1, 2, 0, 1]) == [(-2) % 3, 1, (-1) % 3, 0], "j as in the proof")
    TJ = Code([a, b], 4)
    need(TJ.self_dual() and sp_apply(jj, a) == c and sp_apply(jj, b) == e and TJ.contains(c) and TJ.contains(e),
         "τ_J tetracode")
    # the τ_Q construction: left ideals {rows in a line} → H-invariant tetracodes
    Mi, Mj = ((0, 1), (2, 0)), ((1, 1), (1, 2))

    def mm(X, Yy):
        return tuple(tuple(sum(X[r][t] * Yy[t][c] for t in range(2)) % 3 for c in range(2)) for r in range(2))
    Mk = mm(Mi, Mj)
    I2 = ((1, 0), (0, 1))
    mor = d["morita"]

    def coords(X):
        v = [0] * 4
        for coef, basis in zip((X[0][0], X[0][1], X[1][0], X[1][1]), mor):
            v = [(p + coef * q) % 3 for p, q in zip(v, basis)]
        return v
    alg_ok = mm(Mi, Mi) == ((2, 0), (0, 2)) and mm(Mj, Mj) == ((2, 0), (0, 2)) and \
        mm(Mj, Mi) == tuple(tuple((-x) % 3 for x in r) for r in Mk)
    # the Morita coordinates invert a + bi + cj + dk ↦ matrix
    inv_ok = True
    for q in itertools.product(range(3), repeat=4):
        X = tuple(tuple((q[0] * I2[r][c] + q[1] * Mi[r][c] + q[2] * Mj[r][c] + q[3] * Mk[r][c]) % 3 for c in range(2))
                  for r in range(2))
        inv_ok &= coords(X) == list(q)
    left_ok = True
    for q in itertools.product(range(3), repeat=4):
        X = ((q[0], q[1]), (q[2], q[3]))
        left_ok &= coords(mm(Mi, X)) == sp_apply(d["blkJ"], coords(X))
        left_ok &= coords(mm(Mj, X)) == sp_apply(d["blkK"], coords(X))
    need(alg_ok and inv_ok and left_ok, "quaternion model, Morita coordinates, J and K = left multiplication")
    ideal_ok = True
    for H in tauQ:
        # θ: i ↦ j_H, j ↦ k_H with j_H preserving the pairs; Θ(1) = e_0
        jH = next(g for g in H if sp_mul(g, g) == neg and all(frozenset(g[0][t] for t in P) == P for P in pairs))
        kH = next(g for g in H if sp_mul(g, g) == neg and sp_mul(g, jH) == sp_mul(neg, sp_mul(jH, g)))
        img = [sp_apply(x, [1, 0, 0, 0]) for x in (one, jH, kH, sp_mul(jH, kH))]
        found = set()
        for line in ((1, 0), (0, 1), (1, 1), (1, 2)):
            Ls = [((line[0], line[1]), (0, 0)), ((0, 0), (line[0], line[1]))]
            vecs = []
            for X in Ls:
                q = coords(X)
                vecs.append([sum(q[t] * img[t][c] for t in range(4)) % 3 for c in range(4)])
            Tc = Code(vecs, 4)
            ideal_ok &= Tc.dim == 2 and Tc.self_dual() and all(Tc.is_aut(g) for g in H)
            found.add(Tc.key())
        ideal_ok &= len(found) == 4
    need(ideal_ok, "left ideals give the 4 invariant tetracodes")
    # non-admissible actions on B = π ⊔ π* = (0, 1 | 2, 3): m ⊕ m* with m² = 1 swapping, or diag(1, −1)
    bad = [((1, 0, 3, 2), (1, 1, 1, 1)), ((1, 0, 3, 2), (-1, -1, -1, -1)), ((0, 1, 2, 3), (1, -1, 1, -1))]
    need(all(not invariant_tetracodes(Y, [g]) for g in bad), "no invariant tetracode for the bad actions")
    log(f"  τ_J groups: {len(tauJ)}, invariant tetracodes per group {nJ}; τ_Q groups: {len(tauQ)}, invariant "
        f"tetracodes per group {nQ}, all four = images of the left ideals under Θ; j, k, jk induce the three "
        f"fixed-point-free involutions, ρ simply transitive on ±e_p; the τ_J tetracode of the proof is j-invariant; "
        f"i² = j² = −1, ji = −ij in M_2(F_3) and the Morita coordinates invert the model; the swaps with square +1 "
        f"and diag(1, −1) on a pair admit no invariant tetracode  {stamp()}")


# ================================================================ Part 6: §7.1
def part6(d):
    log("Part 6 (§7.1): Q₈ on the Golay code")
    G12 = d["golay"]
    C = Code(G12, 12)
    W = codewords(G12, 12)
    Wset = set(W)
    J, K = d["J"], d["K"]
    neg = sp_neg(12)
    need(C.is_aut(J) and C.is_aut(K) and rel_Q8({"J": J, "K": K}, 12), "J, K ∈ Aut, relations")
    Q8 = closure([J, K])
    orbits = {frozenset(g[0][i] for g in Q8) for i in range(12)}
    need(len(Q8) == 8 and orbits == {frozenset(range(4 * t, 4 * t + 4)) for t in range(3)}, "orbits")
    need(all(not fixed_coords(g) for g in Q8 if g not in (sp_id(12), neg)), "free Klein group")
    hexads = sorted({A | B for A, B in W if pc(A | B) == 6})
    hexset = set(hexads)
    # all g ∈ Aut(G12) with g² = −1: fixed-point-free involutive permutations, s_b = −s_a on each 2-cycle
    rowsv = [vec(r) for r in G12]

    def matchings(pts):
        if not pts:
            yield []
            return
        a = pts[0]
        for t in range(1, len(pts)):
            for m in matchings(pts[1:t] + pts[t + 1:]):
                yield [(a, pts[t])] + m
    sq = []
    nmatch = 0
    for m in matchings(list(range(12))):
        nmatch += 1
        p = list(range(12))
        for a, b in m:
            p[a], p[b] = b, a
        good = True
        for h in hexads:
            img = 0
            for i in range(12):
                if h >> i & 1:
                    img |= 1 << p[i]
            if img not in hexset:
                good = False
                break
        if not good:
            continue
        for signs in itertools.product((1, -1), repeat=6):
            s = [0] * 12
            for (a, b), e in zip(m, signs):
                s[a], s[b] = e, -e
            g = (tuple(p), tuple(s))
            if all(vec(sp_apply(g, unvec(r, 12))) in Wset for r in rowsv):
                sq.append(g)
    need(nmatch == 10395 and all(sp_mul(g, g) == neg for g in sq), "matchings")
    groups = set()
    for a in sq:
        for b in sq:
            if sp_mul(b, a) == sp_mul(neg, sp_mul(a, b)):
                groups.add(frozenset(closure([a, b])))
    need(len(groups) == 1320 and frozenset(Q8) in groups, f"{len(groups)} Q₈")
    # one conjugacy class: orbit of ⟨J, K⟩ under conjugation by elements of Aut(G12)
    rng = random.Random(7)
    conj = rng.sample(sq, 12)
    orbit = {frozenset(Q8)}
    frontier = [frozenset(Q8)]
    while frontier:
        new = []
        for S in frontier:
            for c in conj:
                ci = sp_inv(c)
                T = frozenset(sp_mul(c, sp_mul(x, ci)) for x in S)
                if T not in orbit:
                    orbit.add(T)
                    new.append(T)
        frontier = new
    need(orbit == groups, f"conjugacy orbit {len(orbit)}")
    # Proposition 7.1 for all 1320
    r72 = set()
    for S in groups:
        orb = {frozenset(g[0][i] for g in S) for i in range(12)}
        need(len(orb) == 3 and all(len(o) == 4 for o in orb), "three orbits of size 4")
        r72.add(R_sigma(W, 12, [set(o) for o in orb]))
    need(r72 == {72}, f"Proposition 7.1 {r72}")
    # σ_Q
    sQ = d["sigmaQ"]
    types = block_types(sQ, Q8)
    stabs = [sum(1 for g in Q8 if frozenset(g[0][y] for y in a + b) == frozenset(a + b)) for a, b in sQ]
    rQ = R_sigma(W, 12, [set(a + b) for a, b in sQ])
    ms = [sum(1 << i for i in a + b) for a, b in sQ]
    HQ = sum(1 for h in hexads for t in range(3)
             if h & ms[t] == ms[t] and all(pc(h & ms[u]) == 1 for u in range(3) if u != t))
    need(types == ["τQ", "τJ", "τJ"] and stabs == [8, 4, 4] and rQ == -24 and HQ == 0, "σ_Q")
    swapK = frozenset(K[0][y] for y in sQ[1][0] + sQ[1][1]) == frozenset(sQ[2][0] + sQ[2][1])
    need(swapK, "K swaps the τ_J blocks")
    log(f"  J, K as printed: in Aut(G12), J² = K² = −1, KJ = −JK, orbits {{0..3}}, {{4..7}}, {{8..11}}, free Klein "
        f"group; {len(sq)} elements g ∈ Aut(G12) with g² = −1; {len(groups)} subgroups ⟨J, K⟩ ≅ Q₈, one conjugacy "
        f"class (orbit of the printed one under 12 conjugators); R(orbit partition) = 72 for all of them "
        f"(Proposition 7.1); σ_Q: types {types}, stabilisers {stabs}, K swaps the τ_J blocks, R = {rQ}, H = {HQ}  "
        f"{stamp()}")
    st = run_chain("Q-chain", G12, 12, sQ, {"J": J, "K": K}, 2, [rel_Q8], ("J", "K"), ["τQ", "τJ", "τJ"], 2)
    need([s["n"] for s in st] == [48, 96], "Q-chain lengths")
    JK = sp_mul(st[0]["gens"]["J"], st[0]["gens"]["K"])
    need(not fixed_coords(JK), "JK fixed-point-free")
    i48, how = F_code(st[0]["rows"], 48, 24)
    need(i48 in (-24, None), f"Index(Q-chain, 48) = {i48}")
    log(f"  Q-chain: n_j = 48j (j = 1, 2), J♯, K♯, J♯K♯ fixed-point-free; Index(E_48) = {i48} ({how}), so +24 after "
        f"re-signing one coordinate  {stamp()}")


# ================================================================ Part 7: §7.2
def part7(d):
    log("Part 7 (§7.2): E36 with Z/6")
    E = d["E36"]
    n = 36
    need(len(E) == 18 and all(len(r) == 36 for r in E), "E36 shape")
    C = Code(E, n)
    ref = Code(read_rows(os.path.join(CODES, "gjf_ex57_len36.txt")), n)
    need(C.self_dual() and C.key() == ref.key(), "E36 self-dual, = codes/gjf_ex57_len36.txt")
    h = (tuple((i + 12) % n for i in range(n)), (1,) * n)
    need(C.is_aut(h) and rel_h({"h": h}, n) and not fixed_coords(h), "h")
    G = closure([sp_neg(n), h])
    idx = R_infoset(E, n, [])
    Th, dimF = twined_R(E, n, h, [])
    need(len(G) == 6 and idx == 24 and Th == 0 and dimF == 6, "Index, T_h")
    b0, b1, b2 = d["betas"]

    def orbit_blocks(b, split):
        out = []
        for t in range(3):
            img = [(i + 12 * t) % n for i in b]
            out.append(((img[split[0]], img[split[1]]), (img[split[2]], img[split[3]])))
        return out
    sA = orbit_blocks(b0, (0, 1, 2, 3))
    sB = orbit_blocks(b1, (0, 1, 2, 3)) + orbit_blocks(b2, (0, 1, 2, 3))
    for s in (sA, sB):
        need(len({i for a, b in s for i in a + b}) == 4 * len(s), "disjoint blocks")
    tA, tB = block_types(sA, G), block_types(sB, G)
    need(set(tA) == {"τ0"} and set(tB) == {"τ0"}, "types τ0")
    rA = R_infoset(E, n, [set(a + b) for a, b in sA])
    rB = R_infoset(E, n, [set(a + b) for a, b in sB])
    thA, _ = twined_R(E, n, h, [set(a + b) for a, b in sA])
    thB, _ = twined_R(E, n, h, [set(a + b) for a, b in sB])
    need((rA, rB, thA, thB) == (24, 24, 0, 0), f"Proposition 7.3 values {(rA, rB, thA, thB)}")
    log(f"  E36 as printed = codes/gjf_ex57_len36.txt, self-dual; h = shift by 12 ∈ Aut, order 3, no fixed coordinate; "
        f"|⟨−1, h⟩| = 6; Index = {idx}, T_h = {Th} (dim E^h = {dimF}); R_σA = {rA}, R_σB = {rB}, R^h_σA = {thA}, "
        f"R^h_σB = {thB}  {stamp()}")
    # the 13,365 h-stable three-block systems and the 803 good ones
    systems = set()
    for res in itertools.combinations(range(12), 4):
        for off in itertools.product(range(3), repeat=4):
            b = frozenset(r + 12 * o for r, o in zip(res, off))
            systems.add(frozenset(frozenset((i + 12 * t) % n for i in b) for t in range(3)))
    need(len(systems) == 13365, f"{len(systems)} systems")
    Fx = fixed_subcode(E, n, h)
    FW = codewords(Fx, n)
    full = (1 << n) - 1
    adm = []
    rh_of = {}
    for S in systems:
        bl = sorted(S, key=min)
        um = 0
        for b in bl:
            um |= sum(1 << i for i in b)
        sm = full & ~um
        m0 = sum(1 << i for i in bl[0])
        tot = 0
        for A, B in FW:
            if (A | B) & sm != sm:
                continue
            tot += (-1 if pc(A & sm) & 1 else 1) * LAM[pc((A | B) & m0)]
        rh_of[S] = tot
        if tot == 0:
            adm.append(S)
    if RUST:
        def job(S):
            return S, rust_R(E, n, [set(b) for b in S], threads=1)
        with concurrent.futures.ThreadPoolExecutor(4) as ex:
            res = dict(ex.map(job, sorted(systems, key=lambda S: sorted(map(sorted, S)))))
        good = sum(1 for S in adm if abs(res[S]) == 24)
        by_rh = {}
        for S, v in res.items():
            if abs(v) == 24:
                by_rh[rh_of[S]] = by_rh.get(rh_of[S], 0) + 1
        mod48 = all(v % 48 == 24 for v in res.values())
        need(good == 803 and mod48, f"{good} good systems")
        log(f"  {len(systems)} h-stable three-block systems, {len(adm)} with R^h = 0; R_σ ≡ 24 mod 48 on all "
            f"(Proposition 9.4); R = ±24 on {sum(by_rh.values())}, by R^h: {dict(sorted(by_rh.items()))}; good "
            f"(R = ±24, R^h = 0): {good}  {stamp()}")
    else:
        log(f"  {len(systems)} h-stable three-block systems, {len(adm)} with R^h = 0; the count 803 needs rsigma_is "
            f"(skipped)")
    # the Z/6-chains
    gens = {"m": sp_neg(n), "h": h}
    stA = run_chain("Z-chain A", E, n, sA, gens, 2, [rel_h], ("h",), ["τ0"] * 3, 3)
    stB = run_chain("Z-chain B", E, n, sB, gens, 2, [rel_h], ("h",), ["τ0"] * 6, 3)
    need([s["n"] for s in stA] == [72, 144] and [s["n"] for s in stB] == [108, 180], "Z-chain lengths")
    Ts = []
    for s in stA + stB:
        t, dim, how = collapsed_T(s["rows"], s["n"], s["gens"]["h"])
        need(t in (0, None) and dim == s["n"] // 6, f"T_h at {s['n']}")
        Ts.append(f"n = {s['n']}: T_h = {t} ({how}, dim E^h = {dim})")
    i72, how = F_code(stA[0]["rows"], 72, 36)
    need(i72 in (24, None), f"Index(Z-chain A, 72) = {i72}")
    log(f"  Z-chains: {'; '.join(Ts)}; Index(E_72) = {i72} ({how})  {stamp()}")


# ================================================================ Part 8: §7.3
def part8(d):
    log("Part 8 (§7.3): E72 with Q₈ × Z/3")
    U = d["U"]
    need(len(U) == 18 and all(len(r) == 36 for r in U) and len(rref(U, 36)) == 18, "U shape")
    omega = all(sum(u[2 * b] * v[2 * b + 1] - u[2 * b + 1] * v[2 * b] for b in range(18)) % 3 == 0 for u in U for v in U)
    need(omega, "U Lagrangian")
    mor = d["morita"]
    rows = []
    for u in U:
        for slot in (0, 1):
            r = [0] * 72
            for b in range(18):
                x, y = u[2 * b], u[2 * b + 1]
                coef = (x, y, 0, 0) if slot == 0 else (0, 0, x, y)
                for c, basis in zip(coef, mor):
                    for t in range(4):
                        r[4 * b + t] = (r[4 * b + t] + c * basis[t]) % 3
            rows.append(r)
    C = Code(rows, 72)
    ref = Code(read_rows(os.path.join(CODES, "q8z3_seed72.txt")), 72)
    need(C.self_dual() and C.key() == ref.key(), "E72 self-dual, = codes/q8z3_seed72.txt")

    def blockwise(g4):
        p, s = [0] * 72, [0] * 72
        for b in range(18):
            for t in range(4):
                p[4 * b + t], s[4 * b + t] = 4 * b + g4[0][t], g4[1][t]
        return (tuple(p), tuple(s))
    J, K = blockwise(d["blkJ"]), blockwise(d["blkK"])
    hb = [3 * (b // 3) + (b % 3 + 1) % 3 for b in range(18)]
    h = (tuple(4 * hb[i // 4] + i % 4 for i in range(72)), (1,) * 72)
    Uh = [[u[2 * hb.index(b) + t] for b in range(18) for t in (0, 1)] for u in U]
    need(Code(Uh, 36).key() == Code(U, 36).key(), "U is h-invariant")
    gens = {"J": J, "K": K, "h": h}
    need(all(C.is_aut(g) for g in gens.values()) and rel_Q8(gens, 72) and rel_h(gens, 72) and rel_hJK(gens, 72)
         and not fixed_coords(h), "J, K, h")
    G = closure(list(gens.values()))
    sQZ = [((4 * b, 4 * b + 1), (4 * b + 2, 4 * b + 3)) for b in range(6)]
    types = block_types(sQZ, G)
    orbitsQ8 = {frozenset(g[0][i] for g in closure([J, K])) for i in range(72)}
    need(len(G) == 24 and set(types) == {"τQ"} and all(frozenset(a + b) in orbitsQ8 for a, b in sQZ), "σ_QZ")
    th, dimF = twined_R(rows, 72, h, [set(a + b) for a, b in sQZ])
    need(th == 0 and dimF == 12, f"R^h_σQZ = {th}")
    if RUST:
        r = rust_R(rows, 72, [set(a + b) for a, b in sQZ])
        need(r == 24, f"R_σQZ = {r}")
        how = "rsigma_is, 2^36 patterns"
    else:
        r, how = None, "skipped"
    log(f"  U as printed: Lagrangian for Σ(u_2b v_2b+1 − u_2b+1 v_2b), h-invariant; E72 from the Morita recipe: "
        f"self-dual, = codes/q8z3_seed72.txt; J, K (as printed on each block), h ∈ Aut, J² = K² = −1, KJ = −JK, "
        f"h³ = 1, hJ = Jh, hK = Kh, h fixed-point-free, |G| = {len(G)}; σ_QZ: Q₈-orbits, types τ_Q; "
        f"R^h_σQZ = {th} (dim E^h = {dimF}); R_σQZ = {r} ({how})  {stamp()}")
    st = run_chain("QZ-chain", rows, 72, sQZ, gens, 2, [rel_Q8, rel_h, rel_hJK], ("J", "K", "h"), ["τQ"] * 6, 6)
    need([s["n"] for s in st] == [144, 288], "QZ-chain lengths")
    t, dim, how = collapsed_T(st[0]["rows"], 144, st[0]["gens"]["h"])
    need(t in (0, None) and dim == 24, f"T_h at 144 = {t}")
    log(f"  QZ-chain: n_j = 144j (j = 1, 2); T_h(E_144) = {t} ({how}, dim E^h = {dim})  {stamp()}")


# ================================================================ Part 9: §8, §9
def kernel_of(images, n):
    """Basis of {x : Σ x_i images[i] = 0}."""
    return left_kernel(images, n, n)


def part9(rng):
    log("Part 9 (§8, §9): Theorem D; neighbours and congruences")
    # Theorem D at n = 12 (k odd) and n = 24 (k = 2)
    tests = []
    nonzero = attempts = 0
    plan = [12, 12] + [24] * 60
    for n in plan:
        if n == 24 and (nonzero >= 4 and len(tests) >= 7):
            break
        attempts += 1
        base_p = [0] * n
        base_s = [1] * n
        for c in range(n // 4):
            for t in range(4):
                base_p[4 * c + t] = 4 * c + (t + 1) % 4
                base_s[4 * c + t] = -1 if t == 3 else 1
        g0 = (tuple(base_p), tuple(base_s))
        r = (tuple(rng.sample(range(n), n)), tuple(rng.choice((1, -1)) for _ in range(n)))
        g = sp_mul(r, sp_mul(g0, sp_inv(r)))
        g2 = sp_mul(g, g)
        need(sp_mul(g2, g2) == sp_neg(n), "g⁴ = −1")
        E = [[1 if j == i else 0 for j in range(n)] for i in range(n)]

        def poly(v, a, b):          # (g² + a g + b) v
            return [(x + a * y + b * z) % 3 for x, y, z in zip(sp_apply(g2, v), sp_apply(g, v), v)]
        Vp = kernel_of([poly(e, 1, 2) for e in E], n)
        Vm = kernel_of([poly(e, 2, 2) for e in E], n)
        need(len(Vp) == n // 2 and len(Vm) == n // 2, "V± dimensions")
        dF9 = rng.randrange(1, n // 4 + 1) if n == 12 else rng.randrange(2, 5)
        Cp = []
        while len(rref(Cp, n)) < 2 * dF9:
            v = [0] * n
            for b in Vp:
                c = rng.randrange(3)
                v = [(x + c * y) % 3 for x, y in zip(v, b)]
            if len(rref(Cp + [v], n)) > len(rref(Cp, n)):
                Cp += [v, sp_apply(g, v)]
        Cp = rref(Cp, n)

        def annih(sub, V):
            M = [[sum(a * b for a, b in zip(w, c)) % 3 for c in sub] for w in V]
            ker = left_kernel(M, len(V), len(sub)) if sub else [[1 if i == j else 0 for i in range(len(V))]
                                                                  for j in range(len(V))]
            return [[sum(a[t] * V[t][c] for t in range(len(V))) % 3 for c in range(n)] for a in ker]
        Cm = annih(Cp, Vm)
        Cc = Code(Cp + Cm, n)
        need(Cc.self_dual() and Cc.is_aut(g), "C = C+ ⊕ C− self-dual, g-invariant")
        idx = index_count(all_words(Cc), n)[0]
        if n == 12:
            need(idx == 0, "Index = 0 for odd k")
            tests.append((n, idx))
            continue
        need(idx % 48 == 0, f"48 | Index ({idx})")
        if idx == 0 and len(tests) >= 4:
            continue                                 # keep the sample informative: at most a few of index 0
        nonzero += idx != 0
        # the four codes through D = D+ ⊕ C−, D+ an F_9-hyperplane of C+
        # D+ = the F_9-span of the first dF9 − 1 vectors of an F_9-basis of C+ (g-invariant)
        basisF9 = []
        for v in Cp:
            if len(rref(basisF9 + [v], n)) > len(rref(basisF9, n)):
                basisF9 += [v, sp_apply(g, v)]
        Dp = rref(basisF9[:-2], n) if len(basisF9) > 2 else []
        D = Code(Dp + Cm, n)
        need(D.dim == n // 2 - 2 and D.is_aut(g), "D")
        M = [[sum(e[c] * r[c] for c in range(n)) % 3 for r in D.basis()] for e in E]
        Dperp = left_kernel(M, n, D.dim)
        ext = []
        for v in Dperp:
            if len(rref(D.basis() + ext + [v], n)) > len(rref(D.basis() + ext, n)):
                ext.append(v)
        need(len(ext) == 4, "D^⊥/D of dimension 4")
        found = {}
        for co in itertools.product(range(3), repeat=4):
            if not any(co):
                continue
            w = [sum(c * e[t] for c, e in zip(co, ext)) % 3 for t in range(n)]
            if sum(x * x for x in w) % 3:
                continue
            C2 = Code(D.basis() + [w, sp_apply(g2, w)], n)
            if C2.dim == n // 2 and C2.self_dual():
                found[C2.key()] = C2
        need(len(found) == 4 and Cc.key() in found, "four J-invariant self-dual codes through D")
        FD = sum(f_of(unvec(x, n)) for x in all_words(D))
        ids = {k: index_count(all_words(c), n)[0] for k, c in found.items()}
        need(sum(ids.values()) == 12 * FD, "(8.1)")
        C2code = Code(Dp + annih(Dp, Vm), n)
        need(C2code.key() in found, "C_2 = D+ ⊕ D+°")
        others = [k for k in found if k not in (Cc.key(), C2code.key())]
        gC3 = Code([sp_apply(g, r) for r in found[others[0]].basis()], n).key()
        need(len(others) == 2 and gC3 == others[1] and ids[others[0]] == ids[others[1]], "g swaps C_3, C_4")
        need((ids[Cc.key()] + ids[C2code.key()]) % 48 == 0 and ids[others[0]] % 24 == 0 and FD % 8 == 0,
             "induction step")
        tests.append((n, idx, sorted(ids.values()), FD))
    need(nonzero >= 4, "Theorem D sample has codes of nonzero index")
    log(f"  Theorem D on random g-invariant codes (g⁴ = −1; {attempts} sampled): {tests} [(n, Index) for k = 1, and "
        f"(n, Index, indices of the four codes through D, F(D)) for n = 24]; 48 | Index on all sampled codes; each time "
        f"the four J-invariant codes through D are C, C_2 = D+ ⊕ D+° and two codes swapped by g with equal index, "
        f"(8.1) holds, and Index(C) + Index(C_2) ≡ 0 mod 48  {stamp()}")
    # Lemma 9.2 / Remark 9.3 / Proposition 9.4 / Proposition 9.5
    nb = 0
    mod48 = 0
    pairs48 = []
    eo = []
    for n in (12, 12, 24, 24):
        C = random_self_dual(n, rng)
        C2 = random_neighbour(C, rng)
        Cb, C2b = C.basis(), C2.basis()                      # D = C ∩ C′ = C ∩ C′^⊥
        M = [[sum(a * b for a, b in zip(u, v)) % 3 for v in C2b] for u in Cb]
        Db = [[sum(a[t] * Cb[t][c] for t in range(len(Cb))) % 3 for c in range(n)]
              for a in left_kernel(M, len(Cb), len(C2b))]
        WC, WC2, WD = all_words(C), all_words(C2), codewords(rref(Db, n), n)
        need(len(WD) == 3 ** (n // 2 - 1), "neighbours")
        for b in (1, 2):
            coords = list(range(n))
            rng.shuffle(coords)
            blocks = [set(coords[4 * t:4 * t + 4]) for t in range(b)]
            SC, SC2, SD = R_sigma(WC, n, blocks), R_sigma(WC2, n, blocks), R_sigma(WD, n, blocks)
            need(SC + SC2 == 4 * SD, "Lemma 9.2 for w_σ")
            iC = index_count(WC, n)[0]
            need((SC - iC) % 48 == 0, "Proposition 9.4")
            mod48 += 1
            pairs48.append((iC, SC))
        FC, FC2, FD = R_sigma(WC, n, []), R_sigma(WC2, n, []), R_sigma(WD, n, [])
        need(FC + FC2 == 4 * FD and FD % 2 == 0, "Remark 9.3")
        for W in (WC, WC2):
            i, e, o = index_count(W, n)
            need(e % 8 == 0 and o % 8 == 0, "Proposition 9.5")
            eo.append((e, o))
        nb += 1
    log(f"  on {nb} random neighbour pairs (n = 12, 12, 24, 24): S(C) + S(C′) = 4S(D) for Λ = f and Λ = w_σ "
        f"(Lemma 9.2, Remark 9.3); R_σ ≡ Index mod 48 on {mod48} (C, σ) (Proposition 9.4; (Index, R_σ) = {pairs48}); "
        f"(#even, #odd) = {eo}, "
        f"all divisible by 8 (Proposition 9.5)  {stamp()}")


# ================================================================ main
def main():
    LOG.clear()
    log(f"conj14_paper_check.py: claims of paper/conj14.tex; Rust rsigma_is: "
        f"{'used' if RUST else ('skipped (--fast)' if FAST else 'not built, skipped')}")
    rng = random.Random(2026)
    d = parse_tex(open(TEX).read())
    status = "all checks passed"
    try:
        part1(d)
        part2(d, rng)
        part3(rng)
        part4(d, rng)
        part5(d)
        part6(d)
        part7(d)
        part8(d)
        part9(rng)
    except AssertionError as e:
        status = f"FAILED: {e}"
    log(status + f" (total {time.time() - T0:.0f}s)")
    with open(os.path.join(HERE, "conj14_paper_check.log"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")
    if status.startswith("FAILED"):
        sys.exit(1)


if __name__ == "__main__":
    main()
