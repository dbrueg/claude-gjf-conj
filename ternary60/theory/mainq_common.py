"""Shared helpers for the Main-Question experiments (notes/main-question.md).

Stdlib only, except `aut_gens`, which calls nauty's `dreadnaut` (path in $DREADNAUT, or `dreadnaut`
on $PATH) to get generators of the monomial automorphism group. Everything that nauty returns is
re-checked here (each generator is verified to preserve the code).

Monomial maps g ∈ 2^n:S_n are pairs (p, s): g(e_i) = s_i e_{p(i)}, i.e. (g x)_{p(i)} = s_i x_i,
with s_i ∈ {1, −1}. Vectors over F_3 are tuples in {0,1,2}. Bit-sliced vectors are pairs of ints
(a, b) = (positions with value 1, positions with value 2).
"""
import itertools, os, shutil, subprocess, tempfile
from existence_common import rref, span, f, PHI

# ------------------------------------------------------------------ codes


def read_code(path):
    with open(path) as fh:
        return [[int(ch) for ch in line.strip()] for line in fh if line.strip()]


def write_code(path, rows):
    with open(path, "w") as fh:
        fh.write("\n".join("".join(map(str, r)) for r in rows) + "\n")


def write_gens(path, gens):
    """Signed permutations {name: (perm, signs)} in the space-separated .gens.txt format."""
    with open(path, "w") as fh:
        for name, (p, s) in gens.items():
            fh.write(f"{name} perm: " + " ".join(map(str, p)) + "\n")
            fh.write(f"{name} sign: " + " ".join(map(str, s)) + "\n")


def read_gens(path):
    """Inverse of write_gens: {name: (perm, signs)}, in file order."""
    d, out = {}, {}
    with open(path) as fh:
        for ln in fh:
            if ln.strip():
                key, vals = ln.split(":")
                d[key.strip()] = tuple(int(x) for x in vals.split())
    for key in d:
        name, kind = key.rsplit(" ", 1)
        if kind == "perm":
            out[name] = (d[key], d[f"{name} sign"])
    return out


def to_bits(v):
    a = b = 0
    for i, x in enumerate(v):
        if x == 1:
            a |= 1 << i
        elif x == 2:
            b |= 1 << i
    return a, b


def from_bits(ab, n):
    a, b = ab
    return tuple(1 if (a >> i) & 1 else 2 if (b >> i) & 1 else 0 for i in range(n))


def badd(x, y):
    t = (x[0] | y[1]) ^ (x[1] | y[0])
    return ((x[1] | y[1]) ^ t, (x[0] | y[0]) ^ t)


def bneg(x):
    return (x[1], x[0])


def systematic(rows, n, order):
    """RREF with pivots taken greedily in the given column order. Returns (rows, pivots)."""
    perm_rows = [[r[c] for c in order] for r in rows]
    R = rref(perm_rows)
    piv = [next(j for j in range(n) if r[j]) for r in R]
    back = [[0] * n for _ in R]
    for k, r in enumerate(R):
        for j in range(n):
            back[k][order[j]] = r[j]
    return back, [order[j] for j in piv]


def low_weight_words(rows, n, wmax):
    """All codewords of weight 1..wmax (both signs), for a self-dual code (two complementary
    information sets: a word of weight w has weight ≤ w/2 on one of them)."""
    out = set()
    _, piv = systematic(rows, n, list(range(n)))
    rest = [j for j in range(n) if j not in piv]
    for order in (piv + rest, rest + piv):
        R, P = systematic(rows, n, order)
        assert len(P) == n // 2, "not an information set"
        B = [to_bits(r) for r in R]
        t = wmax // 2
        for j in range(1, t + 1):
            for idx in itertools.combinations(range(len(B)), j):
                for signs in itertools.product((0, 1), repeat=j):
                    x = (0, 0)
                    for i, sg in zip(idx, signs):
                        x = badd(x, bneg(B[i]) if sg else B[i])
                    w = bin(x[0] | x[1]).count("1")
                    if w <= wmax:
                        out.add(x)
    return sorted(out)


def rust_words(rows, n, wmax):
    """Same as low_weight_words, computed by `ternary60 words` (much faster)."""
    from existence_common import BIN, _TMPDIR
    fn = os.path.join(_TMPDIR, f"words{n}.txt")
    write_code(fn, rows)
    out = subprocess.run([BIN, "words", fn, str(wmax)], capture_output=True, text=True, check=True).stdout
    return sorted(to_bits([int(c) for c in line]) for line in out.split())


def bits_rank(ws, stop=None):
    """Rank over F_3 of bit-sliced vectors (early exit at `stop`)."""
    basis = {}                       # pivot bit -> vector with that lowest set coordinate = 1
    for x in ws:
        while x[0] | x[1]:
            low = (x[0] | x[1]) & -(x[0] | x[1])
            if x[1] & low:
                x = bneg(x)
            if low not in basis:
                basis[low] = x
                break
            x = badd(x, bneg(basis[low]))
        if stop and len(basis) >= stop:
            break
    return len(basis)


def weight(x):
    return bin(x[0] | x[1]).count("1")


# ------------------------------------------------------------------ monomial maps


def mono_apply(g, v):
    p, s = g
    y = [0] * len(p)
    for i, x in enumerate(v):
        if x:
            y[p[i]] = x if s[i] == 1 else 3 - x
    return tuple(y)


def mono_mul(g, h):
    """g∘h (first h, then g)."""
    pg, sg = g
    ph, sh = h
    return (tuple(pg[ph[i]] for i in range(len(ph))), tuple(sh[i] * sg[ph[i]] for i in range(len(ph))))


def mono_id(n):
    return (tuple(range(n)), (1,) * n)


def mono_neg(n):
    return (tuple(range(n)), (-1,) * n)


def mono_pow(g, k):
    n = len(g[0])
    r, b = mono_id(n), g
    while k:
        if k & 1:
            r = mono_mul(b, r)
        b = mono_mul(b, b)
        k >>= 1
    return r


def mono_order(g):
    n = len(g[0]); e = mono_id(n); x = g; k = 1
    while x != e:
        x = mono_mul(g, x); k += 1
    return k


def cycle_type(p):
    seen, out = set(), []
    for i in range(len(p)):
        if i in seen:
            continue
        L, j = 0, i
        while j not in seen:
            seen.add(j); j = p[j]; L += 1
        out.append(L)
    return tuple(sorted(out, reverse=True))


def is_aut(g, rows, n):
    B = rref(rows)
    return all(len(rref(B + [list(mono_apply(g, r))])) == len(B) for r in rows)


# ------------------------------------------------------------------ nauty


def dreadnaut_path():
    p = os.environ.get("DREADNAUT") or shutil.which("dreadnaut")
    if not p:
        raise RuntimeError("dreadnaut not found: set $DREADNAUT (nauty 2.8, `make dreadnaut`)")
    return p


def aut_gens(rows, n, wmax=None, traces=True):
    """Generators of Aut(C) ⊂ 2^n:S_n and |Aut(C)|, via the graph on the ± coordinate vertices and
    the codewords of weight ≤ wmax (default: the smallest wmax whose words span C).
    Returns (gens, order_string_from_nauty, wmax)."""
    B = rref(rows)
    ws = None
    for w in ([wmax] if wmax else range(3, n + 1, 3)):
        ws = rust_words(rows, n, w) if n > 24 else low_weight_words(rows, n, w)
        if ws and bits_rank(ws, len(B)) == len(B):
            wmax = w
            break
    V = 2 * n + len(ws)
    adj = [set() for _ in range(V)]
    for i in range(n):
        adj[2 * i].add(2 * i + 1); adj[2 * i + 1].add(2 * i)
    for k, x in enumerate(ws):
        u = 2 * n + k
        for i in range(n):
            if (x[0] >> i) & 1:
                adj[u].add(2 * i); adj[2 * i].add(u)
            elif (x[1] >> i) & 1:
                adj[u].add(2 * i + 1); adj[2 * i + 1].add(u)
    lines = (["At"] if traces else []) + [f"n={V} g"]
    for u in range(V):
        nb = " ".join(str(v) for v in sorted(adj[u]) if v > u)
        lines.append(f"{u}: {nb};")
    lines[-1] = lines[-1][:-1] + "."
    lines.append(f"f=[0:{2 * n - 1}|{2 * n}:{V - 1}]")
    lines.append("x")
    out = subprocess.run([dreadnaut_path()], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout
    gens, cur = [], ""
    grpsize = None
    for line in out.splitlines():
        s = line.strip()
        if line.startswith("Gen"):            # Traces: "Gen #k: (..)" or "Gen(A) #k: (..)"
            line = s = line.split(":", 1)[1].strip()
        if line.startswith("("):              # a new generator starts in column 0
            if cur:
                gens.append(cur)
            cur = s
        elif cur and line[:1] == " " and s[:1] in "(0123456789":   # indented continuation
            cur += " " + s
        elif cur:
            gens.append(cur); cur = ""
        if "grpsize=" in s:
            grpsize = s.split("grpsize=")[1].split(";")[0]
    if cur:
        gens.append(cur)
    mono = []
    for gtxt in gens:
        img = list(range(V))
        for cyc in gtxt.replace(")", "").split("("):
            c = [int(t) for t in cyc.split()]
            for a, b2 in zip(c, c[1:] + c[:1]):
                img[a] = b2
        p = tuple(img[2 * i] // 2 for i in range(n))
        s = tuple(1 if img[2 * i] % 2 == 0 else -1 for i in range(n))
        g = (p, s)
        assert is_aut(g, rows, n), "nauty generator is not a code automorphism"
        mono.append(g)
    return mono, grpsize, wmax


def closure(gens, n, limit=10 ** 6):
    e = mono_id(n)
    seen = {e}
    frontier = [e]
    while frontier:
        nf = []
        for x in frontier:
            for g in gens:
                y = mono_mul(g, x)
                if y not in seen:
                    seen.add(y); nf.append(y)
                    if len(seen) > limit:
                        raise RuntimeError("group too large for closure")
        frontier = nf
    return seen


# ------------------------------------------------------------------ fixed codes, twined counts


def fixed_code(rows, n, g):
    """Basis of C^g = {x ∈ C : g x = x}, by linear algebra on coefficient vectors."""
    B = rref(rows)
    k = len(B)
    # x = Σ c_j B_j; g x − x = Σ c_j (g B_j − B_j) = 0. Solve for c over F_3.
    D = [[(a - b) % 3 for a, b in zip(mono_apply(g, r), r)] for r in B]
    # columns = coordinates; find null space of the k×n matrix D^T acting on c
    M = [[D[j][i] for j in range(k)] for i in range(n)]   # n×k, M c = 0
    R = rref(M) if any(any(r) for r in M) else []
    piv = [next(j for j in range(k) if r[j]) for r in R]
    free = [j for j in range(k) if j not in piv]
    basis = []
    for fj in free:
        c = [0] * k; c[fj] = 1
        for r, pj in zip(R, piv):
            c[pj] = (-r[fj]) % 3
        basis.append([sum(c[j] * B[j][i] for j in range(k)) % 3 for i in range(n)])
    return basis


def signed_count(rows, n):
    """Σ_{x ∈ span(rows)} f(x) by plain enumeration (use only for small dimension)."""
    if not rows:
        return 0 if n else 1
    return sum(f(x) for x in span(rref(rows), n))


def twined_count(rows, n, h):
    """T_h = Σ_{x ∈ C, hx = x} f(x): the signed count of h-fixed maximal codewords."""
    return signed_count(fixed_code(rows, n, h), n)


def orbit_sum_code(rows, n, h):
    """π(C) for h of order 3: coordinates = fixed points of h and the 3-cycles of h (with h a pure
    permutation on each 3-cycle after the sign normalisation below); π(x) = (x on fixed points, sums
    over 3-cycles). Returns (basis rows of π(C), N)."""
    p, s = h
    seen, cols = set(), []
    for i in range(n):
        if i in seen:
            continue
        cyc = [i]
        while p[cyc[-1]] != i:
            cyc.append(p[cyc[-1]])
        seen.update(cyc)
        cols.append(cyc)
    # normalise signs: choose d with d_{p(i)} = s_i d_i along each cycle (possible since the cycle
    # product of signs is +1 for an element of order 3), then x ↦ D x conjugates h to a permutation.
    d = [0] * n
    for cyc in cols:
        d[cyc[0]] = 1
        for a, b in zip(cyc, cyc[1:]):
            d[b] = s[a] * d[a]
    out = []
    for r in rref(rows):
        y = [(d[i] * r[i]) % 3 for i in range(n)]
        out.append([sum(y[i] for i in cyc) % 3 for cyc in cols])
    B = rref(out) if any(any(v) for v in out) else []
    return B, len(cols), d


def twined_count_trace(rows, n, h):
    """T_h via the trace code: T_h = ε · 3^{N/2 − dim π(C)} · i^N · Ind(π(C)) (notes §3.1), where
    ε = Π_i d_i^{...} is the global sign from the sign normalisation of h (±1)."""
    B, N, d = orbit_sum_code(rows, n, h)
    k = len(B)
    ind = signed_count(B, N) if k else (1 if N == 0 else 0)
    val = (1j ** N) * 3 ** (N / 2 - k) * ind
    eps = 1
    for x in d:
        eps *= x
    return eps * val


def rust_R(rows, blocks, tag="rs"):
    """R_σ(span rows) by full enumeration in Rust (`ternary60 rsigma`), sign-exact; blocks = [] gives
    Σ_{x ∈ C} f(x), i.e. the index for a self-dual C or the signed count of any linear code."""
    from existence_common import BIN, _TMPDIR
    fn = os.path.join(_TMPDIR, tag + ".txt")
    write_code(fn, rows)
    spec = ";".join(",".join(map(str, b)) for b in blocks) if blocks else "-"
    out = subprocess.run([BIN, "rsigma", fn, spec], capture_output=True, text=True, check=True).stdout
    return int(out.split("=")[1])


def twined_count_rust(rows, n, h):
    """T_h via the Rust enumerator on the fixed code (for fixed codes of dimension up to ~26)."""
    Fx = fixed_code(rows, n, h)
    return rust_R(Fx, [], "fix") if Fx else 0
