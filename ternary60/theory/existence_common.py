"""Shared helpers for the existence-half experiments (ternary-code-index.md §5).

Stdlib only. Vectors over F_3 are lists/tuples of ints in {0,1,2}.
f(x) = prod phi(x_i), phi = (0, -1, +1), so Index(C) = sum_{x in C} f(x) (GJF sign).
The Rust binary ../target/release/ternary60 is used for indices at n >= 24.
"""
import itertools, os, re, subprocess, tempfile, cmath

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "..", "target", "release", "ternary60")
PHI = (0, -1, 1)
OMEGA = cmath.exp(2j * cmath.pi / 3)

GOLAY = [[1,0,0,0,0,0,0,1,1,1,1,1],[0,1,0,0,0,0,2,0,1,2,2,1],[0,0,1,0,0,0,2,1,0,1,2,2],
         [0,0,0,1,0,0,2,2,1,0,1,2],[0,0,0,0,1,0,2,2,2,1,0,1],[0,0,0,0,0,1,2,1,2,2,1,0]]
TETRA = [[1,1,1,0],[0,1,2,1]]
# code2 = GJF's second length-12 code: four E_3 = <111> blocks glued by a tetracode ("4E_3^+")
CODE2 = [[1,1,1,0,0,0,0,0,0,0,0,0],[0,0,0,1,1,1,0,0,0,0,0,0],[0,0,0,0,0,0,1,1,1,0,0,0],
         [0,0,0,0,0,0,0,0,0,1,1,1],[0,1,2,0,1,2,0,2,1,0,0,0],[0,0,0,0,1,2,0,1,2,0,2,1]]


def f(x):
    p = 1
    for a in x:
        p *= PHI[a]
        if p == 0:
            return 0
    return p


def dot(a, b):
    return sum(x * y for x, y in zip(a, b)) % 3


def add(a, b, s=1):
    return tuple((x + s * y) % 3 for x, y in zip(a, b))


def span(B, n):
    return [tuple(sum(c * b[j] for c, b in zip(cs, B)) % 3 for j in range(n))
            for cs in itertools.product(range(3), repeat=len(B))]


def rref(rows):
    rows = [list(r) for r in rows]
    out = []
    for c in range(len(rows[0])):
        p = next((i for i, r in enumerate(rows) if r[c]), None)
        if p is None:
            continue
        r = rows.pop(p)
        inv = 1 if r[c] == 1 else 2
        r = [(x * inv) % 3 for x in r]
        rows = [[(x - y * s[c]) % 3 for x, y in zip(s, r)] for s in rows]
        out = [[(x - y * s[c]) % 3 for x, y in zip(s, r)] for s in out]
        out.append(r)
    return out


def inspan(B, v):
    return len(rref(B + [list(v)])) == len(rref(B))


def dsum(blocks):
    n = sum(len(b[0]) for b in blocks)
    rows, off = [], 0
    for b in blocks:
        m = len(b[0])
        for r in b:
            rows.append([0] * off + list(r) + [0] * (n - off - m))
        off += m
    return rows


def nbr(B, x):
    """Kneser 3-neighbour C' = (C ∩ x^⊥) + <x> for isotropic x ∉ C."""
    s = [dot(r, x) for r in B]
    i = next(i for i, t in enumerate(s) if t)
    piv, sp = B[i], s[i]
    D = []
    for j, r in enumerate(B):
        if j != i:
            c = (s[j] * (1 if sp == 1 else 2)) % 3
            D.append([(a - c * b) % 3 for a, b in zip(r, piv)])
    return rref(D + [list(x)])


def rand_iso(B, n, rng):
    while True:
        x = [rng.randrange(3) for _ in range(n)]
        if any(x) and dot(x, x) == 0 and not inspan(B, x):
            return x


_TMPDIR = tempfile.mkdtemp(prefix="ternary_existence_")


def rust_index(B, tag="c"):
    fn = os.path.join(_TMPDIR, tag + ".txt")
    with open(fn, "w") as fh:
        fh.write("\n".join("".join(map(str, r)) for r in B) + "\n")
    out = subprocess.run([BIN, "index", fn], capture_output=True, text=True).stdout
    return int(re.search(r" I=(-?\d+)", out).group(1))


def brute_index(B, n):
    return sum(f(x) for x in span(B, n))


def coset_reps(C, n):
    seen, reps = set(), []
    for y in itertools.product(range(3), repeat=n):
        if y in seen:
            continue
        seen.update(add(y, c) for c in C)
        reps.append(y)
    return reps


def twisted(C, y, v):
    """G_C(y, v) = sum_{x in y+C} f(x) ω^{v·x}  (twisted by y, twined by v)."""
    tot = 0
    for c in C:
        x = add(y, c)
        fx = f(x)
        if fx:
            tot += fx * OMEGA ** dot(v, x)
    return tot
