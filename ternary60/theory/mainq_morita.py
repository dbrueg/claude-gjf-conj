"""Q₈-invariant ternary codes in Morita form (notes/main-question.md §9).

Q₈ = <J, K> acting on n = 4r coordinates with J² = K² = −1 has r orbits of size 4; on each orbit the
action is the left regular action of the quaternion algebra A = F₃⟨i, j⟩ ≅ M₂(F₃) in the coordinates
(a, b, c, d) of a + bi + cj + dk (after a monomial change of coordinates), and the dot product is the
norm form. Hence every Q₈-invariant code is C = F₃² ⊗ U = {2×2r matrices with both rows in U} for a
subspace U ⊂ F₃^{2r} (block b = coordinates 2b, 2b+1), and C is self-dual iff U is Lagrangian for
Ω = ⊕_b ω_b, ω(x, y) = x₀y₁ − x₁y₀.

Here: the coordinate map M₂(F₃) → F₃⁴, random h-invariant Lagrangians (h = the block permutation
(3s+t) ↦ (3s+t+1 mod 3)), free lifts of a Lagrangian Ū over R = F₃[u]/u³ (u = h − 1), and the Rust
enumerator `ternary60 sl2words` (normalised SL₂-words and R_σ for systems of Q₈-orbit blocks).
Stdlib only.
"""
import itertools, os, subprocess
from existence_common import rref, f, BIN, _TMPDIR

# ------------------------------------------------------------------ quaternions as 2x2 matrices
I2 = ((1, 0), (0, 1))
QI = ((0, 1), (2, 0))      # QI² = QJ² = −1, QI QJ = −QJ QI
QJ = ((1, 1), (1, 2))


def mm(A, B):
    return tuple(tuple(sum(A[r][t] * B[t][c] for t in range(2)) % 3 for c in range(2)) for r in range(2))


QK = mm(QI, QJ)
QBASIS = (I2, QI, QJ, QK)


def det2(X):
    return (X[0][0] * X[1][1] - X[0][1] * X[1][0]) % 3


def coeffs(X):
    """Quaternion coordinates (a, b, c, d) of X: orthonormal basis QBASIS for <X, Y> = −tr(X adj Y)."""
    def adj(Y):
        return ((Y[1][1], (-Y[0][1]) % 3), ((-Y[1][0]) % 3, Y[0][0]))
    return tuple((-(mm(X, adj(E))[0][0] + mm(X, adj(E))[1][1])) % 3 for E in QBASIS)


ALL_M2 = [((a, b), (c, d)) for a, b, c, d in itertools.product(range(3), repeat=4)]
SL2 = [X for X in ALL_M2 if det2(X) == 1]
Q8M = [X for X in SL2 if sum(1 for x in coeffs(X) if x) == 1]


def psi(X):
    """ψ: SL₂(F₃) → Z/3 with f₄(X) = φ(ψ(X)) (f₄ = product of φ over the quaternion coordinates)."""
    v = f(coeffs(X))
    return 0 if v == 0 else (1 if v == -1 else 2)


def psi_table():
    """The 81-entry table of ternary60 PSI_TAB (index p0 + 3p1 + 9q0 + 27q1; 255 = det ≠ 1)."""
    out = []
    for idx in range(81):
        X = ((idx % 3, idx // 3 % 3), (idx // 9 % 3, idx // 27))
        out.append(psi(X) if det2(X) == 1 else 255)
    return out


# ------------------------------------------------------------------ U ↔ C
def omega(x, y):
    return sum(x[2 * b] * y[2 * b + 1] - x[2 * b + 1] * y[2 * b] for b in range(len(x) // 2)) % 3


def code_from_U(U, r):
    """Rows of C = F₃² ⊗ U in quaternion coordinates (block b = coordinates 4b..4b+3)."""
    rows = []
    for u in U:
        for top in (True, False):
            v = []
            for b in range(r):
                row = (u[2 * b], u[2 * b + 1])
                v.extend(coeffs((row, (0, 0)) if top else ((0, 0), row)))
            rows.append(v)
    return rows


def q8_gens(r):
    """J, K (left multiplication by QI, QJ on every block) as monomial maps (p, s) on 4r coordinates."""
    def left(Q):
        p, s = [0] * (4 * r), [1] * (4 * r)
        for a in range(4):
            y = coeffs(mm(Q, QBASIS[a]))           # Q · (basis a) = ± basis p(a)
            t = next(i for i in range(4) if y[i])
            for b in range(r):
                p[4 * b + a] = 4 * b + t; s[4 * b + a] = 1 if y[t] == 1 else -1
        return tuple(p), tuple(s)
    return left(QI), left(QJ)


def h_blocks(k):
    """h on the 3k blocks: 3s + t ↦ 3s + (t + 1 mod 3)."""
    return [3 * (b // 3) + (b % 3 + 1) % 3 for b in range(3 * k)]


def h_gen(k):
    """h as a monomial map on the 12k coordinates of code_from_U."""
    hb = h_blocks(k)
    return tuple(4 * hb[i // 4] + i % 4 for i in range(12 * k)), (1,) * (12 * k)


def happly(hb, x):
    y = [0] * len(x)
    for b, c in enumerate(hb):
        y[2 * c], y[2 * c + 1] = x[2 * b], x[2 * b + 1]
    return y


def nullspace_form(S, n, form):
    if not S:
        return [[int(i == j) for i in range(n)] for j in range(n)]
    R = rref([[form(s, [int(i == j) for i in range(n)]) for j in range(n)] for s in S])
    piv = [next(j for j in range(n) if r_[j]) for r_ in R]
    out = []
    for fj in (j for j in range(n) if j not in piv):
        c = [0] * n; c[fj] = 1
        for r_, pj in zip(R, piv):
            c[pj] = (-r_[fj]) % 3
        out.append(c)
    return out


def rand_U(k, rng, tries=500):
    """A random h-invariant Lagrangian U ⊂ F₃^{6k} (None if the greedy extension gets stuck)."""
    r = 3 * k; n = 2 * r; hb = h_blocks(k)
    S = []
    while len(S) < r:
        perp = nullspace_form(S, n, omega)
        for _ in range(tries):
            c = [rng.randrange(3) for _ in perp]
            w = [sum(a * b[i] for a, b in zip(c, perp)) % 3 for i in range(n)]
            if not any(w):
                continue
            orb = [w, happly(hb, w), happly(hb, happly(hb, w))]
            if all(omega(a, b) == 0 for a in orb for b in orb):
                T = rref(S + orb)
                if len(T) > len(S):
                    S = T; break
        else:
            return None
    return S


def fixed_U(U, hb):
    """Basis of U^h."""
    n, k = len(U[0]), len(U)
    D = [[(a - b) % 3 for a, b in zip(happly(hb, u), u)] for u in U]
    M = [[D[j][i] for j in range(k)] for i in range(n)]
    R = rref(M) if any(any(x) for x in M) else []
    piv = [next(j for j in range(k) if r_[j]) for r_ in R]
    out = []
    for fj in (j for j in range(k) if j not in piv):
        c = [0] * k; c[fj] = 1
        for r_, pj in zip(R, piv):
            c[pj] = (-r_[fj]) % 3
        out.append([sum(c[j] * U[j][i] for j in range(k)) % 3 for i in range(n)])
    return out


def collapse(Uh, k):
    """π(U^h) ⊂ F₃^{2k}: the block (s, 0) components of the h-fixed vectors."""
    return rref([[u[2 * (3 * s) + e] for s in range(k) for e in range(2)] for u in Uh]) if Uh else []


# ------------------------------------------------------------------ free lifts over R = F3[u]/u^3
def lagrangians(k):
    """All Lagrangians of F₃^{2k} (k ≤ 2), as rref bases."""
    n = 2 * k
    vecs = [list(v) for v in itertools.product(range(3), repeat=n) if any(v)]
    out = set()

    def rec(B):
        if len(B) == k:
            out.add(tuple(map(tuple, rref(B)))); return
        for v in vecs:
            if all(omega(v, b) == 0 for b in B) and len(rref(B + [v])) > len(B):
                rec(B + [v])
    rec([])
    return [list(map(list, L)) for L in sorted(out)]


def complement(E, k):
    """f₁..f_k with ω(e_i, f_j) = δ_ij and span(f) Lagrangian."""
    F = []
    for j in range(k):
        for v in itertools.product(range(3), repeat=2 * k):
            if all(omega(E[i], v) == int(i == j) for i in range(k)) and all(omega(g, v) == 0 for g in F):
                F.append(list(v)); break
    return F


def lift(E, F, A1, S, k):
    """F₃-basis (block coordinates, length 6k) of U = R·{e_i + u(A1 f)_i + u²((A1+S) f)_i}; A1 skew, S
    symmetric k×k. x = x₀ + x₁u + x₂u² has t-components x₀ − x₁ + x₂, x₁ + x₂, x₂."""
    n = 2 * k
    A2 = [[(A1[i][j] + S[i][j]) % 3 for j in range(k)] for i in range(k)]
    comb = lambda A, i: [sum(A[i][j] * F[j][c] for j in range(k)) % 3 for c in range(n)]

    def blocks(x0, x1, x2):
        xt = [[(a - b + c) % 3 for a, b, c in zip(x0, x1, x2)], [(b + c) % 3 for b, c in zip(x1, x2)], list(x2)]
        out = [0] * (3 * n)
        for s in range(k):
            for j in range(3):
                out[2 * (3 * s + j)], out[2 * (3 * s + j) + 1] = xt[j][2 * s], xt[j][2 * s + 1]
        return out
    z = [0] * n
    rows = []
    for i in range(k):
        rows += [blocks(E[i], comb(A1, i), comb(A2, i)), blocks(z, E[i], comb(A1, i)), blocks(z, z, E[i])]
    return rows


def skews(k):
    idx = [(i, j) for i in range(k) for j in range(i + 1, k)]
    for vals in itertools.product(range(3), repeat=len(idx)):
        A = [[0] * k for _ in range(k)]
        for (i, j), v in zip(idx, vals):
            A[i][j], A[j][i] = v, (-v) % 3
        yield A


def syms(k):
    idx = [(i, j) for i in range(k) for j in range(i, k)]
    for vals in itertools.product(range(3), repeat=len(idx)):
        A = [[0] * k for _ in range(k)]
        for (i, j), v in zip(idx, vals):
            A[i][j] = A[j][i] = v
        yield A


# ------------------------------------------------------------------ Rust enumerator
def rsys(U, systems, tag="ms"):
    """[R_σ(F₃² ⊗ U) for σ in systems] (σ = list of Q₈-orbit blocks; [] gives the index), sign-exact,
    via `ternary60 sl2words`: R_σ = 8 Σ_{good planes} Σ_{s∈F₃} Π_b ρ_b(ψ_b + s), ρ = (−2, 1, 1) on σ and
    φ = (0, −1, 1) off σ. U must be Lagrangian of dimension r."""
    fn = os.path.join(_TMPDIR, tag + ".u"); sf = os.path.join(_TMPDIR, tag + ".sys")
    with open(fn, "w") as fh:
        fh.write("\n".join("".join(map(str, r_)) for r_ in U) + "\n")
    with open(sf, "w") as fh:
        fh.write("\n".join(",".join(map(str, s)) if s else "-" for s in systems) + "\n")
    out = subprocess.run([BIN, "sl2words", fn, "0", sf], capture_output=True, text=True, check=True).stdout
    vals = dict((int(a), int(b)) for _, a, b in (ln.split() for ln in out.splitlines() if ln.startswith("R ")))
    return [vals[i] for i in range(len(systems))]


# ------------------------------------------------------------------ back to Morita form
def to_morita(C, n, J, K):
    """For a code C ⊂ F₃ⁿ invariant under J, K (J² = K² = −1, JK = −KJ): the Q₈-orbits (blocks, as
    4-tuples of coordinates) and U ⊂ F₃^{2r} with C = F₃² ⊗ U in the quaternion coordinates of each
    orbit (x_1 = y_{o0}, x_i, x_j, x_k from J e_{o0}, K e_{o0}, JK e_{o0}). Returns (orbits, U)."""
    seen, orbs = set(), []
    for i in range(n):
        if i in seen:
            continue
        o0 = i
        pJ, sJ = J; pK, sK = K
        q = pK[o0]
        coords = [(o0, 1), (pJ[o0], sJ[o0]), (q, sK[o0]), (pJ[q], sK[o0] * sJ[q])]
        seen.update(c for c, _ in coords)
        orbs.append(coords)
    r = len(orbs)
    # matrices of each basis word, then solve "second rows = 0"
    B = rref(C)

    def blockmats(w):
        out = []
        for coords in orbs:
            a, b, c, d = [(s * w[p]) % 3 for p, s in coords]
            X = [[0, 0], [0, 0]]
            for coef, E in zip((a, b, c, d), QBASIS):
                for u_ in range(2):
                    for v_ in range(2):
                        X[u_][v_] = (X[u_][v_] + coef * E[u_][v_]) % 3
            out.append(X)
        return out
    mats = [blockmats(w) for w in B]
    # linear conditions on coefficients c (len(B)): Σ c_j (second row of block b of word j) = 0
    rows = [[mats[j][b][1][e] for j in range(len(B))] for b in range(r) for e in range(2)]
    R_ = rref(rows) if any(any(x) for x in rows) else []
    piv = [next(j for j in range(len(B)) if r_[j]) for r_ in R_]
    U = []
    for fj in (j for j in range(len(B)) if j not in piv):
        c = [0] * len(B); c[fj] = 1
        for r_, pj in zip(R_, piv):
            c[pj] = (-r_[fj]) % 3
        U.append([sum(c[j] * mats[j][b][0][e] for j in range(len(B))) % 3 for b in range(r) for e in range(2)])
    U = rref(U)
    assert len(U) == r, "C is not of the form F_3^2 (x) U"
    return [tuple(p for p, _ in coords) for coords in orbs], U
