"""Route (1): lattice of integral invariants for cwe's of self-dual ternary codes containing 1.

Group G: MacWilliams M = (1/sqrt3)[[1,1,1],[1,w,w^2],[1,w^2,w]], S_3 symbol permutations,
diag(w,1,1) etc.  Invariants of degree n = 3m are S_3-symmetric polynomials in X=x^3,Y=y^3,Z=z^3
fixed by M.  Basis: monomial symmetric m_lam, lam a partition of m into <= 3 parts.

Index functional (GJF convention): I(P) = P(0, 1, -1)   (x <-> symbol 0, y <-> 1, z <-> -1).

Computes, for each n: the Z-lattice Lam of invariant integer polynomials (coords c_lam),
the extra "orbit" congruences a genuine cwe satisfies (coefficient 1 on m_(m,0,0), even
coefficient on two-equal-part lam, coefficient = 0 mod 6 on lam=(m/3)^3), and the set of
values of I on the resulting affine lattice.
"""
import sys, random
from fractions import Fraction
from math import gcd


# ---- Z[w] arithmetic, w^2 = -1 - w; element (a, b) = a + b w
def zmul(p, q):
    a, b = p
    c, d = q
    return (a * c - b * d, a * d + b * c - b * d)


def zadd(p, q):
    return (p[0] + q[0], p[1] + q[1])


def zpow(p, e):
    r = (1, 0)
    while e:
        if e & 1:
            r = zmul(r, p)
        p = zmul(p, p)
        e >>= 1
    return r


W = (0, 1)
W2 = (-1, -1)


def partitions3(m):
    out = []
    for a in range(m, -1, -1):
        for b in range(min(a, m - a), -1, -1):
            c = m - a - b
            if c <= b:
                out.append((a, b, c))
    return out


def perms(lam):
    from itertools import permutations
    return sorted(set(permutations(lam)))


def eval_mlam(lam, X, Y, Z):
    tot = (0, 0)
    for (a, b, c) in perms(lam):
        tot = zadd(tot, zmul(zmul(zpow(X, a), zpow(Y, b)), zpow(Z, c)))
    return tot


def rref_Q(rows, N):
    M = [[Fraction(x) for x in r] for r in rows]
    piv = []
    r = 0
    for c in range(N):
        p = None
        for i in range(r, len(M)):
            if M[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    return M[:r], piv


def int_kernel(A, N):
    """Z-basis of {x in Z^N : A x = 0} for integer matrix A (list of rows), via column ops."""
    # U tracks column operations: A * U = H
    A = [r[:] for r in A]
    U = [[1 if i == j else 0 for j in range(N)] for i in range(N)]
    col = 0
    for row in range(len(A)):
        if col >= N:
            break
        # gcd-reduce entries A[row][col:] into column `col`
        while True:
            nz = [j for j in range(col, N) if A[row][j] != 0]
            if not nz:
                break
            jmin = min(nz, key=lambda j: abs(A[row][j]))
            # swap jmin to col
            if jmin != col:
                for r_ in A:
                    r_[col], r_[jmin] = r_[jmin], r_[col]
                for r_ in U:
                    r_[col], r_[jmin] = r_[jmin], r_[col]
            done = True
            for j in range(col + 1, N):
                if A[row][j] != 0:
                    q = A[row][j] // A[row][col]
                    for r_ in A:
                        r_[j] -= q * r_[col]
                    for r_ in U:
                        r_[j] -= q * r_[col]
                    if A[row][j] != 0:
                        done = False
            if done:
                break
        if any(A[row][j] != 0 for j in range(col, N)):
            col += 1
    # columns col..N-1 of U span the kernel
    return [[U[i][j] for i in range(N)] for j in range(col, N)]


def hnf_rows(B):
    """Row HNF (echelon over Z) of integer row vectors; returns nonzero rows."""
    B = [r[:] for r in B if any(r)]
    if not B:
        return []
    N = len(B[0])
    out = []
    r0 = 0
    for c in range(N):
        rows = [i for i in range(r0, len(B)) if B[i][c] != 0]
        if not rows:
            continue
        while True:
            rows = [i for i in range(r0, len(B)) if B[i][c] != 0]
            imin = min(rows, key=lambda i: abs(B[i][c]))
            B[r0], B[imin] = B[imin], B[r0]
            done = True
            for i in range(r0 + 1, len(B)):
                if B[i][c] != 0:
                    q = B[i][c] // B[r0][c]
                    B[i] = [a - q * b for a, b in zip(B[i], B[r0])]
                    if B[i][c] != 0:
                        done = False
            if done:
                break
        if B[r0][c] < 0:
            B[r0] = [-a for a in B[r0]]
        r0 += 1
        if r0 == len(B):
            break
    return [r for r in B[:r0] if any(r)]


def invariant_lattice(n, rng, npts=None):
    assert n % 12 == 0
    m = n // 3
    lams = partitions3(m)
    N = len(lams)
    npts = npts or (N + 10)
    s = 3 ** (n // 2)
    rows = []
    for _ in range(npts):
        v = [(rng.randint(-3, 3), rng.randint(-3, 3)) for _ in range(3)]
        x, y, z = v
        w0 = zadd(zadd(x, y), z)
        w1 = zadd(zadd(x, zmul(W, y)), zmul(W2, z))
        w2 = zadd(zadd(x, zmul(W2, y)), zmul(W, z))
        X, Y, Z = zpow(x, 3), zpow(y, 3), zpow(z, 3)
        WX, WY, WZ = zpow(w0, 3), zpow(w1, 3), zpow(w2, 3)
        ra, rb = [], []
        for lam in lams:
            a = eval_mlam(lam, WX, WY, WZ)
            b = eval_mlam(lam, X, Y, Z)
            ra.append(a[0] - s * b[0])
            rb.append(a[1] - s * b[1])
        rows.append(ra)
        rows.append(rb)
    R, piv = rref_Q(rows, N)
    # clear denominators
    Rint = []
    for r in R:
        L = 1
        for x in r:
            L = L * x.denominator // gcd(L, x.denominator)
        Rint.append([int(x * L) for x in r])
    K = int_kernel(Rint, N)
    K = hnf_rows(K)
    return lams, K


def index_functional(lam):
    a, b, c = lam
    if c != 0:
        return 0
    # monomials with X-exponent 0: permutations with first entry 0
    tot = 0
    for (p, q, r) in perms(lam):
        if p == 0:
            tot += (-1) ** r  # Y^q Z^r at Y=1, Z=-1
    return tot


def analyse(n, rng):
    lams, K = invariant_lattice(n, rng)
    m = n // 3
    N = len(lams)
    d = len(K)
    Ivec = [index_functional(l) for l in lams]
    i0 = lams.index((m, 0, 0))
    # sanity: summed design identity on every basis invariant:
    #   sum_{n0=0 monomials} coeff*(-1)^{n2}*(n1-n2)^2 = n * I(P)
    def summed_design(c):
        tot = 0
        for lam, cl in zip(lams, c):
            if cl == 0:
                continue
            for (p, q, r) in perms(lam):
                if p == 0:
                    tot += cl * (-1) ** r * (3 * q - 3 * r) ** 2
        return tot
    design_ok = all(summed_design(c) == n * sum(a * b for a, b in zip(c, Ivec)) for c in K)
    # plain integrality: values of I on {P in Lam : coeff x^n = 1}
    def values(basis):
        # basis rows (coords c). affine slice c[i0]=1.
        g0 = 0
        for r in basis:
            g0 = gcd(g0, r[i0])
        if g0 != 1:
            return None
        # transform basis so that exactly one row has c[i0] = 1 and others 0 (HNF on column i0 first)
        # reorder coordinates: put i0 first
        B = [[r[i0]] + [r[j] for j in range(N) if j != i0] for r in basis]
        H = hnf_rows(B)
        first = H[0]
        assert first[0] == 1
        rest = [h for h in H[1:]]
        def Ival(row):
            full = [0] * N
            full[i0] = row[0]
            idx = 1
            for j in range(N):
                if j != i0:
                    full[j] = row[idx]
                    idx += 1
            return sum(a * b for a, b in zip(full, Ivec))
        g = 0
        for h in rest:
            g = gcd(g, Ival(h))
        return Ival(first), g
    v_plain = values(K)
    # orbit congruences: c_lam even for lam with exactly two equal parts (lam != (m,0,0)); c = 0 mod 6 for (m/3)^3
    cons = []
    for j, lam in enumerate(lams):
        if lam == (m, 0, 0):
            continue
        a, b, c = lam
        if a == b == c:
            cons.append((j, 6))
        elif a == b or b == c:
            cons.append((j, 2))
    # sublattice of Z^d (coeffs t in basis K) with sum_t t_i K[i][j] = 0 mod mod_j
    # integer kernel of [K^T rows for constrained j | mod_j * e_j]
    ncons = len(cons)
    A = []
    for idx, (j, md) in enumerate(cons):
        row = [K[i][j] for i in range(d)] + [md if t == idx else 0 for t in range(ncons)]
        A.append(row)
    if A:
        ker = int_kernel(A, d + ncons)
        sub = []
        for kv in ker:
            t = kv[:d]
            sub.append([sum(t[i] * K[i][j] for i in range(d)) for j in range(N)])
        sub = hnf_rows(sub)
    else:
        sub = K
    v_orbit = values(sub)
    return N, d, design_ok, v_plain, v_orbit


if __name__ == "__main__":
    rng = random.Random(7)
    ns = [int(a) for a in sys.argv[1:]] or [12, 24, 36, 48, 60, 72]
    for n in ns:
        N, d, dok, vp, vo = analyse(n, rng)
        k = n // 12
        need = 24 // gcd(24, k)
        print("n=%d: #sym basis=%d, dim invariants=%d, summed-design identity on all invariants: %s" % (n, N, d, dok))
        print("   I on integral invariants with x^n-coeff 1:            %s  (offset, gcd)" % (vp,))
        print("   I after orbit congruences (even/6 | coefficients):   %s ; TMF needs %d | I, GJF conj 24 | I" % (vo, need))
        sys.stdout.flush()
