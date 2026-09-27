"""Generate the Lean data of the Tier A seeds (lean/GJF/Chain*.lean).

For a seed code, a group and a block system this script
- orders every block so that each generator acts by a local map of the group LM of
  lean/GJF/LocalMaps.lean (A r keeps the pairs, B r swaps them);
- row-reduces the generator matrix on an information set (singletons, and whole blocks
  where needed), in the row order of the evaluation tree;
- prints the Lean literals: bitmask rows, the block placement c, the tree, the generators.
It also recomputes every certified number with an independent plain enumeration where
feasible (information-set sum in Python), so the Lean statements are known to be true
before the kernel checks them.

Usage: python3 lean_seed_data.py q8        (writes lean_seed_data_q8.log)
"""
import itertools
import os
import sys

from mainq_common import mono_apply, mono_mul, mono_neg
from mainq_q8chain import q8

PHI = (0, -1, 1)


def lam(w):
    return 1 if w == 4 else (-2 if w == 1 else 0)


def load(path):
    return [[int(ch) for ch in line.strip()] for line in open(path) if line.strip()]


def rref_on(M, piv, n):
    """Row-reduce M so that column piv[r] is the r-th unit vector."""
    M = [row[:] for row in M]
    for r, c in enumerate(piv):
        p = next(i for i in range(r, len(M)) if M[i][c])
        M[r], M[p] = M[p], M[r]
        inv = M[r][c]  # 1 or 2, self-inverse mod 3
        M[r] = [(x * inv) % 3 for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % 3 for a, b in zip(M[i], M[r])]
    return M


def rank(M):
    M = [row[:] for row in M]
    r = 0
    n = len(M[0]) if M else 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c]), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = M[r][c]
        M[r] = [(x * inv) % 3 for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % 3 for a, b in zip(M[i], M[r])]
        r += 1
    return r


def in_span(M, v):
    return rank(M + [list(v)]) == rank(M)


# ---- the local-map group LM (lean/GJF/LocalMaps.lean) ----

def rot(k):
    """J+^k on a pair, as (perm, sign) on Fin 2."""
    k %= 4
    perm = (0, 1) if k % 2 == 0 else (1, 0)
    if k == 0:
        sg = (1, 1)
    elif k == 2:
        sg = (-1, -1)
    elif k == 1:
        sg = (1, -1)
    else:
        sg = (-1, 1)
    return perm, sg


def kk(r, f, a):
    if a == 0:
        return r % 4
    return (2 - r) % 4 if f else (-r) % 4


def lsp(m):
    """lsp m as a monomial map on positions P = (a, b) -> 2a + b."""
    r, f = m
    perm = [0] * 4
    sg = [0] * 4
    for a in range(2):
        pa = (1 - a) if f else a
        rp, rs = rot(kk(r, f, a))
        for b in range(2):
            perm[2 * a + b] = 2 * pa + rp[b]
            sg[2 * a + b] = rs[b]
    return tuple(perm), tuple(sg)


LM = [(r, f) for r in range(4) for f in (False, True)]
LSP = {m: lsp(m) for m in LM}


def local_map(g, src, dst):
    """g read in the labels of the ordered blocks src -> dst (None if g src != dst)."""
    p, s = g
    perm, sg = [0] * 4, [0] * 4
    for q, x in enumerate(src):
        if p[x] not in dst:
            return None
        perm[q] = dst.index(p[x])
        sg[q] = s[x]
    return tuple(perm), tuple(sg)


def find_lm(g, src, dst):
    loc = local_map(g, src, dst)
    for m, v in LSP.items():
        if v == loc:
            return m
    return None


def lean_F(x):
    return str(x % 3)


def bits(row):
    m1 = sum(1 << i for i, x in enumerate(row) if x == 1)
    m2 = sum(1 << i for i, x in enumerate(row) if x == 2)
    return m1, m2


def rsigma_infoset(rows, piv, S, blocks):
    """R_sigma by enumerating the information set (rows systematic on piv, all in S)."""
    n = len(rows[0])
    total = 0
    k = len(rows)
    for signs in itertools.product((1, 2), repeat=k):
        w = [0] * n
        for a, r in zip(signs, rows):
            if a:
                w = [(x + a * y) % 3 for x, y in zip(w, r)]
        val = 1
        for i in S:
            val *= PHI[w[i]]
            if val == 0:
                break
        if val == 0:
            continue
        for b in blocks:
            val *= lam(sum(1 for i in b if w[i]))
            if val == 0:
                break
        total += val
    return total


def seed_q8(out):
    E = load('../codes/q8chain_len24.txt')
    n = 24
    J, K = q8(n)
    out(f'J = {J}')
    out(f'K = {K}')
    for g, name in ((J, 'J'), (K, 'K')):
        assert all(in_span(E, mono_apply(g, r)) for r in E), name
    neg = mono_neg(n)
    assert mono_mul(J, J) == neg and mono_mul(K, K) == neg
    assert mono_mul(K, J) == mono_mul(neg, mono_mul(J, K))
    out('J, K in Aut(E); J^2 = K^2 = -1, KJ = -JK: ok')
    # block orderings with LM local maps
    blocks = []
    for grp in ((8, 9, 10, 11), (12, 13, 14, 15)):
        found = None
        for o in itertools.permutations(grp):
            mj, mk = find_lm(J, o, o), find_lm(K, o, o)
            if mj is not None and mk is not None and mj[1] is False:
                found = (o, mj, mk)
                break
        assert found, grp
        blocks.append(found)
    for o, mj, mk in blocks:
        out(f'block {o}: J = {mj}, K = {mk}')
    bset = set(x for o, _, _ in blocks for x in o)
    S = [i for i in range(n) if i not in bset]
    # information set: 12 singletons
    piv = None
    for cand in itertools.combinations(S, 12):
        if rank([[r[c] for c in cand] for r in E]) == 12:
            piv = list(cand)
            break
    R = rref_on(E, piv, n)
    blk = [o for o, _, _ in blocks]
    rs = rsigma_infoset(R, piv, S, blk)
    out(f'information set {piv}; R_sigma = {rs} (2^12 candidates)')
    assert rs == 24
    # Lean literals
    out('--- Lean ---')
    out('rows : ' + '[' + ', '.join(f'({a}, {b})' for a, b in map(bits, R)) + ']')
    out('info : ![' + ', '.join(map(str, piv)) + ']')
    out('cS : ![' + ', '.join(map(str, S)) + ']')
    out('cB : ' + '![' + ', '.join('![![%d, %d], ![%d, %d]]' % o for o in blk) + ']')
    tree = []
    for r, c in zip(R, piv):
        a, b = bits(r)
        tree.append(f'.row {a} {b}')
        tree.append(f'.chkS {c}')
    out('tree : [' + ', '.join(tree) + ']')
    sl = [S.index(i) for i in S]
    for g, name in ((J, 'J'), (K, 'K')):
        p, s = g
        gp = [S.index(p[i]) for i in S]
        gs = [lean_F(s[i]) for i in S]
        out(f'{name}s perm : ![' + ', '.join(map(str, gp)) + ']')
        out(f'{name}s sgn : ![' + ', '.join(gs) + ']')
        out(f'{name} full perm : ![' + ', '.join(map(str, p)) + ']')
        out(f'{name} full sgn : ![' + ', '.join(lean_F(x) for x in s) + ']')


# ---- helpers for the cyclic and Q8 x Z/3 seeds ----

from mainq_obstruction import signed_cycles


def mono_pow(g, k):
    n = len(g[0])
    r = (tuple(range(n)), (1,) * n)
    for _ in range(k):
        r = mono_mul(g, r)
    return r


def conj_diag(d, g):
    """d g d^-1 for a diagonal d (list of +-1)."""
    p, s = g
    return (p, tuple(d[i] * s[i] * d[p[i]] for i in range(len(p))))


def apply_diag(d, E):
    return [[(x * d[i]) % 3 for i, x in enumerate(r)] for r in E]


def orbits_of(h):
    p = h[0]
    seen, out = set(), []
    for i in range(len(p)):
        if i not in seen:
            o = [i]
            j = p[i]
            while j != i:
                o.append(j)
                j = p[j]
            seen.update(o)
            out.append(o)
    return out


def normaliser(h, eps):
    """Diagonal d with d h d^-1 pure; eps[o] = sign on the first element of orbit o."""
    p, s = h
    d = [0] * len(p)
    for o, e in zip(orbits_of(h), eps):
        d[o[0]] = e
        for a, b in zip(o, o[1:]):
            d[b] = d[a] * s[a]
    return d


def rsigma_full(E, S, blocks):
    """R_sigma by an information-set enumeration over I = pivots (generic, slow but fine <= 2^18)."""
    n = len(E[0])
    k = len(E)
    # information set: choose pivots greedily preferring singletons
    piv = []
    M = [r[:] for r in E]
    order = list(S) + [i for i in range(n) if i not in S]
    rows = []
    R = rref_greedy(E, order)
    return R


def rref_greedy(E, order):
    M = [r[:] for r in E]
    piv = []
    r = 0
    for c in order:
        if r == len(M):
            break
        p = next((i for i in range(r, len(M)) if M[i][c]), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = M[r][c]
        M[r] = [(x * inv) % 3 for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % 3 for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    return M, piv


def weight_R(w, S, blocks):
    val = 1
    for i in S:
        val *= PHI[w[i]]
        if val == 0:
            return 0
    for b in blocks:
        val *= lam(sum(1 for i in b if w[i]))
        if val == 0:
            return 0
    return val


def enum_sum(rows, piv, weight, opts):
    """Sum of weight over codewords whose value on piv[j] lies in opts[j] (systematic rows)."""
    n = len(rows[0])
    total = 0
    for coeffs in itertools.product(*opts):
        w = [0] * n
        for a, r in zip(coeffs, rows):
            if a:
                w = [(x + a * y) % 3 for x, y in zip(w, r)]
        total += weight(w)
    return total


def fixed_basis(E, h):
    """Basis of the h-fixed subcode of E (h any monomial map), systematic on some coordinates."""
    n = len(E[0])
    k = len(E)
    # a = coefficient vector; fixed iff forms N a = 0 with N_i = g(perm i) - s_i g(i)
    p, s = h
    N = []
    for i in range(n):
        N.append([(E[r][p[i]] - s[i] * E[r][i]) % 3 for r in range(k)])
    # nullspace of N (k unknowns)
    ns = nullspace_mod3(N, k)
    F = []
    for v in ns:
        w = [sum(v[r] * E[r][i] for r in range(k)) % 3 for i in range(n)]
        F.append(w)
    return F, N


def nullspace_mod3(N, k):
    M = [r[:] for r in N]
    piv = []
    r = 0
    for c in range(k):
        p = next((i for i in range(r, len(M)) if M[i][c]), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = M[r][c]
        M[r] = [(x * inv) % 3 for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % 3 for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(k) if c not in piv]
    basis = []
    for fcol in free:
        v = [0] * k
        v[fcol] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-M[i][fcol]) % 3
        basis.append(v)
    return basis


def left_inverse(N, k):
    """Sparse L (list of rows: [(form index, coeff)]) with L N = I_k, or None."""
    # choose k independent rows of N, invert
    chosen = []
    M = []
    for idx, row in enumerate(N):
        if rank(M + [row]) > len(M):
            M.append(row)
            chosen.append(idx)
        if len(M) == k:
            break
    if len(M) < k:
        return None
    # invert M (k x k) mod 3
    A = [M[i][:] + [1 if j == i else 0 for j in range(k)] for i in range(k)]
    for c in range(k):
        p = next(i for i in range(c, k) if A[i][c])
        A[c], A[p] = A[p], A[c]
        inv = A[c][c]
        A[c] = [(x * inv) % 3 for x in A[c]]
        for i in range(k):
            if i != c and A[i][c]:
                f = A[i][c]
                A[i] = [(a - f * b) % 3 for a, b in zip(A[i], A[c])]
    Minv = [row[k:] for row in A]
    # L = Minv * (selection): L[r] = sum_j Minv[r][j] * e_{chosen[j]}
    L = [[(chosen[j], Minv[r][j]) for j in range(k) if Minv[r][j]] for r in range(k)]
    # verify
    for r in range(k):
        for r2 in range(k):
            v = sum(c * N[i][r2] for i, c in L[r]) % 3
            assert v == (1 if r == r2 else 0)
    return L


def lean_rows(R):
    return '[' + ', '.join(f'({a}, {b})' for a, b in map(bits, R)) + ']'


def lean_perm(p):
    return '![' + ', '.join(map(str, p)) + ']'


def lean_sgn(s):
    return '![' + ', '.join(lean_F(x) for x in s) + ']'


def lean_L(L, n):
    def form(i):
        return f'(.inl {i})' if i < n else f'(.inr {i - n})'
    return '![' + ', '.join('[' + ', '.join(f'({form(i)}, {c})' for i, c in row) + ']' for row in L) + ']'


def order_blocks(gp, blocks_in_orbit_order, want_keep=True):
    """Orderings of the blocks (sets) such that the local maps of gp (block i -> next in orbit)
    all lie in LM (and keep the pairs if want_keep). blocks_in_orbit_order: list of orbits, each a
    list of sets in the order gp moves them."""
    result = []
    for orbit in blocks_in_orbit_order:
        L = len(orbit)
        perms = [list(itertools.permutations(sorted(b))) for b in orbit]
        found = None

        def rec(i, ords, ms):
            nonlocal found
            if found:
                return
            if i == L:
                m = find_lm(gp, ords[-1], ords[0])
                if m is not None and not (want_keep and m[1]):
                    found = (ords, ms + [m])
                return
            for o in perms[i]:
                if i > 0:
                    m = find_lm(gp, ords[-1], o)
                    if m is None or (want_keep and m[1]):
                        continue
                    rec(i + 1, ords + [o], ms + [m])
                else:
                    rec(1, [o], [])
        rec(0, [], [])
        if found is None:
            return None
        result.append(found)
    return result


def seed_z12(out, which):
    n = 36
    g = signed_cycles(n, 6)
    h = mono_pow(g, 4)
    assert mono_pow(g, 6) == mono_neg(n)
    if which == 'A6' or which == 'B6':
        E = load('../codes/z12seed_len36_6.txt')
        if which == 'A6':
            orbits = [[{0, 3, 12, 15}, {1, 4, 13, 16}, {2, 5, 14, 17}]]
        else:
            orbits = [[{0, 3, 30, 33}, {1, 4, 31, 34}, {2, 5, 32, 35}],
                      [{6, 9, 12, 15}, {7, 10, 13, 16}, {8, 11, 14, 17}]]
    assert all(in_span(E, mono_apply(g, r)) for r in E)
    hor = orbits_of(h)
    bcoords = set().union(*[b for orb in orbits for b in orb])
    borb = [i for i, o in enumerate(hor) if o[0] in bcoords]
    S = [i for i in range(n) if i not in bcoords]
    found = None
    for bits_ in itertools.product((1, -1), repeat=len(borb)):
        eps = [1] * len(hor)
        for i, e in zip(borb, bits_):
            eps[i] = e
        d = normaliser(h, eps)
        gp = conj_diag(d, g)
        res = order_blocks(gp, orbits)
        if res is not None:
            found = (eps, d, gp, res)
            break
    assert found, 'no ordering'
    eps, d, gp, res = found
    hp = mono_pow(gp, 4)
    assert all(x == 1 for x in hp[1]), 'h not pure'
    Ep = apply_diag(d, E)
    assert all(in_span(Ep, mono_apply(gp, r)) for r in Ep)
    blocks = [ords for ords, ms in res]
    out(f'normalisation eps = {eps}')
    for (ords, ms) in res:
        out(f'orbit orderings {ords}, local maps {ms}')
    # R_sigma sign: fix with a singleton orbit flip if needed
    allb = [b for ords in blocks for b in ords]
    k = len(E)
    # information set: whole blocks if needed
    if which == 'A6':
        order = S + [i for i in range(n) if i not in S]
        R, piv = rref_greedy(Ep, order)
        assert all(c in S for c in piv)
        opts = [(1, 2)] * k
    else:
        # two whole blocks + singletons
        best = None
        for b1, b2 in itertools.combinations(allb, 2):
            order = list(b1) + list(b2) + S
            R, piv = rref_greedy(Ep, order)
            if set(b1) | set(b2) <= set(piv) and len(piv) == k:
                best = (b1, b2, R, piv)
                break
        assert best
        b1, b2, R, piv = best
        out(f'whole blocks in the information set: {b1}, {b2}')
    wR = lambda w: weight_R(w, S, allb)
    if which == 'A6':
        val = enum_sum(R, piv, wR, opts)
    else:
        # enumerate: block rows with weight-1-or-4 patterns, singleton rows +-1
        val = 0
        pats = [pt for pt in itertools.product(range(3), repeat=4)
                if sum(1 for x in pt if x) in (1, 4)]
        nb = 8
        for pa in pats:
            for pb in pats:
                base = [0] * n
                for a, r in zip(pa + pb, R[:8]):
                    if a:
                        base = [(x + a * y) % 3 for x, y in zip(base, r)]
                for sg in itertools.product((1, 2), repeat=k - 8):
                    w = base[:]
                    for a, r in zip(sg, R[8:]):
                        w = [(x + a * y) % 3 for x, y in zip(w, r)]
                    val += wR(w)
    out(f'R_sigma(dE) = {val}')
    if val == -24:
        # flip one singleton h-orbit
        so = next(i for i, o in enumerate(hor) if o[0] not in bcoords)
        eps[so] = -eps[so]
        d = normaliser(h, eps)
        gp = conj_diag(d, g)
        assert order_blocks(gp, orbits) is not None
        Ep = apply_diag(d, E)
        out(f'flipped singleton orbit {hor[so]}; now eps = {eps}')
        return seed_z12_emit(out, which, n, g, d, gp, Ep, orbits, S, bcoords, k)
    assert val == 24
    return seed_z12_emit(out, which, n, g, d, gp, Ep, orbits, S, bcoords, k)


def seed_z12_emit(out, which, n, g, d, gp, Ep, orbits, S, bcoords, k):
    res = order_blocks(gp, orbits)
    blocks = [ords for ords, ms in res]
    allb = [b for ords in blocks for b in ords]
    hp = mono_pow(gp, 4)
    if which == 'A6':
        R, piv = rref_greedy(Ep, S + [i for i in range(n) if i not in S])
        tree = []
        for r, c in zip(R, piv):
            a, b = bits(r)
            tree += [f'.row {a} {b}', f'.chkS {c}']
        val = enum_sum(R, piv, lambda w: weight_R(w, S, allb), [(1, 2)] * k)
    else:
        for b1, b2 in itertools.combinations(allb, 2):
            R, piv = rref_greedy(Ep, list(b1) + list(b2) + S)
            if set(b1) | set(b2) <= set(piv[:8]) and len(piv) == k:
                break
        tree = []
        for j, (r, c) in enumerate(zip(R, piv)):
            a, b = bits(r)
            tree.append(f'.row {a} {b}')
            if j == 3:
                tree.append('.chkB (%d, %d, %d, %d)' % b1)
            elif j == 7:
                tree.append('.chkB (%d, %d, %d, %d)' % b2)
            elif j >= 8:
                tree.append(f'.chkS {c}')
        val = None
    # verify final value
    wR = lambda w: weight_R(w, S, allb)
    if val is None:
        val = 0
        pats = [pt for pt in itertools.product(range(3), repeat=4) if sum(1 for x in pt if x) in (1, 4)]
        for pa in pats:
            for pb in pats:
                base = [0] * n
                for a, r in zip(pa + pb, R[:8]):
                    if a:
                        base = [(x + a * y) % 3 for x, y in zip(base, r)]
                for sg in itertools.product((1, 2), repeat=k - 8):
                    w = base[:]
                    for a, r in zip(sg, R[8:]):
                        w = [(x + a * y) % 3 for x, y in zip(w, r)]
                    val += wR(w)
    out(f'final R_sigma = {val}')
    assert val == 24
    # twined count R^h with representatives (block orbit reps = first block of each orbit)
    F_, N = fixed_basis(R, hp)
    Fr, Fpiv = rref_greedy(F_, S + [i for i in range(n) if i not in S])
    Fr = Fr[:len(F_)]
    Fpiv = Fpiv[:len(F_)]
    reps = [ords[0] for ords in blocks]
    rh = enum_sum(Fr, Fpiv, lambda w: weight_R(w, S, reps), [(0, 1, 2)] * len(Fr))
    out(f'dim fixed code = {len(Fr)}; R^h = {rh}')
    assert rh == 0
    # completeness certificate: forms (n rows for fixedness, d rows for J) in coefficient space
    dF = len(Fr)
    Nfull = [[(R[r][hp[0][i]] - hp[1][i] * R[r][i]) % 3 for r in range(k)] for i in range(n)]
    Nfull += [[R[r][Fpiv[j]] for r in range(k)] for j in range(dF)]
    L = left_inverse(Nfull, k)
    assert L is not None
    out('--- Lean ---')
    out('rows : ' + lean_rows(R))
    out('info : ' + lean_perm(piv))
    out('tree : [' + ', '.join(tree) + ']')
    out('sL : [' + ', '.join(map(str, S)) + ']')
    out('bL : [' + ', '.join('(%d, %d, %d, %d)' % b for b in allb) + ']')
    out('bLrep : [' + ', '.join('(%d, %d, %d, %d)' % b for b in reps) + ']')
    out('frows : ' + lean_rows(Fr))
    out('J : ' + lean_perm(Fpiv))
    out('ftree : [' + ', '.join('.row %d %d' % bits(r) for r in Fr) + ']')
    out('L : ' + lean_L(L, n))
    out('g perm : ' + lean_perm(gp[0]))
    out('g sgn : ' + lean_sgn(gp[1]))
    out('g inv perm : ' + lean_perm([gp[0].index(i) for i in range(n)]))
    gS = [S.index(gp[0][i]) for i in S]
    out('gS perm : ' + lean_perm(gS))
    out('gS inv : ' + lean_perm([gS.index(i) for i in range(len(S))]))
    out('gS sgn : ' + lean_sgn([gp[1][i] for i in S]))
    for ords, ms in res:
        out(f'blocks (orbit order) : {ords}; mu : {ms}')
    return dict(n=n, R=R, piv=piv, tree=tree, S=S, blocks=blocks, allb=allb, reps=reps, Fr=Fr,
                Fpiv=Fpiv, L=L, gp=gp, res=res)


def seed_z12_k3(out):
    """Seed 3 itself (k = 3): Index +24 and T_h = 0 for the signed h = g^4 (no normalisation)."""
    n = 36
    g = signed_cycles(n, 6)
    h = mono_pow(g, 4)
    E = load('../codes/z12seed_len36_3.txt')
    assert all(in_span(E, mono_apply(g, r)) for r in E)
    R, piv = rref_greedy(E, list(range(n)))
    k = len(R)
    idx = enum_sum(R, piv, lambda w: weight_R(w, list(range(n)), []), [(1, 2)] * k)
    out(f'seed 3: Index = {idx} (2^18 candidates)')
    assert idx == 24
    F_, N = fixed_basis(R, h)
    Fr, Fpiv = rref_greedy(F_, list(range(n)))
    Fr, Fpiv = Fr[:len(F_)], Fpiv[:len(F_)]
    th = enum_sum(Fr, Fpiv, lambda w: weight_R(w, list(range(n)), []), [(0, 1, 2)] * len(Fr))
    out(f'seed 3: dim E^h = {len(Fr)}, T_h = {th}')
    assert th == 0
    dF = len(Fr)
    Nfull = [[(R[r][h[0][i]] - h[1][i] * R[r][i]) % 3 for r in range(k)] for i in range(n)]
    Nfull += [[R[r][Fpiv[j]] for r in range(k)] for j in range(dF)]
    L = left_inverse(Nfull, k)
    tree = []
    for r, c in zip(R, piv):
        a, b = bits(r)
        tree += [f'.row {a} {b}', f'.chkS {c}']
    return dict(n=n, R=R, piv=piv, tree=tree, Fr=Fr, Fpiv=Fpiv, L=L, gp=g)


def lean_block_fn(blocks_by_orbit, kind):
    if kind == 'A6':
        orb = blocks_by_orbit[0]
        arr = '![' + ', '.join('![![%d, %d], ![%d, %d]]' % o for o in orb) + ']'
        return f'(fun q => {arr} q.1 q.2.1 q.2.2)'
    arr = '![' + ', '.join('![' + ', '.join('![![%d, %d], ![%d, %d]]' % o for o in orb) + ']'
                           for orb in blocks_by_orbit) + ']'
    return f'(fun q => {arr} q.1.2 q.1.1 q.2.1 q.2.2)'


def emit_z12(path, dA, dB, d3):
    L = []
    w = L.append
    w('import GJF.SeedCert')
    w('')
    w('/-!')
    w('# Data of the ℤ/12 seeds (generated by `ternary60/theory/lean_seed_data.py z12`; do not edit)')
    w('')
    w('* `Z12A`: seed `z12seed_len36_6` normalised so that `h = g⁴` is a permutation, system `σ_A6`')
    w('  (3 blocks, one `g`-orbit).')
    w('* `Z12B`: the same seed and normalisation, system `σ_B6` (6 blocks, two `g`-orbits).')
    w('* `Z12K3`: seed `z12seed_len36_3` (not normalised), for `k = 3`.')
    w('-/')
    w('')
    w('set_option maxRecDepth 100000')
    w('')
    w('namespace GJF.Ex')
    w('')
    w('open Eval')
    w('')
    for name, d, kind in (('Z12A', dA, 'A6'), ('Z12B', dB, 'B6'), ('Z12K3', d3, 'K3')):
        n = d['n']
        w(f'namespace {name}')
        w('')
        w('def rows : List (ℕ × ℕ) := ' + lean_rows(d['R']))
        w('')
        w(f'def info : Fin rows.length → Fin {n} := ' + lean_perm(d['piv']))
        w('')
        w('def tree : List FStep := [' + ', '.join(d['tree']) + ']')
        w('')
        w('def frows : List (ℕ × ℕ) := ' + lean_rows(d['Fr']))
        w('')
        w(f'def J : Fin frows.length → Fin {n} := ' + lean_perm(d['Fpiv']))
        w('')
        w('def ftree : List FStep := [' + ', '.join('.row %d %d' % bits(r) for r in d['Fr']) + ']')
        w('')
        w(f"def L : Fin {len(d['R'])} → List ((Fin {n} ⊕ Fin {len(d['Fr'])}) × ZMod 3) := " + lean_L(d['L'], n))
        w('')
        gp = d['gp']
        w(f'def gperm : Fin {n} → Fin {n} := ' + lean_perm(gp[0]))
        w(f'def ginv : Fin {n} → Fin {n} := ' + lean_perm([gp[0].index(i) for i in range(n)]))
        w(f'def gsgn : Fin {n} → ZMod 3 := ' + lean_sgn(gp[1]))
        w('')
        if kind != 'K3':
            S = d['S']
            w('def sL : List ℕ := [' + ', '.join(map(str, S)) + ']')
            w('def bL : List (ℕ × ℕ × ℕ × ℕ) := [' + ', '.join('(%d, %d, %d, %d)' % b for b in d['allb']) + ']')
            w('def bLrep : List (ℕ × ℕ × ℕ × ℕ) := [' + ', '.join('(%d, %d, %d, %d)' % b for b in d['reps']) + ']')
            nS = len(S)
            gS = [S.index(gp[0][i]) for i in S]
            w(f'def gSperm : Fin {nS} → Fin {nS} := ' + lean_perm(gS))
            w(f'def gSinv : Fin {nS} → Fin {nS} := ' + lean_perm([gS.index(i) for i in range(nS)]))
            w(f'def gSsgn : Fin {nS} → ZMod 3 := ' + lean_sgn([gp[1][i] for i in S]))
            Bt = 'Fin 3' if kind == 'A6' else 'Fin 3 × Fin 2'
            w(f'/-- The placement: singletons, then the blocks in `g`-orbit order. -/')
            w(f'def c : Blk (Fin {nS}) ({Bt}) → Fin {n} :=')
            w('  Sum.elim ' + lean_perm(S) + ' ' + lean_block_fn(d['blocks'], kind))
            w('')
        else:
            w(f'def sL : List ℕ := [' + ', '.join(map(str, range(n))) + ']')
            w('')
        w(f'end {name}')
        w('')
    w('end GJF.Ex')
    open(path, 'w').write('\n'.join(L) + '\n')




def seed_q8z3(out):
    """The Q8 x Z/3 seed (length 72); R_sigma(E72) = 24 is not certified here (a Lean hypothesis)."""
    from mainq_morita import q8_gens, h_gen
    E = load('../codes/q8z3_seed72.txt')
    n = 72
    J, K = q8_gens(18)
    H = h_gen(6)
    for g in (J, K, H):
        assert all(in_span(E, mono_apply(g, r)) for r in E)
    neg = mono_neg(n)
    assert mono_mul(J, J) == neg and mono_mul(K, K) == neg
    assert mono_mul(K, J) == mono_mul(neg, mono_mul(J, K))
    assert mono_pow(H, 3) == (tuple(range(n)), (1,) * n)
    assert mono_mul(H, J) == mono_mul(J, H) and mono_mul(H, K) == mono_mul(K, H)
    out('J, K, h in Aut(E); Q8 relations, h^3 = 1, h commutes with J, K: ok')
    # blocks (s, t) = orbit block 3s + t, coordinates 4b..4b+3; h: t -> t+1 with identity local maps
    blocks = {}
    for s_ in range(2):
        b0 = 3 * s_
        found = None
        for o in itertools.permutations(range(4 * b0, 4 * b0 + 4)):
            mj, mk = find_lm(J, o, o), find_lm(K, o, o)
            if mj is None or mk is None or mj[1] or not mk[1]:
                continue
            ords = [o]
            for t in (1, 2):
                ords.append(tuple(H[0][x] for x in ords[-1]))
            ok = all(find_lm(H, ords[t], ords[(t + 1) % 3]) == (0, False) for t in range(3))
            ok = ok and all(find_lm(J, q, q) == mj and find_lm(K, q, q) == mk for q in ords)
            if ok:
                found = (ords, mj, mk)
                break
        assert found
        for t in range(3):
            blocks[(s_, t)] = found[0][t]
        out(f'orbit s = {s_}: blocks {found[0]}, J = {found[1]}, K = {found[2]}')
    allb = [blocks[(s_, t)] for s_ in range(2) for t in range(3)]
    bset = set(x for b in allb for x in b)
    S = [i for i in range(n) if i not in bset]
    R, piv = rref_greedy(E, S + sorted(bset))
    k = len(R)
    out(f'information set: {sum(1 for c in piv if c in S)} singletons, {sum(1 for c in piv if c not in S)} block coordinates')
    # fixed code of h, systematic on singletons
    F_, N = fixed_basis(R, H)
    Fr, Fpiv = rref_greedy(F_, S + sorted(bset))
    Fr, Fpiv = Fr[:len(F_)], Fpiv[:len(F_)]
    assert all(c in S for c in Fpiv)
    reps = [blocks[(0, 0)], blocks[(1, 0)]]
    rh = enum_sum(Fr, Fpiv, lambda w: weight_R(w, S, reps), [(1, 2)] * len(Fr))
    out(f'dim E^h = {len(Fr)}; R^h = {rh} (2^{len(Fr)} candidates)')
    assert rh == 0
    dF = len(Fr)
    Nfull = [[(R[r][H[0][i]] - H[1][i] * R[r][i]) % 3 for r in range(k)] for i in range(n)]
    Nfull += [[R[r][Fpiv[j]] for r in range(k)] for j in range(dF)]
    L = left_inverse(Nfull, k)
    assert L is not None
    # optional: R_sigma of the Lean rows with the independent evaluator
    exe = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'target', 'release', 'rsigma_is')
    if os.path.exists(exe):
        import subprocess, tempfile
        with tempfile.NamedTemporaryFile('w', suffix='.txt', delete=False) as fh:
            fh.write('\n'.join(''.join(map(str, r)) for r in R) + '\n')
            fn = fh.name
        blk = ';'.join(','.join(map(str, b)) for b in allb)
        res = subprocess.run([exe, fn, blk, '4'], capture_output=True, text=True)
        out('rsigma_is on the Lean rows: ' + ' '.join(res.stdout.split()[-6:]))
    return dict(n=n, R=R, piv=piv, S=S, allb=allb, reps=reps, Fr=Fr, Fpiv=Fpiv, L=L, J=J, K=K, H=H,
                blocks=blocks)


def emit_q8z3(path, d):
    L = []
    w = L.append
    n = d['n']
    S = d['S']
    nS = len(S)
    w('import GJF.SeedCert')
    w('')
    w('/-!')
    w('# Data of the Q₈ × ℤ/3 seed (generated by `ternary60/theory/lean_seed_data.py q8z3`; do not edit)')
    w('')
    w('The seed `q8z3_seed72` (length 72), row-reduced; the blocks `(s, t)` are the orbit blocks')
    w('`3s + t` (`s < 2`, `t < 3`), ordered so that `J` acts by `A`, `K` by `B` and `h` by the identity.')
    w('-/')
    w('')
    w('set_option maxRecDepth 100000')
    w('')
    w('namespace GJF.Ex')
    w('')
    w('open Eval')
    w('')
    w('namespace Q8Z3')
    w('')
    w('def rows : List (ℕ × ℕ) := ' + lean_rows(d['R']))
    w('')
    w(f'def info : Fin rows.length → Fin {n} := ' + lean_perm(d['piv']))
    w('')
    w('def frows : List (ℕ × ℕ) := ' + lean_rows(d['Fr']))
    w('')
    w(f'def J : Fin frows.length → Fin {n} := ' + lean_perm(d['Fpiv']))
    w('')
    tree = []
    for r, c in zip(d['Fr'], d['Fpiv']):
        a, b = bits(r)
        tree += [f'.row {a} {b}', f'.chkS {c}']
    w('def ftree : List FStep := [' + ', '.join(tree) + ']')
    w('')
    w(f"def L : Fin {len(d['R'])} → List ((Fin {n} ⊕ Fin {len(d['Fr'])}) × ZMod 3) := " + lean_L(d['L'], n))
    w('')
    w('def sL : List ℕ := [' + ', '.join(map(str, S)) + ']')
    w('def bLrep : List (ℕ × ℕ × ℕ × ℕ) := [' + ', '.join('(%d, %d, %d, %d)' % b for b in d['reps']) + ']')
    w('')
    for name in ('J', 'K', 'H'):
        g = d[name]
        w(f'def {name}perm : Fin {n} → Fin {n} := ' + lean_perm(g[0]))
        w(f'def {name}inv : Fin {n} → Fin {n} := ' + lean_perm([g[0].index(i) for i in range(n)]))
        w(f'def {name}sgn : Fin {n} → ZMod 3 := ' + lean_sgn(g[1]))
        gS = [S.index(g[0][i]) for i in S]
        w(f'def {name}Sperm : Fin {nS} → Fin {nS} := ' + lean_perm(gS))
        w(f'def {name}Sinv : Fin {nS} → Fin {nS} := ' + lean_perm([gS.index(i) for i in range(nS)]))
        w(f'def {name}Ssgn : Fin {nS} → ZMod 3 := ' + lean_sgn([g[1][i] for i in S]))
        w('')
    arr = '![' + ', '.join('![' + ', '.join('![![%d, %d], ![%d, %d]]' % d['blocks'][(s_, t)] for t in range(3)) + ']'
                           for s_ in range(2)) + ']'
    w('/-- The placement: singletons, then the blocks `(s, t)`. -/')
    w(f'def c : Blk (Fin {nS}) (Fin 2 × Fin 3) → Fin {n} :=')
    w('  Sum.elim ' + lean_perm(S) + f' (fun q => {arr} q.1.1 q.1.2 q.2.1 q.2.2)')
    w('')
    w('end Q8Z3')
    w('')
    w('end GJF.Ex')
    open(path, 'w').write('\n'.join(L) + '\n')


# ---- chunked kernel certificates (mirror of lean/GJF/Eval.lean: fastT, leavesT) ----

def _r1f(x1, x2, y1, y2):
    return (x1 ^ (x1 & (y1 | y2))) | (y1 ^ (y1 & (x1 | x2))) | (x2 & y2)


def _tb(m, i):
    return (m >> i) & 1 == 1


def _cnt(o, bb):
    return sum(1 for i in bb if _tb(o, i))


def _lamC(c):
    return 1 if c == 4 else (-2 if c == 1 else 0)


def parse_tree(tree):
    out = []
    for t in tree:
        parts = t.replace('(', ' ').replace(')', ' ').replace(',', ' ').split()
        if parts[0] == '.row':
            out.append(('row', int(parts[1]), int(parts[2])))
        elif parts[0] == '.chkS':
            out.append(('chkS', int(parts[1])))
        else:
            out.append(('chkB', tuple(int(x) for x in parts[1:5])))
    return out


def WtF(sL, bL, m1, m2):
    v = 1
    for i in sL:
        if _tb(m1, i):
            v = -v
        elif not _tb(m2, i):
            return 0
    o = m1 | m2
    for bb in bL:
        v *= _lamC(_cnt(o, bb))
        if v == 0:
            return 0
    return v


def leavesT(st, a, b):
    if not st:
        return [(a, b)]
    s, rest = st[0], st[1:]
    if s[0] == 'row':
        r1, r2 = s[1], s[2]
        return (leavesT(rest, a, b) + leavesT(rest, _r1f(a, b, r1, r2), _r1f(b, a, r2, r1)) +
                leavesT(rest, _r1f(a, b, r2, r1), _r1f(b, a, r1, r2)))
    if s[0] == 'chkS':
        return leavesT(rest, a, b) if _tb(a | b, s[1]) else []
    c = _cnt(a | b, s[1])
    return leavesT(rest, a, b) if c in (1, 4) else []


def fastT(w, st, a, b):
    return sum(w(m1, m2) for m1, m2 in leavesT(st, a, b))


def emit_cert(path, imports, ns, wexpr, tree_name, tree, sL, bL, target, thm, per_chunk=4500,
              doc=''):
    st = parse_tree(tree)
    total = len(leavesT(st, 0, 0))
    p = 0
    while p < len(st) and max(len(leavesT(st[p:], a, b)) for a, b in leavesT(st[:p], 0, 0)) > per_chunk:
        p += 1
    pre = leavesT(st[:p], 0, 0)
    post = st[p:]
    w = lambda m1, m2: WtF(sL, bL, m1, m2)
    vals = [fastT(w, post, a, b) for a, b in pre]
    assert sum(vals) == target, (sum(vals), target)
    L = []
    o = L.append
    o('\n'.join(f'import {i}' for i in imports))
    o('')
    o('/-!')
    o(f'# Kernel certificate: `{thm}` (generated by `ternary60/theory/lean_seed_data.py`; do not edit)')
    o('')
    o(f'{doc}The tree ({total} leaves) is split below its first {p} steps into {len(pre)} chunks, each')
    o('checked by the kernel as a separate declaration (`Eval.fastT_split`), which bounds the memory.')
    o('-/')
    o('')
    o('set_option maxRecDepth 100000')
    o('')
    o(f'namespace {ns}')
    o('')
    o('open Eval')
    o('')
    for j, ((a, b), v) in enumerate(zip(pre, vals)):
        o(f'theorem {thm}_chunk{j} : fastT ({wexpr}) ({tree_name}.drop {p}) {a} {b} = {v} := by')
        o('  decide +kernel')
        o('')
    o(f'theorem {thm}_leaves : leavesT ({tree_name}.take {p}) 0 0 = [' +
      ', '.join(f'({a}, {b})' for a, b in pre) + '] := by decide')
    o('')
    o(f'theorem {thm} : fastT ({wexpr}) {tree_name} 0 0 = {target} := by')
    o(f'  rw [fastT_split _ {tree_name} {p}, {thm}_leaves]')
    o('  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ' +
      ', '.join(f'{thm}_chunk{j}' for j in range(len(pre))) + ']')
    o('  rfl')
    o('')
    o(f'end {ns}')
    open(path, 'w').write('\n'.join(L) + '\n')
    return p, len(pre), total


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'q8'
    log = open(f'lean_seed_data_{which}.log', 'w')

    def out(s):
        print(s)
        log.write(s + '\n')

    if which == 'q8':
        seed_q8(out)
    elif which in ('A6', 'B6'):
        seed_z12(out, which)
    elif which == 'z12':
        dA = seed_z12(out, 'A6')
        dB = seed_z12(out, 'B6')
        d3 = seed_z12_k3(out)
        emit_z12('../../lean/GJF/SeedZ12Data.lean', dA, dB, d3)
        out('wrote lean/GJF/SeedZ12Data.lean')
        for name, d, bl, tgt, thm, fn in (('Z12A', dA, dA['allb'], 24, 'fastR', 'CertZ12A'),
                                         ('Z12B', dB, dB['allb'], 24, 'fastR', 'CertZ12B'),
                                         ('Z12K3', d3, [], 24, 'fastI', 'CertZ12K3')):
            sLn = d['S'] if 'S' in d else list(range(d['n']))
            wexpr = 'WtF sL bL' if bl else 'WtF sL []'
            p_, nch, tot = emit_cert(f'../../lean/GJF/{fn}.lean', ['GJF.SeedZ12Data'], f'GJF.Ex.{name}',
                                     wexpr, 'tree', d['tree'], sLn, bl, tgt, thm)
            out(f'wrote lean/GJF/{fn}.lean: {tot} leaves, prefix {p_} steps, {nch} chunks')
    elif which == 'q8z3':
        d = seed_q8z3(out)
        emit_q8z3('../../lean/GJF/SeedQ8Z3Data.lean', d)
        out('wrote lean/GJF/SeedQ8Z3Data.lean')
