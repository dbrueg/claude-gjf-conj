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


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'q8'
    log = open(f'lean_seed_data_{which}.log', 'w')

    def out(s):
        print(s)
        log.write(s + '\n')

    {'q8': seed_q8}[which](out)
