"""Equivariant partial quadrupling (notes/main-question.md §3).

Q_σ(E) (notes/ternary-code-index.md §5.1(f‴)) is built from E, tetracodes and coordinate-pair Hadamard
maps. If a finite group G of monomial maps preserves E and permutes the blocks of σ together with their
pair splits, then G extends to the new coordinates (a new coordinate follows its Hadamard partner, with
the same sign), and Q_σ(E) is G-invariant as soon as the tetracodes are placed G-equivariantly: on one
block per G-orbit, a placement invariant under the stabiliser; elsewhere its transport.

Blocks are 4-tuples (a, b, c, d) read with the pair split {a, b}, {c, d}.
"""
import itertools
from existence_common import TETRA, rref, dsum
from existence_hadamard import hadamard
from mainq_common import mono_apply, mono_mul, mono_id, closure, is_aut


def tetra_placements():
    """The 8 distinct monomial images of the tetracode in F_3^4, as (rows, frozenset of words)."""
    out = {}
    for perm in itertools.permutations(range(4)):
        for signs in itertools.product((1, -1), repeat=4):
            g = (perm, signs)
            rows = [list(mono_apply(g, r)) for r in TETRA]
            words = frozenset(tuple((a * x + b * y) % 3 for x, y in zip(rows[0], rows[1]))
                              for a in range(3) for b in range(3))
            out.setdefault(words, rows)
    return [(rows, words) for words, rows in out.items()]


PLACEMENTS = tetra_placements()


def block_image(g, blk):
    """Image of block blk under g: (target positions as a tuple of coordinates, signs)."""
    p, s = g
    return tuple(p[x] for x in blk), tuple(s[x] for x in blk)


def as_split(blk):
    return frozenset((frozenset(blk[:2]), frozenset(blk[2:])))


def check_stable(G, blocks):
    """G must permute the blocks and their splits."""
    by_set = {frozenset(b): b for b in blocks}
    for g in G:
        for b in blocks:
            img, _ = block_image(g, b)
            t = by_set.get(frozenset(img))
            if t is None or as_split(img) != as_split(t):
                return False
    return True


def choose_splits(G, blocksets):
    """Given G-permuted 4-sets, choose pair splits permuted by G (one per orbit, transported).
    Returns a list of 4-tuples, or None if some stabiliser fixes no split."""
    blocksets = [tuple(sorted(b)) for b in blocksets]
    idx = {frozenset(b): j for j, b in enumerate(blocksets)}
    chosen = [None] * len(blocksets)
    for j, b in enumerate(blocksets):
        if chosen[j] is not None:
            continue
        stab = [g for g in G if frozenset(block_image(g, b)[0]) == frozenset(b)]
        a = b[0]
        cands = []
        for partner in b[1:]:
            rest = [x for x in b if x not in (a, partner)]
            cands.append((a, partner, rest[0], rest[1]))
        # prefer splits whose two pairs are each fixed by the stabiliser (then refined blocks stay
        # stabilised), else splits preserved as a partition
        def ok(sp, strict):
            for g in stab:
                img = block_image(g, sp)[0]
                if strict and (frozenset(img[:2]) != frozenset(sp[:2])):
                    return False
                if as_split(img) != as_split(sp):
                    return False
            return True
        sp = next((c for c in cands if ok(c, True)), None) or next((c for c in cands if ok(c, False)), None)
        if sp is None:
            return None
        for g in G:
            img, _ = block_image(g, sp)
            t = idx[frozenset(img)]
            if chosen[t] is None:
                chosen[t] = img
    return chosen


def placement_on(G, newblocks, n):
    """Rows of a G-invariant tetracode sum on the given new 4-blocks (tuples of coordinates)."""
    idx = {frozenset(b): j for j, b in enumerate(newblocks)}
    rows_of = [None] * len(newblocks)
    for j, b in enumerate(newblocks):
        if rows_of[j] is not None:
            continue
        stab = [g for g in G if frozenset(block_image(g, b)[0]) == frozenset(b)]
        for prow, words in PLACEMENTS:
            full = [[0] * n for _ in prow]
            for r, pr in zip(full, prow):
                for i in range(4):
                    r[b[i]] = pr[i]
            fw = set()
            for x, y in itertools.product(range(3), repeat=2):
                fw.add(tuple((x * u + y * v) % 3 for u, v in zip(full[0], full[1])))
            if all(mono_apply(g, w) in fw for g in stab for w in fw):
                break
        else:
            raise ValueError("no stabiliser-invariant tetracode placement")
        for g in G:
            img, _ = block_image(g, b)
            t = idx[frozenset(img)]
            if rows_of[t] is None:
                rows_of[t] = [list(mono_apply(g, r)) for r in full]
    return [r for rs in rows_of for r in rs]


def extend(g, mate, n_old, n_new):
    """Extend monomial g on [n_old] to [n_new]: a new coordinate x* = mate[x] follows x."""
    p, s = list(g[0]) + [None] * (n_new - n_old), list(g[1]) + [None] * (n_new - n_old)
    for x, xs in mate.items():
        p[xs] = mate[p[x]]
        s[xs] = s[x]
    return (tuple(p), tuple(s))


def quad_eq(E, m, blocks, gens, refine=None):
    """Q_σ(E) with σ = blocks (4-tuples with splits), G = <gens> (monomial maps on [m], preserving E
    and σ). refine: list of step-1 block indices to refine (a G-stable set); their refinement splits
    are chosen G-equivariantly. Returns (rows, n, new blocks, extended gens)."""
    G = closure(gens, m)
    assert check_stable(G, blocks), "σ is not G-stable"
    b = len(blocks); n1 = m + 4 * b; n = m + 12 * b
    mate1 = {}
    for j, blk in enumerate(blocks):
        for i in range(4):
            mate1[blk[i]] = m + 4 * j + i
    gens1 = [extend(g, mate1, m, n1) for g in gens]
    G1 = closure(gens1, n1)
    new1 = [tuple(m + 4 * j + i for i in range(4)) for j in range(b)]
    T1 = placement_on(G1, new1, n1)
    rows1 = [list(r) + [0] * (4 * b) for r in E] + T1
    rows1 = hadamard(rows1, list(mate1.items()))
    B1 = []
    for p_, q_, k_, l_ in blocks:
        B1 += [(p_, mate1[p_], q_, mate1[q_]), (k_, mate1[k_], l_, mate1[l_])]
    mate2 = {}
    for r, blk in enumerate(B1):
        for i in range(4):
            mate2[blk[i]] = n1 + 4 * r + i
    gens2 = [extend(g, mate2, n1, n) for g in gens1]
    G2 = closure(gens2, n)
    new2 = [tuple(n1 + 4 * r + i for i in range(4)) for r in range(2 * b)]
    T2 = placement_on(G2, new2, n)
    rows = [list(r) + [0] * (8 * b) for r in rows1] + T2
    rows = hadamard(rows, list(mate2.items()))
    newblocks = []
    if refine == "orbit0":                     # the G-orbit of step-1 block 0
        refine = sorted({next(t for t, B in enumerate(B1) if frozenset(B) == frozenset(block_image(g, B1[0])[0]))
                         for g in G1})
    if refine:
        orb = set()
        for r in refine:
            for g in G1:
                img = frozenset(block_image(g, B1[r])[0])
                orb.add(next(t for t, B in enumerate(B1) if frozenset(B) == img))
        assert orb == set(refine), "refined set of step-1 blocks is not G-stable"
        chosen = choose_splits(G1, [B1[r] for r in refine])
        assert chosen is not None, "no equivariant refinement split"
        for w, x, y, z in chosen:
            newblocks += [(w, mate2[w], x, mate2[x]), (y, mate2[y], z, mate2[z])]
        newblocks = choose_splits(G2, newblocks)      # re-split so that stabilisers fix both pairs
    return rows, n, newblocks, gens2


def orbits_of_blocks(gens, blocks, n):
    G = closure(gens, n)
    idx = {frozenset(b): j for j, b in enumerate(blocks)}
    seen, orbs = set(), []
    for j, b in enumerate(blocks):
        if j in seen:
            continue
        o = sorted({idx[frozenset(block_image(g, b)[0])] for g in G})
        seen.update(o); orbs.append(o)
    return orbs
