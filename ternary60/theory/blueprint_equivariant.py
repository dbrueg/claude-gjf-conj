"""Checks for notes/blueprint/equivariant-quadrupling.md (partial quadrupling Q_σ, its equivariance, and the
collapse of fixed codes). Stdlib only, plus the Rust binary (`rsigma`, `index`) for sums over codes of
dimension > 12.

Part 1 (Def 1.4, Lemma 1.5): tetracode placements. The self-dual codes in F_3^4 are exactly the [4,2,3]
        codes; there are 8, all monomial images of the standard tetracode; Mon(T) has order 48, meets the
        diagonal in ±1, maps onto S_4, has the element orders of GL_2(F_3), is self-normalising in 2^4:S_4;
        the 8 placements form two rulings of 4 (distinct placements in one ruling meet in 0).
Part 2 (Lemma 2.1, 2.2): Lemma A for all 8 placements, Lemma B for all 8 placements and all 3 splits,
        for every u ∈ F_3^4.
Part 3 (Prop 4.9, 4.10): which local actions admit an invariant placement: every signed cycle type of
        2^4:S_4; J-type actions and the explicit placement <(1,s,1,0),(0,s,2,2s')>; the two Q8 models;
        the 8 doubled actions m ⊕ m on a step-one block; Mon(T) ∩ (split stabiliser).
Part 4 (Lemma 4.3, 4.7): the extension g ↦ ĝ on random block-structured signed permutations: homomorphism,
        (−1)^ = −1, commutes with both Hadamard layers, cycle lengths and cycle sign products inherited.
Part 5 (Thm 3.3): Q_σ for arbitrary linear E (not self-dual), arbitrary placements and splits:
        F(Q_σ(E)) = R_σ(E) and R_σ''(Q_σ(E)) = R_σ(E) for every subset of step-one blocks; Q_σ(E)
        self-dual when E is.
Part 6 (Thm 5.5, Cor 5.6, 5.7, Rem 5.8): the collapse identity c(Q_σ(E)^ĥ) = H̄₂H̄₁(D ⊕ T̄₁ ⊕ T̄₂) as
        subspaces, on the Z/12 seed (after the sign normalisation of h, two chain steps, n = 72, 144) and
        on the Q8×Z/3 seed (one step, n = 144); T_h = R_σ̄(D) numerically; the R-collapse pitfall.
Part 7 (Lemma 4.11, Table 4.12): local types of the block stabilisers at every stage of the J-, Z/12-, Q8-
        and Q8×Z/3-chains; invariant placements exist at every stage and the types repeat.
Part 8 (§6 table): size of a naive certificate for R_σ(seed) (rank of the seed on the singletons of σ).
"""
import itertools, os, random, sys, time
from collections import Counter
from existence_common import TETRA, GOLAY, PHI, span, rref, dot, f, rust_index, HERE
from existence_quadruple import R as R_py
from existence_hadamard import hadamard
from ternary import random_self_dual
from mainq_common import (mono_apply, mono_mul, mono_id, mono_neg, mono_pow, mono_order, cycle_type, closure,
                          is_aut, fixed_code, rust_R, read_code)
from mainq_equivariant import placement_on, extend, choose_splits, check_stable, block_image

LAM = (0, -2, 0, 0, 1)
F4 = list(itertools.product(range(3), repeat=4))
MON4 = [(p, s) for p in itertools.permutations(range(4)) for s in itertools.product((1, -1), repeat=4)]
SPLITS = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
CODES = os.path.join(HERE, "..", "codes")


def wt(v):
    return sum(1 for a in v if a)


def fspan(rows, n):
    return frozenset(span(rows, n)) if rows else frozenset([tuple([0] * n)])


def img(g, S):
    return frozenset(mono_apply(g, v) for v in S)


def basis_of(S):
    return rref([list(v) for v in S if any(v)])


# ------------------------------------------------------------------ Part 1

def part1():
    nonzero = [v for v in F4 if any(v)]
    subs = set()
    for a in nonzero:
        for b in nonzero:
            S = fspan([a, b], 4)
            if len(S) == 9:
                subs.add(S)
    sd = {S for S in subs if all(dot(x, y) == 0 for x in S for y in S)}
    mds = {S for S in subs if all(wt(x) == 3 for x in S if any(x))}
    T0 = fspan(TETRA, 4)
    orbit = {img(g, T0) for g in MON4}
    print(f"1 2-dim subspaces of F_3^4: {len(subs)}; self-dual: {len(sd)}; [4,2,3]: {len(mds)}; equal sets: {sd == mds}; "
          f"= monomial orbit of the standard tetracode: {orbit == sd}")
    mon = [g for g in MON4 if img(g, T0) == T0]
    orders = Counter(mono_order(g) for g in mon)
    diag = [g for g in mon if g[0] == (0, 1, 2, 3)]
    permimg = {g[0] for g in mon}

    def conj(x, g):
        xi = next(y for y in MON4 if mono_mul(x, y) == mono_id(4))
        return mono_mul(mono_mul(x, g), xi)
    monset = set(mon)
    normaliser = [x for x in MON4 if all(conj(x, g) in monset for g in mon)]
    P = sorted(sd, key=lambda S: sorted(S))
    stabs = {frozenset(g for g in MON4 if img(g, T) == T) for T in P}
    inter = Counter(len(A & B) for A, B in itertools.combinations(P, 2))
    # rulings: graph "meet in 0" on the 8 placements
    comp, seen = [], set()
    for T in P:
        if T in seen:
            continue
        c = {T} | {U for U in P if len(T & U) == 1}
        seen |= c; comp.append(len(c))
    print(f"1 |Mon(T)| = {len(mon)}; Mon(T) ∩ diagonal = {len(diag)} elements (±1); permutation image {len(permimg)} = |S_4|; "
          f"element orders {dict(sorted(orders.items()))} (GL_2(F_3): 1:1, 2:13, 3:8, 4:6, 6:8, 8:12)")
    print(f"1 normaliser of Mon(T) in 2^4:S_4 has order {len(normaliser)}; distinct stabilisers of the 8 placements: {len(stabs)}; "
          f"|T∩T'| over pairs: {dict(sorted(inter.items()))} (1 = meet in 0, 3 = meet in a line); rulings (classes of 'meet in 0'): {comp}")
    return P


# ------------------------------------------------------------------ Part 2

def psi2(a, b):
    return PHI[(a + b) % 3] * PHI[(a - b) % 3]


def kappa(a, b):
    return ((a + b) % 3 != 0) + ((a - b) % 3 != 0)


def lemA(T, u):
    tot = 0
    for t in T:
        p = 1
        for i in range(4):
            p *= psi2(u[i], t[i])
        tot += p
    return tot


def lemB(T, u, sp):
    return sum(LAM[sum(kappa(u[i], t[i]) for i in sp[0])] * LAM[sum(kappa(u[i], t[i]) for i in sp[1])] for t in T)


def part2(P):
    okA = sum(lemA(T, u) == LAM[wt(u)] for T in P for u in F4)
    okB = sum(lemB(T, u, sp) == LAM[wt(u)] for T in P for u in F4 for sp in SPLITS)
    okk = all(kappa(a, b) == wt(((a + b) % 3, (a - b) % 3)) and
              (psi2(a, b) != 0) == ((a != 0) != (b != 0)) for a in range(3) for b in range(3))
    print(f"2 Lemma A: {okA}/{8 * 81} (placement, u); Lemma B: {okB}/{8 * 3 * 81} (placement, split, u); "
          f"κ = weight of (a+b, a−b) and ψ ≠ 0 ⇔ exactly one of a, b nonzero: {okk}")


# ------------------------------------------------------------------ Part 3

def signed_type(g):
    p, s = g
    seen, out = set(), []
    for i in range(len(p)):
        if i in seen:
            continue
        L, j, sg = 0, i, 1
        while j not in seen:
            seen.add(j); sg *= s[j]; j = p[j]; L += 1
        out.append((L, '+' if sg == 1 else '-'))
    return tuple(sorted(out, reverse=True))


def inv_count(H, P):
    return sum(1 for T in P if all(img(g, T) == T for g in H))


def part3(P):
    cls = {}
    for g in MON4:
        cls.setdefault(signed_type(g), set()).add(inv_count([g], P))
    rows = [f"{''.join(f'{L}{s}' for L, s in t)}:{sorted(c)}" for t, c in sorted(cls.items())]
    print("3 signed cycle type : #placements preserved (constant on each class):  " + "  ".join(rows))
    # J-type
    res = []
    for s, s2 in itertools.product((1, -1), repeat=2):
        J = ((1, 0, 3, 2), (s, -s, s2, -s2))
        assert mono_mul(J, J) == mono_neg(4)
        Tf = fspan([[1, s % 3, 1, 0], [0, s % 3, 2, (2 * s2) % 3]], 4)
        res.append((s, s2, inv_count([J], P), img(J, Tf) == Tf and Tf in P))
    print("3 J-type J(e0)=s e1, J(e1)=−s e0, J(e2)=s' e3, J(e3)=−s' e2: (s, s', #invariant placements, "
          f"<(1,s,1,0),(0,s,2,2s')> invariant) = {res}")
    T0 = fspan(TETRA, 4)
    lean = [(s, s2) for s, s2 in itertools.product((1, -1), repeat=2)
            if img(((1, 0, 3, 2), (s, -s, s2, -s2)), T0) == T0]
    from mainq_jchain import J as JG
    Jb = (JG[0][:4], JG[1][:4])
    print(f"3 the fixed tetracode Tfin = <(1,1,1,0),(0,1,2,1)> of lean/GJF/Existence.lean is J_(s,s')-invariant only for "
          f"(s, s') ∈ {lean}; the J-chain's J acts on block (0,1,2,3) as {Jb}, and Tfin is invariant under it: "
          f"{img(Jb, T0) == T0}")
    # Q8 models
    from mainq_q8chain import q8
    from mainq_morita import q8_gens
    J4, K4 = q8(4)
    Jm, Km = q8_gens(1)
    Q1 = closure([J4, K4], 4); Q2 = closure([Jm, Km], 4)
    print(f"3 Q8-regular: model of mainq_q8chain (|Q8| = {len(Q1)}): {inv_count(Q1, P)} invariant placements; "
          f"Morita model (|Q8| = {len(Q2)}): {inv_count(Q2, P)}")
    # doubled actions on (p, q, p*, q*)
    out = []
    for pp in ((0, 1), (1, 0)):
        for s0, s1 in itertools.product((1, -1), repeat=2):
            g = ((pp[0], pp[1], 2 + pp[0], 2 + pp[1]), (s0, s1, s0, s1))
            m = (pp, (s0, s1))
            kind = ("id" if pp == (0, 1) and s0 == s1 == 1 else "−1" if pp == (0, 1) and s0 == s1 == -1 else
                    "diag(±1,∓1)" if pp == (0, 1) else "swap, m²=−1" if s0 * s1 == -1 else "swap, m²=+1")
            out.append(f"{kind} {m}: {inv_count([g], P)}")
    print("3 doubled action m ⊕ m on a step-one block (p,q,p*,q*): #invariant placements:  " + ";  ".join(out))
    W = [g for g in MON4 if {frozenset(g[0][i] for i in pr) for pr in SPLITS[0]} == {frozenset(pr) for pr in SPLITS[0]}]
    inter = []
    for T in P:
        H = [g for g in W if img(g, T) == T]
        inter.append((len(H), tuple(sorted(Counter(mono_order(g) for g in H).items()))))
    print(f"3 split stabiliser W (order {len(W)}): Mon(T) ∩ W for the 8 placements: {Counter(inter)} "
          "(order 16, element orders of the semidihedral group SD16)")


# ------------------------------------------------------------------ Part 4

def had_vec(v, pairs):
    w = list(v)
    for i, j in pairs:
        w[i], w[j] = (v[i] + v[j]) % 3, (v[i] - v[j]) % 3
    return w


def layout(m, blocks):
    """mate1, step-one blocks (p, p*, q, q*), mate2 for Q_σ on [m] with σ = blocks (p, q, k, l)."""
    b = len(blocks); n1 = m + 4 * b
    mate1 = {blocks[j][i]: m + 4 * j + i for j in range(b) for i in range(4)}
    B1 = []
    for p_, q_, k_, l_ in blocks:
        B1 += [(p_, mate1[p_], q_, mate1[q_]), (k_, mate1[k_], l_, mate1[l_])]
    mate2 = {B1[r][i]: n1 + 4 * r + i for r in range(2 * b) for i in range(4)}
    return mate1, B1, mate2, n1, m + 12 * b


def cycle_data(g, i):
    p, s = g
    L, j, sg = 0, i, 1
    while True:
        sg *= s[j]; j = p[j]; L += 1
        if j == i:
            return L, sg


def part4(rng):
    m = 12
    blocks = [(0, 1, 2, 3), (4, 5, 6, 7)]
    mate1, B1, mate2, n1, n = layout(m, blocks)
    gens = [((1, 0) + tuple(range(2, 12)), (1,) * 12),                                   # swap in a pair
            ((2, 3, 0, 1) + tuple(range(4, 12)), (1,) * 12),                              # swap the pairs
            ((4, 5, 6, 7, 0, 1, 2, 3) + tuple(range(8, 12)), (1,) * 12),                  # swap the blocks
            (tuple(range(8)) + (9, 10, 11, 8), (1,) * 12)]                                # singletons
    for i in range(12):
        gens.append((tuple(range(12)), tuple(-1 if j == i else 1 for j in range(12))))  # signs

    def rnd():
        g = mono_id(12)
        for _ in range(12):
            g = mono_mul(rng.choice(gens), g)
        return g

    def ext(g):
        return extend(extend(g, mate1, m, n1), mate2, n1, n)
    ok_hom = ok_had = ok_cyc = 0
    N = 300
    for _ in range(N):
        g, h = rnd(), rnd()
        ok_hom += ext(mono_mul(g, h)) == mono_mul(ext(g), ext(h))
        G = ext(g)
        v = [rng.randrange(3) for _ in range(n)]
        good = True
        for pairs in (list(mate1.items()), list(mate2.items())):
            good &= had_vec(mono_apply(G, v), pairs) == list(mono_apply(G, had_vec(v, pairs)))
        ok_had += good
        good = True
        for x in mate1:
            for y in (mate1[x], mate2[x], mate2[mate1[x]]):
                good &= cycle_data(G, y) == cycle_data(g, x)
        ok_cyc += good
    ok_neg = ext(mono_neg(12)) == mono_neg(n)
    print(f"4 random block-structured g, h on m = 12 (2 blocks, 4 singletons; n = {n}): ext(gh) = ext(g)ext(h) {ok_hom}/{N}; "
          f"ĝ commutes with H₁ and H₂ {ok_had}/{N}; cycle length and sign product of x*, x**, x*** = those of x {ok_cyc}/{N}; "
          f"(−1)^ = −1 {ok_neg}")


# ------------------------------------------------------------------ Part 5

def quad_general(E, m, blocks, P1, P2):
    """Q_σ(E) with arbitrary linear E (rows), blocks (p,q,k,l) split {p,q},{k,l}, placements P1[j] on
    (p*,q*,k*,l*) and P2[r] on B1[r]** (order of B1[r]); returns rows (not reduced), n, B1, mate2."""
    mate1, B1, mate2, n1, n = layout(m, blocks)
    rows = [list(r) + [0] * (n - m) for r in E]
    for j, T in enumerate(P1):
        for t in basis_of(T):
            v = [0] * n
            for i in range(4):
                v[mate1[blocks[j][i]]] = t[i]
            rows.append(v)
    for r, T in enumerate(P2):
        for t in basis_of(T):
            v = [0] * n
            for i in range(4):
                v[mate2[B1[r][i]]] = t[i]
            rows.append(v)
    rows = [had_vec(had_vec(v, list(mate1.items())), list(mate2.items())) for v in rows]
    return rows, n, B1, mate2


def refine_blocks(B1, mate2, subset, splits):
    out = []
    for r, sp in zip(subset, splits):
        B = B1[r]
        (a, b), (c, d) = sp
        w, x, y, z = B[a], B[b], B[c], B[d]
        out += [(w, mate2[w], x, mate2[x]), (y, mate2[y], z, mate2[z])]
    return out


def part5(P, rng):
    cases = okF = okR = okSD = 0
    nsd = 0
    for trial in range(60):
        selfd = trial % 5 == 0
        m = 8 if selfd else rng.choice((6, 8))
        if selfd:
            E, _ = random_self_dual(8, rng)
        else:
            k = rng.choice((1, 2, 3))
            E = rref([[rng.randrange(3) for _ in range(m)] for _ in range(k)])
        perm = list(range(m)); rng.shuffle(perm)
        blocks = [tuple(perm[:4])]
        P1 = [rng.choice(P)]
        P2 = [rng.choice(P) for _ in range(2)]
        rows, n, B1, mate2 = quad_general(E, m, blocks, P1, P2)
        Q = rref(rows)
        assert len(Q) == len(E) + 6
        QW = span(Q, n)
        r0 = R_py(span(E, m), blocks, m)
        cases += 1
        okF += sum(f(x) for x in QW) == r0
        good = True
        for subset in ([], [0], [1], [0, 1]):
            sps = [rng.choice(SPLITS) for _ in subset]
            good &= R_py(QW, refine_blocks(B1, mate2, subset, sps), n) == r0
        okR += good
        if selfd:
            nsd += 1
            okSD += len(Q) == n // 2 and all(dot(a, b) == 0 for a in Q for b in Q)
    print(f"5 random (E, σ, placements, splits), m ∈ {{6, 8}}, b = 1 (E linear, not self-dual except every 5th): "
          f"F(Q_σ(E)) = R_σ(E) {okF}/{cases}; R_σ''(Q_σ(E)) = R_σ(E) for all 4 subsets 𝓑 with random splits {okR}/{cases}; "
          f"Q_σ(E) self-dual for self-dual E {okSD}/{nsd}")


# ------------------------------------------------------------------ equivariant Q with its layout

def quad_full(E, m, blocks, gens, refine="orbit0"):
    """As mainq_equivariant.quad_eq, but also returns the layout and the placements used."""
    G = closure(gens, m)
    assert check_stable(G, blocks)
    mate1, B1, mate2, n1, n = layout(m, blocks)
    gens1 = [extend(g, mate1, m, n1) for g in gens]
    G1 = closure(gens1, n1)
    b = len(blocks)
    new1 = [tuple(mate1[blocks[j][i]] for i in range(4)) for j in range(b)]
    T1 = placement_on(G1, new1, n1)                      # 2 rows per new block, in the order of new1
    rows1 = [list(r) + [0] * (4 * b) for r in E] + T1
    rows1 = hadamard(rows1, list(mate1.items()))
    gens2 = [extend(g, mate2, n1, n) for g in gens1]
    G2 = closure(gens2, n)
    new2 = [tuple(mate2[B1[r][i]] for i in range(4)) for r in range(2 * b)]
    T2 = placement_on(G2, new2, n)
    rows = [list(r) + [0] * (8 * b) for r in rows1] + T2
    rows = hadamard(rows, list(mate2.items()))
    idx = {frozenset(B): t for t, B in enumerate(B1)}
    orb = sorted({idx[frozenset(block_image(g, B1[0])[0])] for g in G1})
    chosen = choose_splits(G1, [B1[r] for r in orb])
    newblocks = []
    for w, x, y, z in chosen:
        newblocks += [(w, mate2[w], x, mate2[x]), (y, mate2[y], z, mate2[z])]
    newblocks = choose_splits(G2, newblocks)
    T1 = [[r[:n1] + [0] * (n - n1) for r in T1[2 * j:2 * j + 2]] for j in range(b)]
    T2 = [T2[2 * r:2 * r + 2] for r in range(2 * b)]
    return dict(rows=rref(rows), n=n, n1=n1, mate1=mate1, mate2=mate2, B1=B1, new1=new1, new2=new2,
                T1=T1, T2=T2, gens1=gens1, gens2=gens2, G1=G1, G2=G2, newblocks=newblocks, refined=orb)


# ------------------------------------------------------------------ Part 6

def orbit_map(h, n):
    reps, orb = [], {}
    for i in range(n):
        if i not in orb:
            o = [i, h[0][i], h[0][h[0][i]]]
            assert h[0][o[2]] == i and len(set(o)) == 3, "h must be fixed-point-free of order 3"
            for x in o:
                orb[x] = len(reps)
            reps.append(i)
    return reps, orb


def in_span(B, v):
    return len(rref(B + [list(v)])) == len(rref(B)) if B else not any(v)


def collapse_check(E, m, blocks, gens, hpick, label):
    """Q_σ(E) equivariantly; verify c(Q^ĥ) = H̄₂H̄₁(D ⊕ T̄₁ ⊕ T̄₂) (Theorem 5.4) and return the data."""
    t0 = time.time()
    q = quad_full(E, m, blocks, gens)
    n = q["n"]; rows = q["rows"]
    h_old, h_new = hpick(gens), hpick(q["gens2"])
    assert all(x == 1 for x in h_new[1]), "h must be a permutation (normalise signs first)"
    reps, orb = orbit_map(h_new, n)
    N = len(reps)
    Fx = fixed_code(rows, n, h_new)
    W = rref([[v[r] for r in reps] for v in Fx])
    FxE = fixed_code(E, m, h_old)
    D_emb = []
    for v in FxE:
        w = [0] * N
        for x in range(m):
            w[orb[x]] = v[x]
        D_emb.append(w)
    D_emb = rref(D_emb) if D_emb else []
    p1 = sorted({(orb[x], orb[y]) for x, y in q["mate1"].items()})
    p2 = sorted({(orb[x], orb[y]) for x, y in q["mate2"].items()})
    Wp = hadamard(hadamard(W, p2), p1)
    # collapsed placements, one per ĥ-orbit of new blocks
    Tbar, seenb = [], set()
    for j, nb in enumerate(q["new1"]):
        key = frozenset(orb[x] for x in nb)
        if key in seenb:
            continue
        seenb.add(key)
        Tbar.append((sorted(key), [[0] * N for _ in range(2)]))
        for r, t in zip(Tbar[-1][1], q["T1"][j]):
            for x in nb:
                r[orb[x]] = t[x]
    nT1 = len(Tbar)
    for j, nb in enumerate(q["new2"]):
        key = frozenset(orb[x] for x in nb)
        if key in seenb:
            continue
        seenb.add(key)
        Tbar.append((sorted(key), [[0] * N for _ in range(2)]))
        for r, t in zip(Tbar[-1][1], q["T2"][j]):
            for x in nb:
                r[orb[x]] = t[x]
    nT2 = len(Tbar) - nT1
    ok_D = all(in_span(Wp, v) for v in D_emb)
    ok_T = all(in_span(Wp, v) for _, rs in Tbar for v in rs)
    ok_tetra = all(len(set(fspan([[r[c] for c in cols] for r in rs], 4))) == 9 and
                   all(wt(x) == 3 for x in fspan([[r[c] for c in cols] for r in rs], 4) if any(x)) for cols, rs in Tbar)
    all_rows = D_emb + [v for _, rs in Tbar for v in rs]
    ok_dim = len(Wp) == len(D_emb) + 2 * (nT1 + nT2) == len(rref(all_rows))
    # collapsed block systems
    old_reps = sorted({orb[x] for x in range(m)})
    pos = {c: i for i, c in enumerate(old_reps)}
    D_old = rref([[v[c] for c in old_reps] for v in D_emb]) if D_emb else []
    sbar, seen = [], set()
    for bl in blocks:
        key = frozenset(orb[x] for x in bl)
        if key not in seen:
            seen.add(key); sbar.append(tuple(pos[orb[x]] for x in bl))
    sbar2, seen2 = [], set()
    for bl in q["newblocks"]:
        key = frozenset(orb[x] for x in bl)
        if key not in seen2:
            seen2.add(key); sbar2.append(tuple(orb[x] for x in bl))
    print(f"6 {label}: n = {n}, Q^ĥ collapsed: length {N}, dim {len(W)}; D = c(E^h): length {len(old_reps)}, dim {len(D_old)}; "
          f"D ⊂ H̄₁H̄₂(c(Q^ĥ)) {ok_D}; {nT1} + {nT2} collapsed placements inside {ok_T}, each a [4,2,3] code {ok_tetra}; "
          f"dimensions add up (direct sum = whole) {ok_dim}  [{time.time() - t0:.0f}s]", flush=True)
    return dict(q=q, W=W, N=N, D_old=D_old, sbar=sbar, sbar2=sbar2, orb=orb, reps=reps,
                ok=ok_D and ok_T and ok_tetra and ok_dim)


def sign_normalise(E, m, gens, hpick):
    """Diagonal d with d h d^{-1} a permutation (d_{p(i)} = s_i d_i along each 3-cycle)."""
    h = hpick(gens)
    d = [0] * m
    for i in range(m):
        if d[i] == 0:
            d[i] = 1
            j = i
            while h[0][j] != i:
                d[h[0][j]] = h[1][j] * d[j]; j = h[0][j]
    Dg = (tuple(range(m)), tuple(d))
    E2 = [list(mono_apply(Dg, r)) for r in E]
    gens2 = [mono_mul(Dg, mono_mul(g, Dg)) for g in gens]
    return E2, gens2, d


def synthetic(rng):
    """h = cyclic shift of three copies of 6 coordinates (block {0,1,2,3} + singletons {4,5} per copy)."""
    m = 18
    h = (tuple(6 * ((i // 6 + 1) % 3) + i % 6 for i in range(m)), (1,) * m)
    blocks = [(6 * c, 6 * c + 1, 6 * c + 2, 6 * c + 3) for c in range(3)]
    res = []
    for case in range(8):
        if case == 0:
            y = [1, 0, 0, 0, 1, 1]
            E = [y * 3]                                  # E = diag(<(1,0,0,0,1,1)>)
        else:
            gen = []
            for _ in range(rng.choice((1, 2, 3))):
                v = [rng.randrange(3) for _ in range(m)]
                for _ in range(3):
                    gen.append(v); v = list(mono_apply(h, v))
            E = rref(gen)
        q = quad_full(E, m, blocks, [h])
        hq = q["gens2"][0]
        Fx = fixed_code(q["rows"], q["n"], hq)
        Th = sum(f(x) for x in span(Fx, q["n"])) if Fx else 0
        FxE = fixed_code(E, m, h)
        D = [[v[j] for j in range(6)] for v in FxE]
        RD = R_py(span(D, 6), [(0, 1, 2, 3)], 6) if D else 0
        naive = R_py(span(FxE, m), blocks, m) if FxE else 0
        res.append((Th, RD, naive))
    ok = sum(a == b for a, b, _ in res)
    bad = sum(b != c for _, b, c in res)
    print(f"6 synthetic h-invariant E (m = 18, σ = one h-orbit of 3 blocks, 6 singletons; case 0: E = diag<(1,0,0,0,1,1)>): "
          f"(T_h(Q_σ(E)), R_σ̄(D), Σ_{{E^h}} w_σ) = {res}; T_h = R_σ̄(D) {ok}/{len(res)}; naive R-collapse differs in {bad}", flush=True)


def part6():
    from mainq_z12chain import g36, SIGMA_A
    # --- Z/12 seed, h = g^4
    E = read_code(os.path.join(CODES, "z12seed_len36_3.txt")); m = 36
    g = g36()
    h4 = lambda gs: mono_pow(gs[0], 4)
    E2, gens2, d = sign_normalise(E, m, [g], h4)
    h2 = h4(gens2)
    eps = 1
    for x in d:
        eps *= x
    print(f"6 Z/12 seed: h = g⁴ has {sum(1 for s in h4([g])[1] if s == -1)} sign changes; after the diagonal change "
          f"(global sign Π d_i = {eps}) h is a permutation {all(s == 1 for s in h2[1])}, g' ∈ Aut(E') {is_aut(gens2[0], E2, m)}, "
          f"ord g' = {mono_order(gens2[0])}, g'⁶ = −1 {mono_pow(gens2[0], 6) == mono_neg(m)}", flush=True)
    G = closure(gens2, m)
    blocks = choose_splits(G, SIGMA_A)
    c1 = collapse_check(E2, m, blocks, gens2, h4, "Z/12 step 1 (36 → 72)")
    D, sbar = c1["D_old"], c1["sbar"]
    RD = rust_R(D, [list(b) for b in sbar], "bpD") if D else 0
    TQ = rust_R(c1["W"], [], "bpW")
    RW = rust_R(c1["W"], [list(b) for b in c1["sbar2"]], "bpW2")
    print(f"6   T_h(Q) = F(c(Q^ĥ)) = {TQ}; R_σ̄(D) = {RD}; R_σ̄''(c(Q^ĥ)) = {RW} (Lemma 5.8(2) on the collapsed chain)", flush=True)
    # the pitfall: R does not collapse
    FxE = fixed_code(E2, m, mono_pow(gens2[0], 4))
    wsum = R_py(span(FxE, m), blocks, m)
    print(f"6   on the seed: Σ_{{x∈E^h}} w_σ(x) = {wsum}, R_σ̄(D) = {RD} (equal here by accident; see the synthetic cases)",
          flush=True)
    q = c1["q"]
    c2 = collapse_check(q["rows"], q["n"], q["newblocks"], q["gens2"], h4, "Z/12 step 2 (72 → 144)")
    W2abs = abs(rust_index(c2["W"], "bpW3"))
    print(f"6   step 2: c(Q₂^ĥ) = Q_σ̄''(c(Q^ĥ)) as subspaces {c2['ok']}; |T_h(Q₂)| = |F(c(Q₂^ĥ))| = {W2abs} (ternary60 index); "
          f"collapsed code of step 1 equals D₁ of step 2: {rref(c2['D_old']) == rref(c1['W']) if len(c2['D_old']) == len(c1['W']) else 'dims differ'}",
          flush=True)
    # --- Q8 × Z/3 seed
    from mainq_morita import code_from_U, q8_gens, h_gen
    U = read_code(os.path.join(CODES, "q8z3_seed72.U.txt"))
    E = code_from_U(U, 18); m = 72
    J, K = q8_gens(18); H = h_gen(6)
    gens = [J, K, H]
    G = closure(gens, m)
    blocks = choose_splits(G, [tuple(range(4 * b, 4 * b + 4)) for b in range(6)])
    hq = lambda gs: gs[2]
    c3 = collapse_check(E, m, blocks, gens, hq, "Q8×Z/3 step 1 (72 → 144)")
    RD = rust_R(c3["D_old"], [list(b) for b in c3["sbar"]], "bpD8")
    W3abs = abs(rust_index(c3["W"], "bpW8"))
    print(f"6   R_σ̄(D) = {RD} (D length {len(c3['D_old'][0])}); |T_h(Q)| = |F(c(Q^ĥ))| = {W3abs} (ternary60 index)", flush=True)
    return dict(z12=(c1, c2), q8z3=c3, jz12=(E2, blocks, gens2))


# ------------------------------------------------------------------ Part 7

def local_image(G, blk):
    out = set()
    for g in G:
        p, s = g
        if {p[x] for x in blk} == set(blk):
            out.add((tuple(blk.index(p[x]) for x in blk), tuple(s[x] for x in blk)))
    return out


def classify(H):
    """Type of a local stabiliser image H (signed perms of the 4 positions (a,b,c,d), split {a,b},{c,d})."""
    idp = (0, 1, 2, 3)
    if all(g[0] == idp and len(set(g[1])) == 1 for g in H):
        return "scalar" if len(H) == 2 else "trivial"
    neg = (idp, (-1,) * 4)
    sq = lambda g: mono_mul(g, g)
    non = [g for g in H if g[0] != idp]
    if len(H) == 4 and neg in H and all(sq(g) == neg for g in non):
        pr = non[0][0]
        return "J(pairs fixed)" if pr in ((1, 0, 3, 2),) else "J(pairs swapped)" if pr in ((2, 3, 0, 1), (3, 2, 1, 0)) else "J(other)"
    if len(H) == 8 and neg in H and all(sq(g) == neg for g in non) and len({g[0] for g in H}) == 4:
        return "Q8-regular"
    return f"other(|H|={len(H)})"


def chain_types(label, E, m, blocks, gens, steps):
    t0 = time.time()
    lines = []
    for st in range(steps):
        G = closure(gens, m)
        tb = Counter((classify(local_image(G, bl)), inv_count(list(local_image(G, bl)), PLACE) > 0) for bl in blocks)
        q = quad_full(E, m, blocks, gens)
        ts = Counter((classify(local_image(q["G1"], B)), inv_count(list(local_image(q["G1"], B)), PLACE) > 0)
                     for B in q["B1"])
        auts = all(is_aut(g, q["rows"], q["n"]) for g in q["gens2"])
        lines.append(f"n={m}: b={len(blocks)} σ-blocks {dict(tb)}; step-one blocks {dict(ts)}; refined {len(q['refined'])} "
                     f"→ b''={len(q['newblocks'])}; gens ∈ Aut(Q) (n={q['n']}) {auts}")
        E, m, blocks, gens = q["rows"], q["n"], q["newblocks"], q["gens2"]
    G = closure(gens, m)
    tb = Counter((classify(local_image(G, bl)), inv_count(list(local_image(G, bl)), PLACE) > 0) for bl in blocks)
    lines.append(f"n={m}: b={len(blocks)} σ-blocks {dict(tb)}")
    print(f"7 {label}  [{time.time() - t0:.0f}s]\n      " + "\n      ".join(lines), flush=True)


def part7():
    from mainq_jchain import J as JG, BLOCK
    from mainq_z12chain import g36, SIGMA_A
    from mainq_q8chain import q8
    from mainq_morita import code_from_U, q8_gens, h_gen
    G = closure([JG], 12)
    chain_types("J-chain (Golay, J):", GOLAY, 12, choose_splits(G, [BLOCK]), [JG], 3)
    E = read_code(os.path.join(CODES, "z12seed_len36_3.txt"))
    g = g36()
    chain_types("Z/12 chain A (seed 3, σ₃):", E, 36, choose_splits(closure([g], 36), SIGMA_A), [g], 2)
    E = read_code(os.path.join(CODES, "q8chain_len24.txt"))
    J, K = q8(24)
    chain_types("Q8 chain (q8chain_len24):", E, 24, choose_splits(closure([J, K], 24), [(9, 8, 11, 10), (13, 12, 15, 14)]),
                [J, K], 2)
    U = read_code(os.path.join(CODES, "q8z3_seed72.U.txt"))
    E = code_from_U(U, 18)
    J, K = q8_gens(18); H = h_gen(6)
    chain_types("Q8×Z/3 chain (q8z3_seed72):", E, 72,
                choose_splits(closure([J, K, H], 72), [tuple(range(4 * b, 4 * b + 4)) for b in range(6)]), [J, K, H], 1)


def part8():
    """Size of a naive certificate for R_σ(seed): a word with w_σ ≠ 0 is ±1 on every singleton, so if E has rank r
    on the singletons, at most 2^r · 3^(dim E − r) words need to be evaluated (3^dim E by plain enumeration)."""
    from mainq_z12chain import SIGMA_A, SIGMA_B
    from mainq_morita import code_from_U
    U = read_code(os.path.join(CODES, "q8z3_seed72.U.txt"))
    seeds = [("Golay σ₁ (J-chain, Lean)", GOLAY, 12, [(0, 1, 2, 3)]),
             ("Golay σ₂ (Lean)", GOLAY, 12, [(0, 1, 2, 3), (4, 5, 6, 8)]),
             ("Z/12 seed σ₃", read_code(os.path.join(CODES, "z12seed_len36_3.txt")), 36, SIGMA_A),
             ("Z/12 seed σ₆", read_code(os.path.join(CODES, "z12seed_len36_3.txt")), 36, SIGMA_B),
             ("Q8 seed", read_code(os.path.join(CODES, "q8chain_len24.txt")), 24, [(9, 8, 11, 10), (13, 12, 15, 14)]),
             ("Q8×Z/3 seed", code_from_U(U, 18), 72, [tuple(range(4 * b, 4 * b + 4)) for b in range(6)])]
    out = []
    for name, E, m, bl in seeds:
        inb = {x for b in bl for x in b}
        sing = [i for i in range(m) if i not in inb]
        k = len(rref(E)); r = len(rref([[row[i] for i in sing] for row in E]))
        out.append(f"{name}: dim {k}, {len(sing)} singletons, rank on singletons {r}, "
                   f"candidates 2^{r}·3^{k - r} ≈ {2 ** r * 3 ** (k - r):.2e} (plain 3^{k} ≈ {3 ** k:.2e})")
    print("8 certificate sizes for R_σ(seed):\n      " + "\n      ".join(out))


PLACE = None

if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        rng = random.Random(20260927)
        PLACE = part1()
        part2(PLACE)
        part3(PLACE)
        part4(rng)
        part5(PLACE, rng)
        synthetic(rng)
        part6()
        part7()
        part8()
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
