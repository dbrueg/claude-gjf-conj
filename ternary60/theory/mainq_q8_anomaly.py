"""The 't Hooft anomaly of Q₈ acting on V_{Λ(C)} (notes/main-question.md §8).

Theorem 8.1: if Q₈ = <J, K> ⊂ Aut(C) has centre −1, the anomaly of its action on V_{Λ(C)} is
(n/4)·a = 3k·a with a := anomaly of Q₈ on 8 Majorana fermions in the real regular representation, and
8a = 0. So the action is non-anomalous when 8 | k.

Part 1 (the reduction to free fermions, on the Q₈-chain codes of mainq_q8chain.py): every coordinate orbit
        of Q₈ has size 4 and carries a Q₈-invariant tetracode; their sum C₀ is a Q₈-invariant self-dual code
        with the same coordinate action; Q₈ acts freely on the 8 nonzero words of each tetracode, so on the
        weight-1/2 space of V_{Λ(T)} ≅ V_{ℤ⁴} ≅ Fer(8) it acts by the regular character. Also: all 8 sign
        patterns of a Q₈ action on 4 coordinates admit an invariant tetracode.
Part 2 (consistency check by eta invariants, exact rational arithmetic): for chiral Majorana fermions in a
        real representation ρ, the anomaly evaluated on a spherical space form M = S³/Γ (Γ ⊂ SU(2),
        spin structure = character ε: Γ → ±1) is A_ρ = ½(η(ρ) − dim ρ·η(1)) mod 1, with the equivariant
        formula η(ρ) = −(1/|Γ|) Σ_{g≠1} ε(g) χ_ρ(g) / (2 − tr g)   (tr = trace in SU(2)).
        Calibration: one Majorana odd under ℤ/2 gives ±1/8 on RP³ (the Kitaev generator of ℤ/8).
        Output: A_ρ for ρ = χ_i, H (quaternionic), Reg on RP³, the lens spaces S³/<i>, S³/<j>, S³/<k>, and
        S³/Q₈; the k for which 3k·A_Reg vanishes on all of them (answer: 8 | k), and the cyclic restrictions
        (⟨−1⟩: 2 | k; ℤ/4: 4 | k), matching the anomaly clause "m | k" of GJF Thm 5.6.
"""
import itertools, os, sys
from fractions import Fraction as Fr
from existence_common import dot, rref, HERE
from mainq_common import mono_mul, mono_neg, mono_apply, closure, is_aut, read_code
from mainq_equivariant import PLACEMENTS
from mainq_q8chain import q8

# ------------------------------------------------------------------ quaternion group
# elements as unit quaternions (a, b, c, d) = a + b i + c j + d k
Q8 = [(s * x[0], s * x[1], s * x[2], s * x[3]) for s in (1, -1)
      for x in ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))]
ONE, MONE = (1, 0, 0, 0), (-1, 0, 0, 0)


def trace_su2(q):
    return 2 * q[0]                      # trace of a unit quaternion in the 2-dim complex rep


def char(name, q):
    """Real characters of Q₈: '1', 'chi_i', 'chi_j', 'chi_k', 'H' (4-dim quaternionic), 'Reg'."""
    if name == "1":
        return 1
    if name == "Reg":
        return 8 if q == ONE else 0
    if name == "H":
        return 4 if q == ONE else (-4 if q == MONE else 0)
    axis = {"chi_i": 1, "chi_j": 2, "chi_k": 3}[name]
    if q in (ONE, MONE) or q[axis] != 0:
        return 1
    return -1


def eta(group, eps, rho):
    s = Fr(0)
    for g in group:
        if g == ONE:
            continue
        s += Fr(eps(g) * char(rho, g), 1) / (2 - trace_su2(g))
    return -s / len(group)


def anomaly(group, eps, rho, dim):
    a = (eta(group, eps, rho) - dim * eta(group, eps, "1")) / 2
    return a - (a.numerator // a.denominator)


def qmul(p, q):
    a1, b1, c1, d1 = p; a2, b2, c2, d2 = q
    return (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2, a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
            a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2, a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)


def spin_structures(group):
    """All homomorphisms ε: Γ → ±1 (the spin structures on S³/Γ, Γ ⊂ SU(2))."""
    out = []
    for signs in itertools.product((1, -1), repeat=len(group)):
        e = dict(zip(group, signs))
        if all(e[qmul(a, b)] == e[a] * e[b] for a in group for b in group):
            out.append(lambda q, e=e: e[q])
    return out


def subgroup(gen):
    G = [ONE]; x = gen
    while x != ONE:
        G.append(x); x = qmul(x, gen)
    return G


def part2():
    DIMS = {"chi_i": 1, "chi_j": 1, "chi_k": 1, "H": 4, "Reg": 8}
    spaces = {"RP³ = S³/<−1>": subgroup(MONE), "S³/<i>": subgroup((0, 1, 0, 0)),
              "S³/<j>": subgroup((0, 0, 1, 0)), "S³/<k>": subgroup((0, 0, 0, 1)), "S³/Q₈": Q8}
    # calibration: ℤ/2 = <−1> acting by −1 on one Majorana (character −1 at g = −1)
    cal = []
    for e_m1 in (1, -1):
        eps = lambda q, e=e_m1: (e if q == MONE else 1)
        e_odd = -Fr(eps(MONE) * (-1)) / (2 - trace_su2(MONE)) / 2
        e_triv = -Fr(eps(MONE) * 1) / (2 - trace_su2(MONE)) / 2
        a = (e_odd - e_triv) / 2
        cal.append(a - (a.numerator // a.denominator))
    print(f"2 calibration: one Majorana odd under ℤ/2, on RP³ with its two spin structures: A = {cal} "
          f"(order 8: the Kitaev generator)", flush=True)
    table = {}
    for mname, G in spaces.items():
        row = []
        for eps in spin_structures(G):
            vals = {rho: anomaly(G, eps, rho, d) for rho, d in DIMS.items()}
            row.append(vals)
        table[mname] = row
        print(f"2 {mname}: " + "; ".join(
            "ε=" + str(tuple(eps(g) for g in G)) + ": " + ", ".join(f"A_{r} = {v[r]}" for r in DIMS)
            for eps, v in zip(spin_structures(G), row)), flush=True)
    good = [k for k in range(1, 49)
            if all((3 * k * v["Reg"]) % 1 == 0 for row in table.values() for v in row)]
    print(f"2 3k·A_Reg vanishes on all these space forms exactly for k ∈ {good} (1 ≤ k ≤ 48): i.e. 8 | k",
          flush=True)
    for name, cond in (("RP³ = S³/<−1>", 2), ("S³/<i>", 4)):
        ks = [k for k in range(1, 25) if all((3 * k * v["Reg"]) % 1 == 0 for v in table[name])]
        print(f"2   restriction to the cyclic subgroup of {name}: vanishes exactly for k ∈ {ks} "
              f"(= multiples of {cond}; GJF Thm 5.6: m | k with m = {cond})", flush=True)


def orbits(gens, n):
    G = closure(gens, n)
    seen, out = set(), []
    for i in range(n):
        if i not in seen:
            o = sorted({g[0][i] for g in G})
            seen.update(o); out.append(o)
    return out, G


def part1():
    neg4 = mono_neg(4); cnt = []
    for s in itertools.product((1, -1), repeat=4):
        for t in itertools.product((1, -1), repeat=4):
            J = ((1, 0, 3, 2), s); K = ((2, 3, 0, 1), t)
            if mono_mul(J, J) == neg4 and mono_mul(K, K) == neg4 and mono_mul(J, K) == mono_mul(neg4, mono_mul(K, J)):
                cnt.append(sum(all(mono_apply(J, w) in W and mono_apply(K, w) in W for w in W) for _, W in PLACEMENTS))
    print(f"1 Q₈ actions on 4 coordinates (J, K with J² = K² = −1, JK = −KJ): {len(cnt)} sign patterns, "
          f"invariant tetracodes per pattern: {sorted(set(cnt))}", flush=True)
    for n in (24, 48, 96):
        fn = os.path.join(HERE, "..", "codes", f"q8chain_len{n}.txt")
        C = read_code(fn)
        # recover the extended J, K by rebuilding the chain is unnecessary: q8(n) acts groupwise on the
        # seed coordinates, and the chain extends it; we recompute it with mainq_q8chain's construction
        J, K = CHAIN_GENS[n]
        assert is_aut(J, C, n) and is_aut(K, C, n)
        orbs, G = orbits([J, K], n)
        sizes = sorted({len(o) for o in orbs})
        C0 = []
        ok_inv = True; ok_free = True
        for o in orbs:
            # the restriction of J, K to the orbit, as signed permutations of positions 0..3
            pos = {x: i for i, x in enumerate(o)}
            loc = [((tuple(pos[g[0][x]] for x in o)), tuple(g[1][x] for x in o)) for g in (J, K)]
            inv = [rows for rows, W in PLACEMENTS if all(mono_apply(h, w) in W for h in loc for w in W)]
            ok_inv &= bool(inv)
            rows = inv[0]
            W = {tuple((a * x + b * y) % 3 for x, y in zip(rows[0], rows[1])) for a in range(3) for b in range(3)}
            Gl = closure(loc, 4)
            ok_free &= all(mono_apply(h, w) != w for h in Gl if h != ((0, 1, 2, 3), (1, 1, 1, 1)) for w in W if any(w))
            for r in rows:
                v = [0] * n
                for i, x in enumerate(o):
                    v[x] = r[i]
                C0.append(v)
        sd = len(rref(C0)) == n // 2 and all(dot(a, b) == 0 for a in C0 for b in C0)
        print(f"1 q8chain_len{n} (k = {n // 12}): centre −1 {mono_mul(J, J) == mono_neg(n)}; orbit sizes {sizes} "
              f"({len(orbs)} orbits = 3k); invariant tetracode on every orbit {ok_inv}; C₀ = their sum is "
              f"self-dual {sd} and Q₈-invariant {is_aut(J, C0, n) and is_aut(K, C0, n)}; Q₈ free on nonzero "
              f"tetracode words {ok_free}", flush=True)


def chain_gens():
    """Rebuild the Q₈ chain of mainq_q8chain.py to get the extended J, K at n = 24, 48, 96."""
    import random
    from mainq_q8chain import rand_group_code
    from mainq_equivariant import quad_eq, choose_splits
    from mainq_common import rust_R
    n = 24
    J, K = q8(n)
    out = {24: (J, K)}
    E = read_code(os.path.join(HERE, "..", "codes", "q8chain_len24.txt"))
    G = closure([J, K], n)
    blocks = None
    for g1, g2 in itertools.combinations(range(n // 4), 2):
        bl = choose_splits(G, [tuple(range(4 * g1, 4 * g1 + 4)), tuple(range(4 * g2, 4 * g2 + 4))])
        if bl is not None and abs(rust_R(E, bl, "q8a")) == 24:
            blocks = bl; break
    m, gens = n, [J, K]
    for _ in range(2):
        rows, nn, newb, g2 = quad_eq(E, m, blocks, gens, refine="orbit0")
        out[nn] = tuple(g2)
        E, m, blocks, gens = rows, nn, newb, g2
    return out


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        CHAIN_GENS = chain_gens()
        part1()
        part2()
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
