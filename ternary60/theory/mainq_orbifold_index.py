"""Checks for notes/orbifold-index.md (Theorem O: the index of the orbifolds used for the Main Question).

Part 1 (Lemma 2.1, abstract groups). For G = ℤ/m (m = 2, 3, 4, 6, 12), Q₈ and Q₈ × ℤ/3:
        - (a) every commuting pair generates a cyclic subgroup;
        - (b) −1 is the unique involution and a power of every element of even order;
        - (c) the elements of odd order form a subgroup of order 3 (or 1), and it is central;
        - SL₂(ℤ/3) acts transitively on (ℤ/3)² ∖ 0 (used in §3.3);
        - the class-sum identity Σ_[g] (1/|C(g)|) Σ_{h∈C(g)} X(g,h) = (1/|G|) Σ_{commuting (g,h)} X(g,h) for
          class functions X (checked on the indicator of each G-orbit of commuting pairs). Theorem O no longer
          needs it; it is the form of the index formula in blueprint/orbifold-foundations.md Prop 5.6.
Part 2 (Lemmas 1.2, 3.2, 3.3, on the actual codes and groups). For each code: self-dual (rank n/2 and all
        generator rows pairwise orthogonal), generators in Aut(C). For every element g of the group:
        - N₋(g) := #{i : s_i = −1} is even, i.e. the Majorana layer ε(g) = Π s_i is 1 (Lemma 1.2);
        - if g ∉ {±1}, the underlying permutation of g has no fixed point (Lemma 3.2);
        - if g has even order m: g^{m/2} = −1; the eigenvalue phases, computed from the signed cycles
          (a cycle of length L with sign product s has θ = (j + [s = −1]/2)/L), are exactly the odd multiples
          s/m, each with multiplicity 2n/m; and the vacuum energy E_g = ¼ Σ θ(1−θ) equals
          n/24 + n/(12m²) exactly (Lemma 3.3);
        - if g has order 3: cycle shape 3^{n/3}.
        Codes and groups (the whole cyclic group ⟨g⟩ is checked even where only a subgroup is the orbifold
        group, e.g. ⟨g²⟩ at n = 72 and ⟨g⁴⟩ at n = 108; other chain lengths are covered by Lemma 3.2):
        - J-chain n = 48: ⟨J⟩;
        - ℤ/12-chains n = 72, 108, 144: ⟨g⟩, g of order 12;
        - Q₈-chain n = 96: Q₈;
        - Q₈ × ℤ/3 seed n = 72 and chain n = 144, 288.
        Generators are read from the space-separated files jchain_len<n>.gens.txt, z12chain_len<n>.gens.txt
        (written by mainq_gens_files.py from the older separator-less .J.txt/.g.txt files) and
        q8z3_chain_len<n>.gens.txt, and are checked to be automorphisms of the code.
Part 3 (the vanishing table, §3). For each group and each class [g] the script lists how the proof disposes
        of it: even order (no Ramond ground states, §3.1); g = 1 (the untwisted terms Z_RR(1,x), §3.2);
        g of order 3 (Z_RR(g,x) by one S-transformation for x of even order, by an SL₂(ℤ)-orbit for x ∈ ⟨g⟩,
        §3.3). It reports whether the proof uses modular transformations for that group.
Runtime ≈ 2–3 min (the group closures and Aut checks on the long codes).
"""
import os, sys, itertools
from fractions import Fraction as Fr
from collections import Counter
from existence_common import rref, dot, HERE
from mainq_common import read_code, read_gens, is_aut, mono_mul, mono_neg, mono_id, closure
from mainq_morita import q8_gens, h_gen
import mainq_q8_anomaly as QA

CODES = os.path.join(HERE, "..", "codes")


# ------------------------------------------------------------------ Part 1: abstract groups
def cyclic_group(m):
    return list(range(m)), (lambda a, b: (a + b) % m), 0


def q8_group():
    return list(QA.Q8), QA.qmul, QA.ONE


def q8z3_group():
    els = [(q, a) for q in QA.Q8 for a in range(3)]
    return els, (lambda x, y: (QA.qmul(x[0], y[0]), (x[1] + y[1]) % 3)), (QA.ONE, 0)


GROUPS = (("ℤ/2", cyclic_group(2)), ("ℤ/3", cyclic_group(3)), ("ℤ/4", cyclic_group(4)), ("ℤ/6", cyclic_group(6)),
          ("ℤ/12", cyclic_group(12)), ("Q₈", q8_group()), ("Q₈×ℤ₃", q8z3_group()))


def gen_sub(gens, mul, e):
    S, frontier = {e}, [e]
    while frontier:
        x = frontier.pop()
        for g in gens:
            y = mul(x, g)
            if y not in S:
                S.add(y); frontier.append(y)
    return S


def order_of(x, mul, e):
    k, y = 1, x
    while y != e:
        y, k = mul(y, x), k + 1
    return k


def group_facts(name, G, mul, e):
    comm = [(g, h) for g in G for h in G if mul(g, h) == mul(h, g)]
    cyclic_ok = all(any(gen_sub([x], mul, e) == gen_sub([g, h], mul, e) for x in gen_sub([g, h], mul, e))
                    for g, h in comm)
    invol = [x for x in G if x != e and mul(x, x) == e]
    even = [x for x in G if order_of(x, mul, e) % 2 == 0]
    b_ok = len(invol) <= 1 and all(invol and invol[0] in gen_sub([x], mul, e) for x in even)
    odd = {x for x in G if order_of(x, mul, e) % 2 == 1}
    c_ok = (len(odd) in (1, 3) and gen_sub(list(odd), mul, e) == odd
            and all(mul(x, g) == mul(g, x) for x in odd for g in G))
    # class-sum identity for the indicator of each orbit of commuting pairs under simultaneous conjugation
    inv = {x: next(y for y in G if mul(x, y) == e) for x in G}
    conj = lambda x, g: mul(mul(x, g), inv[x])
    orbits, seen = [], set()
    for p in comm:
        if p not in seen:
            orb = {(conj(x, p[0]), conj(x, p[1])) for x in G}
            seen |= orb; orbits.append(orb)
    classes, cseen = [], set()
    for g in G:
        if g not in cseen:
            cl = {conj(x, g) for x in G}; cseen |= cl; classes.append(g)
    cs_ok = True
    for orb in orbits:
        lhs = sum(Fr(sum(1 for h in G if mul(g, h) == mul(h, g) and (g, h) in orb),
                     sum(1 for h in G if mul(g, h) == mul(h, g))) for g in classes)
        cs_ok &= lhs == Fr(len(orb), len(G))
    print(f"1 {name} (|G| = {len(G)}): (a) {len(comm)} commuting pairs, all generate cyclic subgroups {cyclic_ok}; "
          f"(b) unique involution, a power of every even-order element {b_ok}; (c) odd-order elements form a "
          f"central subgroup of order {len(odd)} {c_ok}; class-sum identity on {len(orbits)} pair-orbits {cs_ok}",
          flush=True)
    return cyclic_ok and b_ok and c_ok and cs_ok


def sl2_transitive():
    """SL₂(ℤ/3) (the image of SL₂(ℤ)) is transitive on (ℤ/3)² ∖ 0, acting on row vectors (a, b)γ."""
    mats = [(a, b, c, d) for a, b, c, d in itertools.product(range(3), repeat=4) if (a * d - b * c) % 3 == 1]
    orbit = {((0 * a + 1 * c) % 3, (0 * b + 1 * d) % 3) for a, b, c, d in mats}   # images of (0, 1)
    ok = len(mats) == 24 and orbit == {(x, y) for x in range(3) for y in range(3)} - {(0, 0)}
    print(f"1 SL₂(ℤ/3): order {len(mats)}, the orbit of (0,1) is all of (ℤ/3)² ∖ 0: {ok}", flush=True)
    return ok


# ------------------------------------------------------------------ Part 2: the codes
def gens_from(path, names):
    d = read_gens(path)
    return [d[x] for x in names]


def signed_cycles(g):
    p, s = g
    seen, out = set(), []
    for i in range(len(p)):
        if i not in seen:
            c, j, sg = [], i, 1
            while j not in seen:
                seen.add(j); c.append(j); sg *= s[j]; j = p[j]
            out.append((len(c), sg))
    return out


def phases(g):
    """Multiset of eigenvalue phases θ ∈ [0, 1) of g on ℝⁿ: a cycle of length L with sign product s has
    θ = (j + [s = −1]/2)/L, j = 0..L−1."""
    out = Counter()
    for L, sg in signed_cycles(g):
        shift = Fr(1, 2) if sg == -1 else Fr(0)
        for j in range(L):
            out[(Fr(j) + shift) / L] += 1
    return out


def mono_order(g, n):
    e, x, k = mono_id(n), g, 1
    while x != e:
        x, k = mono_mul(g, x), k + 1
    return k


def check_code(tag, C, gens, n):
    G = closure(gens, n)
    neg, one = mono_neg(n), mono_id(n)
    R = rref(C)
    sd = len(R) == n // 2 and all(dot(a, b) == 0 for i, a in enumerate(C) for b in C[i:])
    inv = all(is_aut(g, C, n) for g in gens)
    maj_ok = fpf_ok = even_ok = odd_ok = True
    n_even, margins = 0, set()
    for g in G:
        maj_ok &= sum(1 for x in g[1] if x == -1) % 2 == 0
        if g not in (one, neg):
            fpf_ok &= all(g[0][i] != i for i in range(n))
        m = mono_order(g, n)
        if m % 2 == 0:
            n_even += 1
            x = g
            for _ in range(m // 2 - 1):
                x = mono_mul(g, x)
            ph = phases(g)
            expected = Counter({Fr(s, m): 2 * n // m for s in range(1, m, 2)})
            E = sum(th * (1 - th) * c for th, c in ph.items()) / 4
            even_ok &= x == neg and ph == expected and E == Fr(n, 24) + Fr(n, 12 * m * m)
            margins.add((m, E - Fr(n, 24)))
        elif m == 3:
            odd_ok &= all(L == 3 for L, _ in signed_cycles(g))
    ok = sd and inv and maj_ok and fpf_ok and even_ok and odd_ok
    print(f"2 {tag}: n = {n}, |G| = {len(G)}; self-dual (rank n/2, rows orthogonal) {sd}; generators in Aut {inv}; "
          f"N₋(g) even for all g (ε = 1) {maj_ok}; underlying permutation fixed-point-free for all g ≠ ±1 {fpf_ok}; "
          f"all {n_even} even-order g: g^(m/2) = −1, phases = odd multiples of 1/m each 2n/m times, "
          f"E_g = n/24 + n/(12m²) {even_ok} (E_g − n/24 by order: "
          + ", ".join(f"m={m}: {d}" for m, d in sorted(margins)) + f"); order-3 elements of shape 3^(n/3) {odd_ok}",
          flush=True)
    return ok


def part2():
    allok = True
    C = read_code(os.path.join(CODES, "jchain_len48.txt"))
    allok &= check_code("J-chain jchain_len48 (⟨J⟩)", C, gens_from(os.path.join(CODES, "jchain_len48.gens.txt"), "J"), 48)
    for n in (72, 108, 144):
        C = read_code(os.path.join(CODES, f"z12chain_len{n}.txt"))
        allok &= check_code(f"ℤ/12-chain z12chain_len{n} (⟨g⟩, ord g = 12)", C,
                            gens_from(os.path.join(CODES, f"z12chain_len{n}.gens.txt"), "g"), n)
    gens = QA.chain_gens()
    C = read_code(os.path.join(CODES, "q8chain_len96.txt"))
    allok &= check_code("Q₈-chain q8chain_len96 (Q₈)", C, list(gens[96]), 96)
    C = read_code(os.path.join(CODES, "q8z3_seed72.txt"))
    J, K = q8_gens(18)
    allok &= check_code("Q₈×ℤ₃ seed q8z3_seed72", C, [J, K, h_gen(6)], 72)
    for n in (144, 288):
        C = read_code(os.path.join(CODES, f"q8z3_chain_len{n}.txt"))
        allok &= check_code(f"Q₈×ℤ₃ chain q8z3_chain_len{n}", C,
                            gens_from(os.path.join(CODES, f"q8z3_chain_len{n}.gens.txt"), "JKH"), n)
    return allok


# ------------------------------------------------------------------ Part 3: the vanishing table
def part3():
    ok = True
    for name, (G, mul, e) in GROUPS:
        cnt = Counter()
        for g in G:
            og = order_of(g, mul, e)
            for x in G:
                if mul(g, x) != mul(x, g):
                    continue
                ox = order_of(x, mul, e)
                if og % 2 == 0:
                    cnt["[g] even: no ground states"] += 1
                elif g == e:
                    cnt["(1,1): Index(C)" if x == e else ("(1,x) x even: no fixed maximal word" if ox % 2 == 0
                                                         else "(1,x) x of order 3: ζ·T_h")] += 1
                else:
                    cnt["(g,x) g order 3, x even: one S" if ox % 2 == 0 else "(g,x) inside ⟨h₃⟩: SL₂-orbit"] += 1
        modular = any(k.startswith("(g,x)") for k in cnt)
        print(f"3 {name}: " + "; ".join(f"{k} {v}" for k, v in sorted(cnt.items())) +
              f"; modular transformations needed: {modular}", flush=True)
        ok &= (not modular) == (name in ("ℤ/2", "ℤ/4", "Q₈"))
    return ok


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        a = all([group_facts(nm, *grp) for nm, grp in GROUPS]) and sl2_transitive()
        b = part2()
        c = part3()
        print(f"all checks pass: {a and b and c}", flush=True)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
