"""Checks for notes/orbifold-index.md: the index of the orbifolds used for the Main Question.

Part 1 (group theory; Lemma 2.1 and the class-sum identity (1.2)). For G = ℤ/m (m = 2, 3, 4, 6, 12), Q₈ and
        Q₈ × ℤ/3, as abstract groups:
        - every commuting pair generates a cyclic subgroup;
        - every element of even order has the unique involution as a power;
        - the elements of odd order form the subgroup of order 3 (or 1);
        - Σ_[g] (1/|C(g)|) Σ_{h∈C(g)} X(g,h) = (1/|G|) Σ_{commuting (g,h)} X(g,h) for class functions X
          (checked with X = indicator of each G-orbit of commuting pairs).
Part 2 (Lemma 3.3, on the actual codes). For every element g of even order of the group acting on each code:
        - g is fixed-point-free on ℝⁿ (every signed cycle has sign product −1 on its fixed line... i.e. no
          eigenvalue 1);
        - some power of g is −1;
        - the twisted vacuum energy ρ_g = ¼ Σ θ(1−θ) (exact, from the signed cycles) exceeds c/24 = n/24.
        For elements of order 3: cycle shape 3^{n/3} (no fixed coordinate).
        Codes and groups:
        - J-chain n = 48: ⟨J⟩, m = 4;
        - ℤ/12-chains n = 72, 108, 144: ⟨g⟩, m = 12;
        - Q₈-chain n = 96: Q₈;
        - Q₈ × ℤ/3 seed n = 72 and chain n = 144, 288.
        The generator files jchain_len<n>.J.txt and z12chain_len<n>.g.txt write the permutation without
        separators; it is parsed back by backtracking and accepted only if it is a permutation that is an
        automorphism of the code.
Part 3 (the vanishing table). For each group, every commuting pair (g,h) ≠ (1,1) is classified by the reason
        its RR index vanishes: §3.1 (g of even order), §3.2 (g = 1), §3.3 (one S-transformation), §3.4
        (inside the order-3 subgroup, GJF). The script reports whether the proof uses modular
        transformations for that group.
"""
import os, sys, itertools
from fractions import Fraction as Fr
from existence_common import rref, HERE
from mainq_common import read_code, is_aut, mono_mul, mono_neg, mono_id, closure
from mainq_morita import q8_gens, h_gen, code_from_U
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
    c_ok = len(odd) in (1, 3) and gen_sub(list(odd), mul, e) == odd
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
        rhs = Fr(len(orb), len(G))
        cs_ok &= lhs == rhs
    print(f"1 {name} (|G| = {len(G)}): {len(comm)} commuting pairs, all generate cyclic subgroups {cyclic_ok}; "
          f"unique involution, a power of every even-order element {b_ok}; odd-order elements form a subgroup of "
          f"order {len(odd)} {c_ok}; class-sum identity on {len(orbits)} pair-orbits {cs_ok}", flush=True)
    return cyclic_ok and b_ok and c_ok and cs_ok


# ------------------------------------------------------------------ Part 2: the codes
def parse_perm(s, n):
    """Split a digit string into a permutation of 0..n−1 (backtracking); None if impossible."""
    used, out = [False] * n, []

    def rec(i):
        if i == len(s):
            return len(out) == n
        for L in (1, 2, 3):
            if i + L <= len(s) and (L == 1 or s[i] != "0"):
                v = int(s[i:i + L])
                if v < n and not used[v]:
                    used[v] = True; out.append(v)
                    if rec(i + L):
                        return True
                    used[v] = False; out.pop()
        return False
    sys.setrecursionlimit(10000)
    return tuple(out) if rec(0) else None


def read_gen_file(path, n, C):
    with open(path) as fh:
        rows = [ln.strip() for ln in fh if ln.strip()]
    p = parse_perm(rows[0], n)
    s = tuple(1 if ch == "1" else -1 for ch in rows[1])
    g = (p, s)
    assert p is not None and len(s) == n and is_aut(g, C, n), path
    return g


def read_gens_txt(path):
    d = {}
    with open(path) as fh:
        for ln in fh:
            key, vals = ln.split(":")
            d[key.strip()] = tuple(int(x) for x in vals.split())
    return [(d[f"{c} perm"], d[f"{c} sign"]) for c in "JKH"]


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


def rho_twisted(g):
    """(fixed-point-free?, ρ_g = ¼ Σ θ(1−θ)) from the signed cycles: a cycle of length L with sign product s
    has eigenvalues e^{2πiθ}, θ = (j + [s = −1]/2)/L, j = 0..L−1."""
    fpf, rho = True, Fr(0)
    for L, sg in signed_cycles(g):
        shift = Fr(1, 2) if sg == -1 else Fr(0)
        for j in range(L):
            th = (Fr(j) + shift) / L
            if th == 0:
                fpf = False
            rho += th * (1 - th) / 4
    return fpf, rho


def mono_order(g, n):
    e, x, k = mono_id(n), g, 1
    while x != e:
        x, k = mono_mul(g, x), k + 1
    return k


def check_code(tag, C, gens, n):
    G = closure(gens, n)
    neg = mono_neg(n)
    ok, worst, odd_ok, n_even = True, None, True, 0
    for g in G:
        m = mono_order(g, n)
        if m % 2 == 0:
            n_even += 1
            powers, x = set(), g
            for _ in range(m):
                powers.add(x); x = mono_mul(g, x)
            fpf, rho = rho_twisted(g)
            margin = rho - Fr(n, 24)
            ok &= fpf and neg in powers and margin > 0
            if worst is None or margin / n < worst[0]:
                worst = (margin / n, m)
        elif m == 3:
            odd_ok &= all(L == 3 for L, _ in signed_cycles(g))
    sd = len(rref(C)) == n // 2
    inv = all(is_aut(g, C, n) for g in gens)
    print(f"2 {tag}: n = {n}, |G| = {len(G)}, self-dual {sd}, generators in Aut {inv}; all {n_even} even-order elements "
          f"fixed-point-free with −1 as a power and ρ_g > n/24: {ok} (smallest margin (ρ_g − n/24)/n = "
          f"{worst[0]} at order {worst[1]}); order-3 elements have cycle shape 3^(n/3): {odd_ok}", flush=True)
    return ok and odd_ok and sd and inv


def part2():
    allok = True
    # J-chain, m = 4 (k = 4)
    C = read_code(os.path.join(CODES, "jchain_len48.txt"))
    allok &= check_code("J-chain jchain_len48 (⟨J⟩, m = 4)", C, [read_gen_file(os.path.join(CODES, "jchain_len48.J.txt"), 48, C)], 48)
    for n in (72, 108, 144):
        C = read_code(os.path.join(CODES, f"z12chain_len{n}.txt"))
        g = read_gen_file(os.path.join(CODES, f"z12chain_len{n}.g.txt"), n, C)
        allok &= check_code(f"ℤ/12-chain z12chain_len{n} (⟨g⟩, m = 12)", C, [g], n)
    gens = QA.chain_gens()
    C = read_code(os.path.join(CODES, "q8chain_len96.txt"))
    allok &= check_code("Q₈-chain q8chain_len96 (Q₈)", C, list(gens[96]), 96)
    C = read_code(os.path.join(CODES, "q8z3_seed72.txt"))
    J, K = q8_gens(18)
    allok &= check_code("Q₈×ℤ₃ seed q8z3_seed72", C, [J, K, h_gen(6)], 72)
    for n in (144, 288):
        C = read_code(os.path.join(CODES, f"q8z3_chain_len{n}.txt"))
        allok &= check_code(f"Q₈×ℤ₃ chain q8z3_chain_len{n}", C, read_gens_txt(os.path.join(CODES, f"q8z3_chain_len{n}.gens.txt")), n)
    return allok


# ------------------------------------------------------------------ Part 3: the vanishing table
def part3():
    ok = True
    for name, (G, mul, e) in (("ℤ/2", cyclic_group(2)), ("ℤ/3", cyclic_group(3)), ("ℤ/4", cyclic_group(4)),
                              ("ℤ/6", cyclic_group(6)), ("ℤ/12", cyclic_group(12)), ("Q₈", q8_group()),
                              ("Q₈×ℤ₃", q8z3_group())):
        cnt = {"(1,1)": 0, "§3.1 g even": 0, "§3.2 g = 1": 0, "§3.3 one S": 0, "§3.4 order-3 subgroup": 0}
        for g in G:
            for h in G:
                if mul(g, h) != mul(h, g):
                    continue
                og, oh = order_of(g, mul, e), order_of(h, mul, e)
                if g == e and h == e:
                    cnt["(1,1)"] += 1
                elif og % 2 == 0:
                    cnt["§3.1 g even"] += 1
                elif g == e:
                    cnt["§3.2 g = 1"] += 1
                elif oh % 2 == 0:
                    cnt["§3.3 one S"] += 1
                else:
                    cnt["§3.4 order-3 subgroup"] += 1
        modular = cnt["§3.3 one S"] + cnt["§3.4 order-3 subgroup"] > 0
        print(f"3 {name}: " + ", ".join(f"{k} {v}" for k, v in cnt.items()) +
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
        a = all([group_facts(nm, *grp) for nm, grp in
                 (("ℤ/2", cyclic_group(2)), ("ℤ/3", cyclic_group(3)), ("ℤ/4", cyclic_group(4)),
                  ("ℤ/6", cyclic_group(6)), ("ℤ/12", cyclic_group(12)), ("Q₈", q8_group()),
                  ("Q₈×ℤ₃", q8z3_group()))])
        b = part2()
        c = part3()
        print(f"all checks pass: {a and b and c}", flush=True)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
