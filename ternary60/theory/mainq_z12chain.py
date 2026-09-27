"""Z/12-equivariant partial quadrupling: index-24 codes with an order-12 symmetry g (g⁶ = −1, cycle
shape 6^{n/6}, h = g⁴ balanced) at every k ≡ 0 mod 6 (notes/main-question.md §4.4).

Seed: a self-dual code E of length 36 (k = 3) invariant under g = (e_{6j+i} ↦ e_{6j+i+1}, i < 5;
e_{6j+5} ↦ −e_{6j}), found by the random search of `mainq_seed_search.py` (GJF's method with a
prescribed automorphism). σ is a g-stable 3-block system (one h-orbit of J-stable blocks, J = g³) with
R_σ(E) = ±24 and R_σ̄(D) = 0, where D is the h-fixed code of E collapsed to one coordinate per h-orbit.

Part 1: the seed: g ∈ Aut(E), ord g = 12, g⁶ = −1; Index(E), T_h(E); R_σ(E); R_σ̄(D).
Part 2: the chain n = 72 (k = 6), 144 (k = 12) [, 216 (k = 18)]: self-duality, g-invariance, ord g,
        g⁶ = −1, cycle shape; Index (Rust |I| at n = 72; Lemma 5.8 of [I] beyond); T_h by enumerating the
        fixed code (Rust); GJF Thm 5.6 hypotheses for m = gcd(k,24).
Codes are saved to ../codes/z12chain_len<n>.txt with g in z12chain_len<n>.g.txt.
"""
import os, sys
from existence_common import dot, rust_index, rref, span, HERE
from existence_quadruple import R
from mainq_common import (mono_pow, mono_neg, mono_order, cycle_type, is_aut, write_code, write_gens, read_code,
                          closure, fixed_code, rust_R, twined_count_rust)
from mainq_equivariant import quad_eq, choose_splits, block_image
from math import gcd

SEED = os.path.join(HERE, "..", "codes", "z12seed_len36_3.txt")
SIGMA_A = [(24, 27, 30, 33), (28, 25, 34, 31), (26, 29, 32, 35)]                  # b = 3: k = 6, 12, 18, …
SIGMA_B = [(0, 3, 7, 10), (4, 1, 11, 8), (2, 5, 9, 6),
           (12, 15, 25, 28), (16, 13, 29, 26), (14, 17, 27, 24)]                     # b = 6: k = 9, 15, 21, …


def g36():
    n = 36
    p = [0] * n; s = [1] * n
    for j in range(n // 6):
        for i in range(6):
            p[6 * j + i] = 6 * j + (i + 1) % 6
        s[6 * j + 5] = -1
    return (tuple(p), tuple(s))


def selfdual(B, n):
    return len(B) == n // 2 and all(dot(a, c) == 0 for a in B for c in B)


def collapsed(E, n, h):
    """h-fixed code, one coordinate per h-orbit (orbit rep = smallest index), and the orbit map."""
    orbits, seen = [], set()
    for i in range(n):
        if i not in seen:
            o = [i, h[0][i], h[0][h[0][i]]]
            seen.update(o); orbits.append(o)
    Fx = fixed_code(E, n, h)
    D = rref([[r[o[0]] for o in orbits] for r in Fx]) if Fx else []
    return D, {x: k for k, o in enumerate(orbits) for x in o}, len(orbits)


def gjf_check(g, n):
    k = n // 12; m = gcd(k, 24)
    if m == 24:
        return f"m = 24: needs an element of order 24 (not available)"
    x = mono_pow(g, 12 // m)                         # the element of order m in <g>
    o = mono_order(x)
    c1 = (m % 2 == 1) or mono_pow(x, m // 2) == mono_neg(n)
    c2 = True
    if m % 3 == 0:
        y = mono_pow(x, m // 3)
        c2 = set(cycle_type(y[0])) == {3}
    return f"m = {m}: element g^{12 // m} of order {o}; condition 1 {c1}; cycle-shape part of condition 2 {c2}"


def main(label, SIGMA, maxn, tmax):
    print(f"== chain {label}: σ = {SIGMA} (b = {len(SIGMA)})", flush=True)
    E = read_code(SEED); n = 36
    g = g36(); h = mono_pow(g, 4)
    print(f"1 seed {os.path.basename(SEED)}: g ∈ Aut {is_aut(g, E, n)}, ord g = {mono_order(g)}, "
          f"g⁶ = −1 {mono_pow(g, 6) == mono_neg(n)}; Index = {rust_R(E, [])} (sign-exact); "
          f"T_h = {twined_count_rust(E, n, h)}", flush=True)
    D, orb, N = collapsed(E, n, h)
    sbar = [tuple(sorted(orb[x] for x in SIGMA[j])) for j in range(0, len(SIGMA), 3)]
    print(f"1 σ = {SIGMA}: R_σ(E) = {rust_R(E, SIGMA)}; collapsed D: length {N}, dim {len(D)}, "
          f"σ̄ = {sbar}, R_σ̄(D) = {R(span(D, N), sbar, N)}", flush=True)
    G = closure([g], n)
    blocks = choose_splits(G, SIGMA)
    gens = [g]; m_ = n
    while True:
        rows, nn, newb, gens2 = quad_eq(E, m_, blocks, gens, refine="orbit0")
        gq = gens2[0]
        line = (f"2 n = {nn} (k = {nn // 12}): self-dual {selfdual(rows, nn)}, g ∈ Aut {is_aut(gq, rows, nn)}, "
                f"ord g = {mono_order(gq)}, g⁶ = −1 {mono_pow(gq, 6) == mono_neg(nn)}, "
                f"cycle shape {sorted(set(cycle_type(gq[0])))}")
        if nn <= 72:
            line += f"; |Index| = {abs(rust_index(rows, f'z12_{nn}'))} (Rust)"
        else:
            line += "; Index = R_σ(seed) by Lemma 5.8 of [I] (not computed)"
        hq = mono_pow(gq, 4)
        if nn <= tmax:
            line += f"; T_h = {twined_count_rust(rows, nn, hq)} (fixed code enumerated)"
        else:
            line += "; T_h = R_σ̄(D) = 0 by Lemma 4.3 (not enumerated)"
        line += f"; next b = {len(newb)}"
        print(line, flush=True)
        print("3   " + gjf_check(gq, nn), flush=True)
        write_code(os.path.join(HERE, "..", "codes", f"z12chain_len{nn}.txt"), rows)
        write_code(os.path.join(HERE, "..", "codes", f"z12chain_len{nn}.g.txt"),
                   [list(gq[0]), [1 if s == 1 else 2 for s in gq[1]]])
        write_gens(os.path.join(HERE, "..", "codes", f"z12chain_len{nn}.gens.txt"), {"g": gq})
        if nn >= maxn:
            break
        E, m_, blocks, gens = rows, nn, newb, gens2


if __name__ == "__main__":
    import io, contextlib
    maxn = int(sys.argv[1]) if len(sys.argv) > 1 else 144      # chain A goes to n = maxn
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        main("A", SIGMA_A, maxn, 144)
        main("B", SIGMA_B, 108, 108)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
