"""Q₈-equivariant chains: index-24 codes with a quaternion group of automorphisms at every k ≡ 0 mod 4
(notes/main-question.md §5, "What could still work").

Q₈ = <J, K> acts on each group of 4 coordinates by signed permutations with J² = K² = −1, JK = −KJ
(permutation parts (01)(23) and (02)(13)). It has no element of order 8, so Theorem 5.1 does not
apply. Every commuting pair in Q₈ generates a cyclic group, and every nontrivial one contains −1, so
if the action on V_{Λ(C)} is non-anomalous, V_{Λ(C)}//Q₈ has index Index(C)/8 = 3. The anomaly is not
computed here.

Part 1: random Q₈-invariant self-dual codes of length 24 (index distribution); the first one with
        Index ±24 and a Q₈-stable 2-block system (two coordinate groups) with R_σ = ±24 is the seed.
Part 2: the chain n = 48 (k = 4, |Index| by Rust), 96 (k = 8, Index by Lemma 5.8 of [I]):
        self-duality, J, K ∈ Aut, J² = K² = −1, JK = −KJ. Codes saved to ../codes/q8chain_len<n>.txt.
"""
import itertools, os, random, sys
from collections import Counter
from existence_common import dot, rref, rust_index, HERE
from mainq_common import mono_mul, mono_neg, mono_apply, closure, is_aut, write_code, rust_R
from mainq_equivariant import quad_eq, choose_splits
from mainq_obstruction import nullspace


def q8(n):
    """Signed J, K on each group of 4 coordinates with J² = K² = −1 and JK = −KJ."""
    neg4 = mono_neg(4)
    for s in itertools.product((1, -1), repeat=4):
        for t in itertools.product((1, -1), repeat=4):
            J4 = ((1, 0, 3, 2), s); K4 = ((2, 3, 0, 1), t)
            if (mono_mul(J4, J4) == neg4 and mono_mul(K4, K4) == neg4
                    and mono_mul(J4, K4) == mono_mul(neg4, mono_mul(K4, J4))):
                J = (tuple(4 * j + x for j in range(n // 4) for x in J4[0]), J4[1] * (n // 4))
                K = (tuple(4 * j + x for j in range(n // 4) for x in K4[0]), K4[1] * (n // 4))
                return J, K


def rand_group_code(gens, n, rng):
    G = list(closure(gens, n))
    S = []
    while len(S) < n // 2:
        perp = nullspace(S, n); ok = False
        for _ in range(600):
            c = [rng.randrange(3) for _ in perp]
            w = [sum(a * b[i] for a, b in zip(c, perp)) % 3 for i in range(n)]
            if not any(w):
                continue
            orb = [list(mono_apply(g, w)) for g in G]
            if all(dot(w, o) == 0 for o in orb):
                T = rref(S + orb)
                if len(T) > len(S):
                    S = T; ok = True; break
        if not ok:
            return None
    return S


def main():
    n = 24
    J, K = q8(n)
    G = closure([J, K], n)
    rng = random.Random(7)
    cnt = Counter(); seed = None; tried = 0
    while seed is None:
        C = rand_group_code([J, K], n, rng)
        tried += 1
        if C is None:
            continue
        I = rust_R(C, [], "q8I"); cnt[abs(I)] += 1
        if abs(I) != 24:
            continue
        for g1, g2 in itertools.combinations(range(n // 4), 2):
            bl = choose_splits(G, [tuple(range(4 * g1, 4 * g1 + 4)), tuple(range(4 * g2, 4 * g2 + 4))])
            if bl is not None and abs(rust_R(C, bl, "q8R")) == 24:
                seed = (C, bl, rust_R(C, bl, "q8R")); break
    print(f"1 n = 24: {tried} random Q₈-invariant codes until a seed; |Index| seen {dict(sorted(cnt.items()))}; "
          f"seed σ = {seed[1]}, R_σ = {seed[2]}", flush=True)
    E, m, blocks, gens = seed[0], n, seed[1], [J, K]
    write_code(os.path.join(HERE, "..", "codes", "q8chain_len24.txt"), E)
    for _ in range(2):
        rows, nn, newb, g2 = quad_eq(E, m, blocks, gens, refine="orbit0")
        Jn, Kn = g2; neg = mono_neg(nn)
        sd = len(rows) == nn // 2 and all(dot(a, c) == 0 for a in rows for c in rows)
        idx = f"|Index| = {abs(rust_index(rows, 'q8c'))} (Rust)" if nn <= 72 else f"Index = {seed[2]} by Lemma 5.8 of [I]"
        print(f"2 n = {nn} (k = {nn // 12}): self-dual {sd}, J, K ∈ Aut {is_aut(Jn, rows, nn) and is_aut(Kn, rows, nn)}, "
              f"J² = K² = −1 {mono_mul(Jn, Jn) == neg and mono_mul(Kn, Kn) == neg}, "
              f"JK = −KJ {mono_mul(Jn, Kn) == mono_mul(neg, mono_mul(Kn, Jn))}; {idx}; next b = {len(newb)}", flush=True)
        write_code(os.path.join(HERE, "..", "codes", f"q8chain_len{nn}.txt"), rows)
        E, m, blocks, gens = rows, nn, newb, g2


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        main()
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
