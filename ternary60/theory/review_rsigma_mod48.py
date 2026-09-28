"""Review check (2026-09-28, paper/review-2026-09-28.md §2): R_σ(E) ≡ Index(E) (mod 48) for every self-dual E
of length m ≡ 0 mod 12 and every partial block system σ (CLAUDE.md "Next steps" item 3).

Proof (notes/ternary-code-index.md Theorem 5.4, with Λ = φ^{⊗s} ⊗ λ^{⊗b} in place of λ^{⊗m/4}):
- Λ is a Fourier eigenfunction: φ̂ = i√3·φ on F_3 and λ̂ = 9·λ on F_3^4, so Λ̂ = (i√3)^s 9^b Λ = i^s 3^{m/2} Λ,
  and s = m − 4b ≡ 0 mod 4, so Λ̂ = 3^{m/2} Λ, the eigenvalue of f.
- Λ is supported on isotropic vectors: a word with Λ ≠ 0 has weight s + Σ_β w_β with w_β ∈ {1, 4}, ≡ s + b = m − 3b ≡ 0.
- Λ(−x) = (−1)^s Λ(x) = Λ(x). So the neighbour identity S(C) + S(C') = 4 S(C ∩ C') holds for S = Σ Λ.
- Ψ = Σ (Λ − f): Λ − f is even on every word and ±x pair off, so Ψ(D) ∈ 4ℤ; hence Ψ(C') ≡ −Ψ(C) mod 16.
- Base: on a sum of tetracodes (blocks of σ among them) Λ = f = 0. Connectivity gives Ψ ≡ 0 mod 16.
- Both R_σ(E) = Index(Q_σ E) and Index(E) are in 24ℤ, so they agree mod 48.

Checks: λ̂ = 9λ on F_3^4 and φ̂ = i√3 φ exactly (in ℤ[ω]); R_σ(E) ≡ Index(E) mod 48 and 24 | R_σ(E) on random
self-dual codes of length 12 and 24 with random partial block systems (all codewords enumerated), and on all
495 + 17325 block systems of the Golay code with 1 or 2 blocks.
"""
import itertools
import os
import random

from review_conj14_check import (codewords, R_sigma, random_self_dual, GOLAY_PAPER, LAM, phi, log, LOG)

HERE = os.path.dirname(os.path.abspath(__file__))


def zomega_check():
    """Exact check of the one-coordinate and one-block Fourier transforms in Z[ω], ω = e^{2πi/3}.
    Elements a + bω are pairs (a, b); ω² = −1 − ω."""
    def mul(x, y):
        a, b = x
        c, d = y
        # (a + bω)(c + dω) = ac + (ad + bc)ω + bd ω² = (ac − bd) + (ad + bc − bd) ω
        return (a * c - b * d, a * d + b * c - b * d)

    def add(x, y):
        return (x[0] + y[0], x[1] + y[1])

    def wpow(e):
        e %= 3
        return [(1, 0), (0, 1), (-1, -1)][e]

    isq = add(wpow(1), mul((-1, 0), wpow(2)))            # ω − ω² = i√3
    for u in range(3):
        s = (0, 0)
        for x in range(3):
            s = add(s, mul((phi(x), 0), wpow(u * x)))
        assert s == mul(isq, (phi(u), 0)), (u, s)
    for u in itertools.product(range(3), repeat=4):
        s = (0, 0)
        for x in itertools.product(range(3), repeat=4):
            w = LAM[sum(1 for v in x if v)]
            if w:
                s = add(s, mul((w, 0), wpow(sum(a * b for a, b in zip(u, x)))))
        assert s == (9 * LAM[sum(1 for v in u if v)], 0), (u, s)
    log("φ̂ = i√3·φ on F_3 and λ̂ = 9·λ on F_3^4, exactly in Z[ω]")


def random_system(m, b, rng):
    coords = list(range(m))
    rng.shuffle(coords)
    return [set(coords[4 * j:4 * j + 4]) for j in range(b)]


def main():
    LOG.clear()
    rng = random.Random(4848)
    zomega_check()
    for m, reps in ((12, 40), (24, 6)):
        cnt = 0
        vals = {}
        for _ in range(reps):
            E = random_self_dual(m, rng, steps=30 if m == 12 else 60)
            W = codewords(E, m)
            idx = R_sigma(W, m, [])
            for b in range(0, m // 4 + 1):
                for _ in range(3 if m == 12 else 2):
                    sig = random_system(m, b, rng)
                    R = R_sigma(W, m, sig)
                    assert R % 24 == 0 and (R - idx) % 48 == 0, (m, b, R, idx)
                    vals[(idx % 48, R % 48)] = vals.get((idx % 48, R % 48), 0) + 1
                    cnt += 1
        log(f"m = {m}: {cnt} (code, partial system) pairs, 24 | R_σ(E) and R_σ(E) ≡ Index(E) mod 48; "
            f"(Index mod 48, R mod 48) counts {dict(sorted(vals.items()))}")
    W = codewords(GOLAY_PAPER, 12)
    bad = 0
    tot = 0
    for b1 in itertools.combinations(range(12), 4):
        r = R_sigma(W, 12, [set(b1)])
        bad += (r - 24) % 48 != 0
        tot += 1
        rest = [i for i in range(12) if i not in b1]
        for b2 in itertools.combinations(rest, 4):
            if b2 < b1:
                continue
            r = R_sigma(W, 12, [set(b1), set(b2)])
            bad += (r - 24) % 48 != 0
            tot += 1
    log(f"Golay: all {tot} systems with 1 or 2 blocks have R_σ ≡ Index = 24 mod 48 (failures: {bad})")
    assert bad == 0
    log("all checks passed")
    with open(os.path.join(HERE, "review_rsigma_mod48.log"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
