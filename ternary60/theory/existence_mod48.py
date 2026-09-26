"""Mod-48 invariance of tetracode Hadamard doubling (ternary-code-index.md §5.1, Thm 5.4, Prop 5.5).

Λ(x) = Π_b λ(|supp x ∩ b|), λ = (0,−2,0,0,1), over a partition of [m] into 4-blocks.
Index(H(E ⊕ σT^{m/4})) = Σ_{x∈E} Λ(x)  (§5.1(f)).
Part 1: λ̂ = 9λ on F_3^4 (so Λ̂ = 3^{m/2} Λ, like f).
Part 2: Σ_{C}Λ + Σ_{C'}Λ = 4 Σ_{C∩C'}Λ on random neighbour pairs (the (★)-analogue).
Part 3: Thm 5.4: Σ_E Λ ≡ Index(E) mod 16 for random E, random blocks (m = 12, 24).
Part 4: Prop 5.5: #even ≡ #odd ≡ 0 mod 8 maximal codewords, i.e. |F| ≡ Index mod 16
        (m = 12, 24 exact; m = 36, 48, 60 via Rust full_weight and |I|).
"""
import itertools, random, re, subprocess, os
from collections import Counter
from existence_common import *
from ternary import random_self_dual

LAM = (0, -2, 0, 0, 1)


def Lam(x, blocks):
    p = 1
    for bl in blocks:
        p *= LAM[sum(1 for j in bl if x[j])]
        if not p:
            return 0
    return p


def part1():
    ok = True
    for v in itertools.product(range(3), repeat=4):
        s = 0
        for y in itertools.product(range(3), repeat=4):
            lam = LAM[sum(1 for a in y if a)]
            if lam:
                s += lam * OMEGA ** dot(v, y)
        ok &= abs(s - 9 * LAM[sum(1 for a in v if a)]) < 1e-9
    print("1 lambda-hat = 9 lambda on F_3^4:", ok)


def part2(rng, m, N):
    ok = 0
    for _ in range(N):
        B, _ = random_self_dual(m, rng)
        x = rand_iso([list(r) for r in B], m, rng)
        B2 = nbr([list(r) for r in B], x)
        s = [dot(r, x) for r in B]
        i = next(i for i, t in enumerate(s) if t)
        D = [[(a - (s[j] * (1 if s[i] == 1 else 2)) % 3 * b) % 3 for a, b in zip(r, B[i])]
             for j, r in enumerate(B) if j != i]
        p = list(range(m)); rng.shuffle(p)
        blocks = [p[4 * b:4 * b + 4] for b in range(m // 4)]
        SC, SC2, SD = (sum(Lam(c, blocks) for c in span(X, m)) for X in (B, B2, D))
        ok += (SC + SC2 == 4 * SD)
    print(f"2 m={m}: S(C)+S(C') = 4S(C∩C') on {ok}/{N} random neighbour pairs")


def part3(rng, m, N):
    res = Counter()
    for _ in range(N):
        B, _ = random_self_dual(m, rng)
        Ew = span(B, m)
        I = sum(f(c) for c in Ew)
        for _ in range(3):
            p = list(range(m)); rng.shuffle(p)
            blocks = [p[4 * b:4 * b + 4] for b in range(m // 4)]
            S = sum(Lam(c, blocks) for c in Ew)
            res[(S - I) % 16 == 0] += 1
    print(f"3 m={m}: Σ_E Λ ≡ Index(E) mod 16 on {res[True]}/{sum(res.values())}")


def part4(rng, m, N):
    ok = 0; hist = Counter()
    for _ in range(N):
        B, _ = random_self_dual(m, rng)
        if m <= 24:
            Ew = span(B, m)
            F = sum(1 for c in Ew if all(c)); I = sum(f(c) for c in Ew)
        else:
            fn = os.path.join(tempfile_dir, "p4.txt")
            open(fn, "w").write("\n".join("".join(map(str, r)) for r in B) + "\n")
            out = subprocess.run([BIN, "index", fn], capture_output=True, text=True).stdout
            F = int(re.search(r"full_weight=(\d+)", out).group(1)); I = int(re.search(r" I=(-?\d+)", out).group(1))
        ok += (F - I) % 16 == 0
        hist[(F % 16, I % 16)] += 1
    print(f"4 m={m}: |F| ≡ Index mod 16 on {ok}/{N}; (|F| mod 16, I mod 16) -> {dict(hist)}")


if __name__ == "__main__":
    import tempfile
    tempfile_dir = tempfile.mkdtemp()
    rng = random.Random(11)
    part1()
    part2(rng, 12, 40); part2(rng, 24, 6)
    part3(rng, 12, 60); part3(rng, 24, 20)
    part4(rng, 12, 200); part4(rng, 24, 30)
    for m, N in ((36, 200), (48, 60), (60, 20)):
        part4(rng, m, N)
