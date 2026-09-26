"""Seed search for Theorem 5.7-type chains at odd multiples of 12 (ternary-code-index.md §5.1(f″)).

A seed is a pair (E, σ): E self-dual of length m = 12k₀, σ a partition of [m] into 4-blocks, with
S_σ(E) = Index(H(E ⊕ σT)) = ±24. By Lemma 5.6, one seed gives index-24 codes at every length
12k₀·2^j (j ≥ 1). Theorem 5.4 forces Index(E) ≡ 24 mod 48 for a seed.
The index of the doubled code (length 2m) is computed with the Rust `index`, so this is feasible
for m ≤ 36 (n = 72: about 10 s per σ on 8 cores). Found seeds are appended to ../runs/seeds.txt.

Usage:
  python3 existence_seed_search.py --code ../codes/P17.txt --tries 300 --seed 1
  python3 existence_seed_search.py --random 36 --tries 300 --seed 2   # first finds a random index-24 code
"""
import argparse, os, random, time
from existence_common import *
from existence_refinement import double
from ternary import random_self_dual

HERE = os.path.dirname(os.path.abspath(__file__))


def load(fn):
    return rref([[int(ch) for ch in l.strip()] for l in open(fn) if l.strip()])


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--code"); ap.add_argument("--random", type=int)
    ap.add_argument("--tries", type=int, default=100); ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    if a.code:
        E = load(a.code); label = os.path.basename(a.code)
    else:
        while True:
            B, _ = random_self_dual(a.random, rng)
            E = rref([list(r) for r in B])
            if abs(rust_index(E)) == 24:
                break
        label = f"random{a.random}_seed{a.seed}"
    m = len(E[0]); I = rust_index(E)
    print(f"E = {label}: length {m}, Index ±{abs(I)}, Index mod 48 = {abs(I) % 48} (need 24)", flush=True)
    vals, t0 = [], time.time()
    for t in range(a.tries):
        p = list(range(m)); rng.shuffle(p)
        blocks = [sorted(p[4 * b:4 * b + 4]) for b in range(m // 4)]
        S = rust_index(double(E, blocks, m)); vals.append(S)
        print(f"try {t}: S = {S}  ({time.time() - t0:.0f}s)", flush=True)
        if abs(S) == 24:
            with open(os.path.join(HERE, "..", "runs", "seeds.txt"), "a") as fh:
                fh.write(f"# seed: {label}, S = {S}\n" + "\n".join("".join(map(str, r)) for r in E) + f"\nblocks = {blocks}\n\n")
            print("FOUND seed; appended to runs/seeds.txt", flush=True)
            break
    print(f"summary: {len(vals)} tries, all S ≡ 24 mod 48: {all(v % 48 == 24 for v in vals)}, "
          f"min |S| = {min(abs(v) for v in vals)}", flush=True)
