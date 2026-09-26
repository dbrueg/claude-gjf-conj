"""Gadget substitution (ternary-code-index.md §5.1, item (c)).

A gadget of odd length k is a self-orthogonal R ⊂ F_3^k of dim (k-1)/2; R^⊥/R = <e>, ν = e·e.
Substituting gadgets for the coordinates of a self-dual W gives a self-dual code with
Index = ± prod_i a_i · Index(W), a = F(e+R) (F(R) = 0 since f is odd for k odd).
Random gadgets: a ∈ 12Z in every sample (k = 5, 7, 9, 11, 13).
"""
import random, sys
from collections import Counter
from existence_common import *


def random_gadget(k, rng):
    gens = []
    while len(gens) < (k - 1) // 2:
        v = [rng.randrange(3) for _ in range(k)]
        if dot(v, v) or any(dot(v, g) for g in gens):
            continue
        if not gens or not inspan(gens, v):
            gens.append(v)
    return gens


def analyse(gens, k, rng):
    R = span(gens, k)
    Rs = set(R)
    while True:
        e = tuple(rng.randrange(3) for _ in range(k))
        if e not in Rs and all(dot(e, g) == 0 for g in gens):
            break
    return dot(e, e), sum(f(add(e, r)) for r in R)


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    rng = random.Random(1)
    for k in (5, 7, 9, 11, 13):
        cnt = Counter(analyse(random_gadget(k, rng), k, rng) for _ in range(N if k == 13 else N // 3))
        print(f"k={k}: (nu, a) -> count {dict(cnt)};  all a in 12Z: {all(a % 12 == 0 for _, a in cnt)}")
