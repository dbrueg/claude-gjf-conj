"""All 10395 pair-matchings for the second doubling at n = 48 (ternary-code-index.md §5.1(f″)).

E_1 = H(Golay ⊕ σ₀T³), σ₀ = SIGMA0 (h = 0, Index −24). Every perfect matching M of the 12 Golay
coordinates gives 4-blocks {i, 12+i, j, 12+j} of E_1. A word H(g,t) has state X (exactly one of
g_i, t_i ≠ 0), B (both) or N (neither) at i. S_M(E_1) = Σ_{(g,t)} Π_{{i,j}∈M} w, where
w(XX) = 1, w({B,N}) = −2, and w = 0 otherwise. S_M(E_1) = Index(H(E_1 ⊕ σ_M T⁶)).
Output: the distribution of S over all M, and the result for the 27 matchings inside σ₀-blocks
(the refinements of Lemma 5.6), all of which give S = Index(E_1) = −24.
"""
from collections import Counter
from existence_common import *
from existence_refinement import SIGMA0, tetra_on


def matchings(pts):
    if not pts:
        yield []
        return
    a = pts[0]
    for k in range(1, len(pts)):
        rest = pts[1:k] + pts[k + 1:]
        for m in matchings(rest):
            yield [(a, pts[k])] + m


if __name__ == "__main__":
    Gw, Tw = span(GOLAY, 12), span(tetra_on(SIGMA0, 12), 12)
    grp = Counter()
    for g in Gw:
        for t in Tw:
            B = frozenset(i for i in range(12) if g[i] and t[i])
            N = frozenset(i for i in range(12) if not g[i] and not t[i])
            if len(B) == len(N):
                grp[(B, N)] += 1
    blocks = [set(b) for b in SIGMA0]
    dist, inblock = Counter(), Counter()
    for M in matchings(list(range(12))):
        S = 0
        for (B, N), mult in grp.items():
            ok = True
            for i, j in M:
                si = "B" if i in B else "N" if i in N else "X"
                sj = "B" if j in B else "N" if j in N else "X"
                if not (si == sj == "X" or {si, sj} == {"B", "N"}):
                    ok = False
                    break
            if ok:
                S += mult * (-2) ** len(B)
        dist[S] += 1
        if all(any(i in b and j in b for b in blocks) for i, j in M):
            inblock[S] += 1
    print(f"all 10395 matchings: |S| = 24 for {dist[24] + dist[-24]}; distribution {dict(sorted(dist.items()))}")
    print(f"27 in-block matchings (refinements of σ₀): {dict(inblock)}")
