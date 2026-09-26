"""EXPLORATORY (notes §5.1(e)): Golay rings with 2-dimensional bonds.

Each Golay cell has left bond Z = <z1,z2> and right bond Y = <y1,y2> in F_3^12 with Z ⊥ Y and
Gram(Z) = −Gram(Y). The 81×81 transfer matrix is M[(a,b),(a',b')] = G((a,a'),(b,b')) over the
basis (z1,z2,y1,y2), where G(u,v) = Σ_{x∈u+C} f(x) ω^{v·x}. The ring of s cells has index
Tr(M^s)/9^s. Prints the power sums p_1..p_5 for random bonds; they grow like random codes.
Usage: python3 bond2.py golay|code2 SEED N
"""
import random, itertools, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ternary60', 'theory'))
from existence_common import f, dot, add, span, GOLAY, CODE2, inspan, rref
from fractions import Fraction
F4 = list(itertools.product(range(3), repeat=4))


def Gtable(Cw, basis):
    tab = {}
    for al in F4:
        u = tuple(sum(a * b[j] for a, b in zip(al, basis)) % 3 for j in range(len(basis[0])))
        cnt = {}
        for c in Cw:
            x = add(u, c); fx = f(x)
            if fx:
                sig = tuple(dot(x, b) for b in basis)
                cnt[sig] = cnt.get(sig, 0) + fx
        for be in F4:
            p = q = 0
            for sig, m in cnt.items():
                e = sum(s * t for s, t in zip(sig, be)) % 3
                if e == 0: p += m
                elif e == 1: q += m
                else: p -= m; q -= m
            tab[(al, be)] = (p, q)
    return tab


PAIRS = [(a, b) for a in itertools.product(range(3), repeat=2) for b in itertools.product(range(3), repeat=2)]


def transfer(tab):
    P = [[0] * 81 for _ in range(81)]; Q = [[0] * 81 for _ in range(81)]
    for i, (a, b) in enumerate(PAIRS):
        for j, (a2, b2) in enumerate(PAIRS):
            p, q = tab[(a + a2, b + b2)]; P[i][j] = p; Q[i][j] = q
    return P, Q


def mm(A, B):
    Bt = list(zip(*B))
    return [[sum(x * y for x, y in zip(A[i], Bt[j])) for j in range(len(B[0]))] for i in range(len(A))]


def zmm(X, Y):
    P1, Q1 = X; P2, Q2 = Y
    a = mm(P1, P2); b = mm(Q1, Q2); c = mm(P1, Q2); d = mm(Q1, P2)
    n, m = len(a), len(a[0])
    return ([[a[i][j] - b[i][j] for j in range(m)] for i in range(n)],
            [[c[i][j] + d[i][j] - b[i][j] for j in range(m)] for i in range(n)])


def ztr(X):
    return (sum(X[0][i][i] for i in range(len(X[0]))), sum(X[1][i][i] for i in range(len(X[0]))))


def powersums(M, K, norm):
    out = []; P = M
    for k in range(1, K + 1):
        t = ztr(P); out.append((Fraction(t[0], norm ** k), Fraction(t[1], norm ** k)))
        if k < K: P = zmm(P, M)
    return out


def rand_bonds(X, rng, m=12):
    rv = lambda: tuple(rng.randrange(3) for _ in range(m))
    while True:
        y1, y2 = rv(), rv()
        if len(rref([list(r) for r in X] + [list(y1), list(y2)])) != len(X) + 2: continue
        g = [[(-dot(a, b)) % 3 for b in (y1, y2)] for a in (y1, y2)]
        for _ in range(20000):
            z1 = rv()
            if dot(z1, y1) or dot(z1, y2) or dot(z1, z1) != g[0][0]: continue
            z2 = rv()
            if dot(z2, y1) or dot(z2, y2) or dot(z2, z2) != g[1][1] or dot(z1, z2) != g[0][1]: continue
            return (z1, z2, y1, y2)


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    X = {"golay": GOLAY, "code2": CODE2}[sys.argv[1] if len(sys.argv) > 1 else "golay"]
    Cw = span(X, 12)
    for t in range(int(sys.argv[3]) if len(sys.argv) > 3 else 3):
        M = transfer(Gtable(Cw, rand_bonds(X, rng)))
        print(tuple((str(a) if b == 0 else f"{a}+{b}w") for a, b in powersums(M, 5, 9)), flush=True)
