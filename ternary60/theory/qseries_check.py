"""Check the full q-series identity (not only the leading coefficient) on the Golay lattice:
   sum_{v in shadow} s(v) (v.mu)^2 q^{v^2/2} = (I mu^2/12) E_2(q) eta(q)^n,   mu = sqrt3 (e1+e2),
and Phi = sum s(v) q^{v^2/2} = I eta^n.  Series in Q = q^{1/24}.
Shadow vector coords: m_i/(2 sqrt3), m_i odd, m_i = 2c_i+3 mod 6; sign (-1)^{sum (m_i-3)/2}.
"""
import itertools
from fractions import Fraction
from ternary import rref
from check_design import GOLAY_GJF, to3, all_codewords
N = 12
TOP = 12 + 24 * 4          # Q-exponent cutoff (4 orders beyond leading)
def coord_series(a, poly=None):
    s = [0] * (TOP + 1)
    for m in range(-40, 41):
        if m % 2 == 0 or (m - (2 * a + 3)) % 6: continue
        e = m * m
        if e <= TOP * 1:  # exponent of Q is m^2/2*... v^2/2 = m^2/24 -> Q^{m^2}
            s[e] += (1 if ((m - 3) // 2) % 2 == 0 else -1)
    return s
# NB: v^2/2 = sum m_i^2/24, i.e. q^{v^2/2} = Q^{sum m_i^2} with Q = q^{1/24}
def mul(a, b):
    c = [0] * (TOP + 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b[:TOP + 1 - i]):
                if y: c[i + j] += x * y
    return c
f = {a: coord_series(a) for a in range(3)}
def pair_series(a, b):
    c = [Fraction(0)] * (TOP + 1)
    for m1 in range(-40, 41):
        if m1 % 2 == 0 or (m1 - (2 * a + 3)) % 6: continue
        for m2 in range(-40, 41):
            if m2 % 2 == 0 or (m2 - (2 * b + 3)) % 6: continue
            e = m1 * m1 + m2 * m2
            if e <= TOP:
                c[e] += (1 if ((m1 - 3) // 2 + (m2 - 3) // 2) % 2 == 0 else -1) * Fraction((m1 + m2) ** 2, 4) * Fraction(1, 1)
    return c
# (v.mu)^2 with mu = sqrt3(e1+e2): v.mu = sqrt3 (m1+m2)/(2 sqrt3) = (m1+m2)/2
B, piv = rref(to3(GOLAY_GJF), N)
Phi = [0] * (TOP + 1); Phimu = [Fraction(0)] * (TOP + 1)
ps = {(a, b): pair_series(a, b) for a in range(3) for b in range(3)}
for w in all_codewords(B, N):
    rest = [1] + [0] * TOP
    for i in range(2, N): rest = mul(rest, f[w[i]])
    full = mul(mul(rest, f[w[0]]), f[w[1]])
    Phi = [x + y for x, y in zip(Phi, full)]
    pm = ps[(w[0], w[1])]
    for i, x in enumerate(rest):
        if x:
            for j in range(TOP + 1 - i):
                if pm[j]: Phimu[i + j] += x * pm[j]
# eta^12 = Q^{12} prod (1-q^k)^12, q = Q^24 ; E2 = 1 - 24 sum sigma(n) q^n
def eta_pow(n):
    s = [0] * (TOP + 1); s[n] = 1
    for k in range(1, TOP // 24 + 1):
        for _ in range(n):
            t = s[:]
            for i in range(TOP + 1 - 24 * k): t[i + 24 * k] -= s[i]
            s = t
    return s
E2 = [0] * (TOP + 1); E2[0] = 1
for k in range(1, TOP // 24 + 1):
    E2[24 * k] = -24 * sum(d for d in range(1, k + 1) if k % d == 0)
eta12 = eta_pow(12)
I = Phi[12]
print("Index from shadow theta:", I)
print("Phi == I*eta^12 :", Phi == [I * x for x in eta12])
mu2 = 6
rhs = [Fraction(I * mu2, 12) * x for x in mul(E2, eta12)]
print("Phi_mu == (I mu^2/12) E2 eta^12 through q^{1/2+%d}:" % ((TOP - 12) // 24), Phimu == rhs)
print("nonzero coefficients (Q-exponent: lhs, rhs):", [(i, Phimu[i], rhs[i]) for i in range(TOP + 1) if Phimu[i] or rhs[i]])
