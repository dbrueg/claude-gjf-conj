"""Unambiguous generator files for the J- and ℤ/12-chains (notes/blueprint/chains-and-seeds.md §6).

The files jchain_len<n>.J.txt and z12chain_len<n>.g.txt (written by mainq_jchain.py and mainq_z12chain.py
before 2026-09-27) store the permutation as concatenated decimal numbers without separators, so the first line
has several parses into a permutation of 0..n−1. For each file this script
- enumerates every parse (all of them, not just the first);
- keeps those that satisfy the stated relation (J² = −1, resp. ord g = 12 and g⁶ = −1) and are automorphisms
  of the code;
- checks that exactly one survives, and writes it to <name>.gens.txt in the space-separated format of
  q8z3_chain_len<n>.gens.txt ("J perm: …", "J sign: …" with signs ±1).
The writers in mainq_jchain.py and mainq_z12chain.py now also write the .gens.txt files directly.
"""
import os, sys
from existence_common import HERE
from mainq_common import read_code, is_aut, mono_mul, mono_neg, mono_pow, write_gens

CODES = os.path.join(HERE, "..", "codes")


def all_parses(s, n):
    out, used, cur = [], [False] * n, []

    def rec(i):
        if i == len(s):
            if len(cur) == n:
                out.append(tuple(cur))
            return
        for L in (1, 2, 3):
            if i + L <= len(s) and (L == 1 or s[i] != "0"):
                v = int(s[i:i + L])
                if v < n and not used[v]:
                    used[v] = True; cur.append(v)
                    rec(i + L)
                    used[v] = False; cur.pop()
    sys.setrecursionlimit(10000)
    rec(0)
    return out


def convert(stem, name, n, relation):
    C = read_code(os.path.join(CODES, f"{stem}.txt"))
    with open(os.path.join(CODES, f"{stem}.{name}.txt")) as fh:
        rows = [ln.strip() for ln in fh if ln.strip()]
    s = tuple(1 if ch == "1" else -1 for ch in rows[1])
    parses = all_parses(rows[0], n)
    good = [p for p in parses if relation((p, s), n) and is_aut((p, s), C, n)]
    ok = len(good) == 1
    if ok:
        write_gens(os.path.join(CODES, f"{stem}.gens.txt"), {name: (good[0], s)})
    print(f"{stem}.{name}.txt: {len(parses)} parses, {len(good)} satisfying the relation and in Aut(C); "
          f"wrote {stem}.gens.txt: {ok}", flush=True)
    return ok


def rel_J(g, n):
    return mono_mul(g, g) == mono_neg(n)


def rel_g(g, n):
    e = mono_pow(g, 0)
    return mono_pow(g, 6) == mono_neg(n) and mono_pow(g, 4) != e and mono_pow(g, 6) != e


if __name__ == "__main__":
    import io, contextlib
    buf = io.StringIO()

    class Tee:
        def write(self, s):
            sys.__stdout__.write(s); buf.write(s)

        def flush(self):
            sys.__stdout__.flush()

    with contextlib.redirect_stdout(Tee()):
        ok = all([convert(f"jchain_len{n}", "J", n, rel_J) for n in (24, 48, 72, 96, 120, 144)] +
                 [convert(f"z12chain_len{n}", "g", n, rel_g) for n in (72, 108, 144)])
        print(f"all checks pass: {ok}", flush=True)
    with open(os.path.splitext(os.path.abspath(__file__))[0] + ".log", "w") as fh:
        fh.write(buf.getvalue())
