#!/usr/bin/env python3
"""B-F1: 小さい (a,b,N) で fh_sieve（現在座標・根集合更新式）と Python の直積列挙オラクル
（初期座標 FH-interval・Fraction、根集合の直接式）を全項目で照合する。"""
import itertools
import json
import os
import subprocess
import tempfile
from fractions import Fraction
from math import gcd
from obmath import carry_alphabet, modinv, primes_upto, trial_factor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
BIN = os.path.join(ROOT, "build", "word-appendix", "fh_sieve_oracle_bin")
CASES = [(6, 5, 6), (6, 5, 8), (6, 5, 10), (9, 7, 4), (9, 7, 5), (9, 7, 6), (7, 5, 5), (5, 2, 6), (8, 3, 5), (11, 9, 4)]


def build():
    subprocess.check_call(["g++", "-O2", "-std=c++17", "-o", BIN, os.path.join(HERE, "fh_sieve.cpp")])


def oracle(a, b, N):
    alph = carry_alphabet(a, b)
    rp = [p for p in primes_upto(N + 1) if p % 2 == 1 and (a * b) % p != 0]
    A = [0] * (N + 1)
    rejI = [0] * (N + 2)
    rejR = [0] * (N + 2)
    leaves = {"small": 0, "even": 0, "roots": 0, "candidates": 0}
    cands = []
    interval_equiv_fail = 0
    roots_formula_fail = 0
    # 深さ s の通過語: 長さ s の全語を直積で列挙し、深さ 1..s の条件を順に検査
    for s in range(0, N + 1):
        for w in itertools.product(alph, repeat=s):
            # C_j
            C = [0]
            for j, c in enumerate(w):
                C.append(a * C[j] + b ** j * c)
            status = "pass"
            fail_depth = None
            lo, hi = Fraction(0), Fraction(1)
            Lc, Uc, Bc = 0, 1, 1
            roots = {p: {0} for p in rp}
            Rcur = {p: 0 for p in rp}
            for j in range(1, s + 1):
                # 初期座標 FH-interval
                lo = max(lo, Fraction(C[j], a ** j))
                hi = min(hi, Fraction(C[j] + b ** j, a ** j))
                # 現在座標（画像）
                Bc2 = b * Bc
                Lc2 = max(0, a * Lc - w[j - 1] * Bc)
                Uc2 = min(Bc2, a * Uc - w[j - 1] * Bc)
                Lc, Uc, Bc = Lc2, Uc2, Bc2
                empty_init = lo >= hi
                empty_cur = Lc >= Uc
                if empty_init != empty_cur:
                    interval_equiv_fail += 1
                if not empty_init:
                    # 現在区間 = 初期区間の像
                    if Fraction(Lc, Bc) != (a ** j * lo - C[j]) / b ** j or Fraction(Uc, Bc) != (a ** j * hi - C[j]) / b ** j:
                        interval_equiv_fail += 1
                if empty_init:
                    status, fail_depth = "interval", j
                    break
                cover = False
                for p in rp:
                    # 直接式 R_j = -C_j a^{-j} mod p と更新式
                    Rd = (-C[j] * pow(modinv(a, p), j, p)) % p
                    Ru = (Rcur[p] - w[j - 1] * pow(b, j - 1, p) * pow(modinv(a, p), j, p)) % p
                    if Rd != Ru:
                        roots_formula_fail += 1
                    Rcur[p] = Rd
                    roots[p].add(Rd)
                    if len(roots[p]) == p:
                        cover = True
                if cover:
                    status, fail_depth = "roots", j
                    break
            if status == "pass":
                A[s] += 1
                if s == N:
                    seed = (-C[N] * modinv(pow(a, N, b ** N), b ** N)) % (b ** N)
                    assert all((a ** j * seed + C[j]) % (b ** j) == 0 for j in range(1, N + 1))
                    if seed <= max(a, N + 1):
                        leaves["small"] += 1
                    elif seed % 2 == 0:
                        leaves["even"] += 1
                    elif any(seed % p in roots[p] for p in rp):
                        leaves["roots"] += 1
                    else:
                        leaves["candidates"] += 1
                        cands.append((seed,) + tuple(w))
            elif fail_depth == s:
                # 深さ s で初めて棄却された語（接頭語 s-1 は通過）
                if status == "interval":
                    rejI[s] += 1
                else:
                    rejR[s] += 1
    return {"alphabet": alph, "root_primes": rp, "A": A, "rejI": rejI, "rejR": rejR, "leaves": leaves,
            "candidates": sorted(cands), "interval_equiv_fail": interval_equiv_fail, "roots_formula_fail": roots_formula_fail}


def main():
    build()
    results = []
    all_ok = True
    with tempfile.TemporaryDirectory() as td:
        for (a, b, N) in CASES:
            prefix = os.path.join(td, "%d_%d_%d" % (a, b, N))
            subprocess.check_call([BIN, str(a), str(b), str(N), prefix])
            cpp = json.load(open(prefix + ".counts.json"))
            cpp_cands = sorted(tuple(int(x) for x in line.split()) for line in open(prefix + ".candidates.txt"))
            orc = oracle(a, b, N)
            ch = {}
            ch["alphabet"] = cpp["alphabet"] == orc["alphabet"]
            ch["root primes"] = cpp["root_primes"] == orc["root_primes"]
            ch["A_s all depths"] = cpp["A"] == orc["A"]
            ch["rejected by interval per depth"] = cpp["rejected_interval_by_depth"][:N + 1] == orc["rejI"][:N + 1]
            ch["rejected by roots per depth"] = cpp["rejected_roots_by_depth"][:N + 1] == orc["rejR"][:N + 1]
            ch["leaf classification"] = all(cpp["leaves"][k] == orc["leaves"][k] for k in ("small", "even", "roots", "candidates"))
            ch["candidate list identical"] = cpp_cands == orc["candidates"]
            ch["initial-coordinate FH-interval == current-coordinate interval"] = orc["interval_equiv_fail"] == 0
            ch["root direct formula == update formula"] = orc["roots_formula_fail"] == 0
            ch["seed consistency (cpp)"] = cpp["seed_consistency_failures"] == 0
            ok = all(ch.values())
            all_ok &= ok
            results.append({"a": a, "b": b, "N": N, "A": cpp["A"], "leaves": cpp["leaves"], "n_candidates": len(cpp_cands),
                            "checks": ch, "all_pass": ok})
    out = {"check": "B-F1 sieve oracle comparison (small cases)", "results": results, "all_pass": all_ok, "status": "success",
           "summary": "; ".join("(%d,%d,%d): A=%s cand=%d pass=%s" % (r["a"], r["b"], r["N"], r["A"], r["n_candidates"], r["all_pass"]) for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
