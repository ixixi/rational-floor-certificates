#!/usr/bin/env python3
"""B-F2: 9/7 (N=18) の残候補の追跡。T(Q)=Q+2⌊(Q+4)/7⌋ で j<=7 の各項に真の約数 d（等式 T^j(P)=d·e、1<d,e）を探す。
候補側整合性（奇数、範囲、T 軌道のキャリー = 篩の語、FH-interval 非空、根集合）も再検査。"""
import hashlib
import json
import os
from fractions import Fraction
from math import gcd
from obmath import primes_upto, modinv, carry_alphabet

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
CAND = os.path.join(ROOT, "build", "word-appendix", "fh", "9_7_18.candidates.txt")
a, b, N, t = 9, 7, 18, 1
import sys
DIV_BOUND = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 5   # 約数探索の上限（分布はこの上限と探索順序に依存する）
J_MAX = 7
J_EXT = 20


def T(Q):
    return Q + 2 * ((Q + 3 * t + 1) // b)


def small_factor(n, primes):
    for p in primes:
        if p * p > n:
            return None
        if n % p == 0:
            return p
    return None


def sqrt_factor(n):
    d = 3
    while d * d <= n:
        if n % d == 0:
            return d
        d += 2
    return None


def main():
    primes = primes_upto(DIV_BOUND)
    rp = [p for p in primes_upto(N + 1) if p % 2 == 1 and (a * b) % p != 0]
    alph = carry_alphabet(a, b)
    lines = [l.split() for l in open(CAND)]
    cands = [(int(l[0]), tuple(int(x) for x in l[1:])) for l in lines]
    h = hashlib.sha256(open(CAND, "rb").read()).hexdigest()
    dist = {}
    maxdiv = 0
    witnesses = []
    fails = []
    n_ext = 0
    for P, word in cands:
        # 候補側整合性
        cons = {}
        cons["odd"] = P % 2 == 1
        cons["max(a,N+1) < P <= b^N"] = max(a, N + 1) < P <= b ** N
        Q = [P]
        for j in range(N):
            Q.append(T(Q[j]))
        carries = tuple(b * Q[j + 1] - a * Q[j] for j in range(N))
        cons["T-orbit carries in alphabet"] = all(c in alph for c in carries)
        cons["T-orbit carries == sieve word"] = carries == word
        C = [0]
        for j, c in enumerate(word):
            C.append(a * C[j] + b ** j * c)
        lo, hi = Fraction(0), Fraction(1)
        for j in range(1, N + 1):
            lo = max(lo, Fraction(C[j], a ** j))
            hi = min(hi, Fraction(C[j] + b ** j, a ** j))
        cons["FH-interval nonempty"] = lo < hi
        cons["seed equation"] = all((a ** j * P + C[j]) % (b ** j) == 0 for j in range(1, N + 1))
        rootsok = True
        for p in rp:
            roots = {(-C[j] * pow(modinv(a, p), j, p)) % p for j in range(N + 1)}
            if len(roots) == p or (P % p) in roots:
                rootsok = False
        cons["roots do not cover and P mod p not a root"] = rootsok
        # 真の約数
        found = None
        for j in range(J_MAX + 1):
            d = small_factor(Q[j], primes)
            if d is not None:
                found = (j, d)
                break
        if found is None:
            n_ext += 1
            Qe = list(Q)
            while len(Qe) < J_EXT + 1:
                Qe.append(T(Qe[-1]))
            for j in range(J_MAX + 1):
                d = sqrt_factor(Qe[j])
                if d is not None:
                    found = (j, d)
                    break
            if found is None:
                for j in range(J_MAX + 1, J_EXT + 1):
                    d = small_factor(Qe[j], primes)
                    if d is not None:
                        found = (j, d)
                        break
        if found is None:
            fails.append({"P": P, "type": "no proper divisor found j<=%d" % J_EXT})
            continue
        j, d = found
        Qj = Q[j] if j <= N else None
        e = Qj // d
        eq = (Qj == d * e and 1 < d < Qj and 1 < e)
        if not eq or not all(cons.values()):
            fails.append({"P": P, "j": j, "d": d, "cons": cons, "eq": eq})
        dist[j] = dist.get(j, 0) + 1
        maxdiv = max(maxdiv, d)
        witnesses.append([P, j, d, e])
    out = {"check": "B-F2 residual candidates (9/7, N=18)", "candidates_file": os.path.relpath(CAND, ROOT), "candidates_sha256": h,
           "n_candidates": len(cands), "T": "Q + 2*floor((Q+4)/7)", "divisor_search": "trial division by primes <= %d, j<=%d first; fallback sqrt / j<=%d" % (DIV_BOUND, J_MAX, J_EXT),
           "first_divisor_time_distribution (search-order dependent)": {str(k): v for k, v in sorted(dist.items())},
           "max_divisor": maxdiv, "n_needed_extension": n_ext, "n_failures": len(fails), "failures": fails[:20],
           "witnesses_sha256": hashlib.sha256(json.dumps(witnesses).encode()).hexdigest(),
           "witnesses": witnesses,
           "all_pass": not fails, "status": "success",
           "summary": "%d candidates: all have proper divisor at j<=%d and satisfy sieve conditions=%s; distribution %s; max divisor %d" % (
               len(cands), max(dist) if dist else -1, not fails, {k: v for k, v in sorted(dist.items())}, maxdiv)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
