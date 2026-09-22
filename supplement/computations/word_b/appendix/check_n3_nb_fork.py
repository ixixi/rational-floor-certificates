#!/usr/bin/env python3
"""B-N3: NB-FORK（audit-04 §3.2.5 補題 D と帰結）。b<60 の全既約 b<a<2b、奇数 Q<400；例 a=462u+77。"""
import json
from math import gcd
from obmath import primes_upto, is_prime

BMAX, QMAX = 60, 400


def ceil_div(n, d):
    return -((-n) // d)


def candidates(a, b, Q):
    lo = (a * Q) // b   # 候補は floor(aQ/b) .. ceil(a(Q+1)/b)-1（メモ §10.4）
    hi = ceil_div(a * (Q + 1), b) - 1
    return list(range(lo, hi + 1))


def main():
    n_pairs = n_forks = 0
    fails = []
    n_cond_pairs = 0
    n_cond_checked = 0
    for b in range(2, BMAX):
        for a in range(b + 1, 2 * b):
            if gcd(a, b) != 1:
                continue
            n_pairs += 1
            d = a - b
            ks = [k for k in range(1, d) if (k - a) % 2 == 0]
            cond = all(gcd(k, b) > 1 or gcd(d + k, a) > 1 or gcd(d - k, a) > 1 or ((a % 3 == 0) != (k % 3 == 0)) for k in ks)
            for Q in range(1, QMAX, 2):
                cs = candidates(a, b, Q)
                odd = [v for v in cs if v % 2 == 1]
                if len(odd) > 2:
                    fails.append({"a": a, "b": b, "Q": Q, "type": ">2 odd candidates"})
                if len(odd) == 2:
                    n_forks += 1
                    L = odd[0]
                    if odd[1] != L + 2:
                        fails.append({"a": a, "b": b, "Q": Q, "type": "odd candidates not L,L+2"})
                    C = L + 1
                    k = b * C - a * Q
                    ok = (1 <= k < d) and ((k - a) % 2 == 0) and (b * L == a * (Q - 1) + (d + k)) and (b * (L + 2) == a * (Q + 1) - (d - k))
                    if not ok:
                        fails.append({"a": a, "b": b, "Q": Q, "L": L, "k": k, "type": "lemma D"})
            if cond:
                n_cond_pairs += 1
                # 帰結: Q, L, L+2 > a が全て素数となる分岐はない
                for Q in primes_upto(5000):
                    if Q <= a:
                        continue
                    n_cond_checked += 1
                    odd = [v for v in candidates(a, b, Q) if v % 2 == 1]
                    if len(odd) == 2 and is_prime(odd[0]) and is_prime(odd[1]) and odd[0] > a:
                        fails.append({"a": a, "b": b, "Q": Q, "type": "prime fork despite condition"})
    # 例 a = 462u+77
    ex = []
    for u in range(0, 4):
        a, b = 462 * u + 77, 462 * u + 71
        d = a - b
        info = {"u": u, "a": a, "b": b, "gcd": gcd(a, b), "a<2b": a < 2 * b, "d": d,
                "k=1: 7|a": a % 7 == 0, "k=5: 11|a": a % 11 == 0, "k=3: 3∤a": a % 3 != 0}
        maxsucc = 0
        n_Q = 0
        for Q in primes_upto(3000):
            if Q <= a:
                continue
            n_Q += 1
            succ = [v for v in candidates(a, b, Q) if is_prime(v)]
            maxsucc = max(maxsucc, len(succ))
        info["n_prime_Q"] = n_Q
        info["max prime successors"] = maxsucc
        info["ok"] = gcd(a, b) == 1 and a < 2 * b and info["k=1: 7|a"] and info["k=5: 11|a"] and info["k=3: 3∤a"] and maxsucc <= 1
        ex.append(info)
    all_ok = not fails and all(e["ok"] for e in ex)
    out = {"check": "B-N3 NB-FORK", "b_max": BMAX, "Q_max": QMAX, "n_pairs": n_pairs, "n_forks": n_forks, "n_pairs_with_condition": n_cond_pairs,
           "n_prime_Q_checked_under_condition": n_cond_checked, "example_462u+77": ex, "n_failures": len(fails), "failures": fails[:20],
           "all_pass": all_ok, "status": "success",
           "summary": "%d pairs, %d two-odd-candidate forks satisfy lemma D; %d pairs with k-condition have no prime fork (%d primes); example 462u+77 max prime successors <=1: %s" % (
               n_pairs, n_forks, n_cond_pairs, n_cond_checked, all(e["ok"] for e in ex))}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
