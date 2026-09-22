#!/usr/bin/env python3
"""B-R2: REC-DIGIT（audit-04 §3.1.5）。t<=8、L<=3、z∈[-300,1200)。"""
import itertools
import json
from math import gcd

T0, L0 = 8, 3
ZLO, ZHI = -300, 1200


def ceil_div(n, d):
    return -((-n) // d)


def main():
    results = []
    all_ok = True
    for t in range(1, T0 + 1):
        a, b = 6 * t + 3, 6 * t + 1
        delta = t % 2
        H = 3 * t - 1 - delta

        def Tt(Q):
            return Q + 2 * ((Q + 3 * t + 1) // b)

        def F(z):
            return ceil_div(a * z - delta, b)

        def digit(z):
            return b * F(z) - a * z + delta

        ch = {}
        ch["H odd"] = H % 2 == 1
        ch["conjugacy T(2z+H)=2F(z)+H"] = all(Tt(2 * z + H) == 2 * F(z) + H for z in range(ZLO, ZHI))
        ch["0<=e<b"] = all(0 <= digit(z) < b for z in range(ZLO, ZHI))
        ch["e = delta - a z mod b"] = all((digit(z) - (delta - a * z)) % b == 0 for z in range(ZLO, ZHI))
        ch["c = 2(e-(3t-1))"] = all(b * Tt(2 * z + H) - a * (2 * z + H) == 2 * (digit(z) - (3 * t - 1)) for z in range(ZLO, ZHI))
        ch["Q' = 2e-1 mod 3"] = all((Tt(2 * z + H) - (2 * digit(z) - 1)) % 3 == 0 for z in range(ZLO, ZHI))
        ch["F(s+bv)=F(s)+av"] = all(F(s + b * v) == F(s) + a * v for s in range(b) for v in range(-5, 6))
        # 桁語 ↔ z mod b^L の全単射
        bij = True
        for L in range(1, L0 + 1):
            words = {}
            for z in range(b ** L):
                zz, w = z, []
                for _ in range(L):
                    w.append(digit(zz))
                    zz = F(zz)
                w = tuple(w)
                if w in words:
                    bij = False
                words[w] = z
            if len(words) != b ** L:                  # 衝突なし・被覆完全
                bij = False
            # 別代表で同語
            for z in range(0, b ** L, max(1, b ** L // 50)):
                for v in (1, -1, 3):
                    zz, w = z + v * b ** L, []
                    for _ in range(L):
                        w.append(digit(zz))
                        zz = F(zz)
                    if words.get(tuple(w)) != z:
                        bij = False
        ch["digit word <-> z mod b^L bijection (L<=%d)" % L0] = bij
        Dt = [e for e in range(0, b) if gcd(abs(e - (3 * t - 1)), a * b) == 1]
        ch["|D_t| <= 4t+1"] = len(Dt) <= 4 * t + 1
        ch["e=2 mod 3 excluded from D_t"] = all(e % 3 != 2 for e in Dt)
        ok = all(ch.values())
        all_ok &= ok
        results.append({"t": t, "a": a, "b": b, "delta": delta, "H": H, "D_t": Dt, "|D_t|": len(Dt), "checks": ch, "all_pass": ok})
    memo = {1: [0, 1, 3, 4, 6], 2: [1, 3, 4, 6, 7, 9, 12], 3: [0, 3, 4, 6, 7, 9, 10, 12, 13, 16, 18]}
    memo_match = all(results[t - 1]["D_t"] == memo[t] for t in memo)
    all_ok &= memo_match
    out = {"check": "B-R2 REC-DIGIT", "T0": T0, "L0": L0, "z_range": [ZLO, ZHI], "results": results, "memo D_t (t=1,2,3) match": memo_match,
           "all_pass": all_ok, "status": "success",
           "summary": "t<=%d: conjugacy, digits, c=2(e-(3t-1)), Q'=2e-1 (3), shift, bijection L<=%d, |D_t|<=4t+1 all=%s; D_1..D_3 match memo=%s" % (T0, L0, all_ok, memo_match)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
