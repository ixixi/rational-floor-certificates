#!/usr/bin/env python3
"""B-N4: NB-GAP（audit-04 §3.2.6）と §10.5.1（§3.2.7）。d<=30 の素数冪、表の 4 行、四族 u<=2、z∈[-20,200)。"""
import json
from math import gcd
from fractions import Fraction
from obmath import trial_factor, crt, floor_frac


def ceil_div(n, d):
    return -((-n) // d)


def main():
    results = []
    all_ok = True
    table = {}
    for d in range(2, 31):
        f = trial_factor(d)
        if len(f) != 1:
            continue
        p = next(iter(f))
        K = [k for k in range(1, d) if (k - (d + 1)) % 2 == 0]
        ells = {}
        ok = True
        for k in K:
            fac = [q for q in trial_factor(d + k) if q != p]
            if not fac or (d + k) % 2 == 0:
                ok = False
            ells[k] = min(fac) if fac else None
        Pd = 1
        for q in sorted(set(v for v in ells.values() if v)):
            Pd *= q
        ok &= gcd(Pd, 2 * d) == 1
        a0 = crt([(0, Pd), ((d + 1) % (2 * d), 2 * d)])
        mod = 2 * d * Pd
        a = a0
        while a <= 2 * d:
            a += mod
        b = a - d
        ok &= gcd(a, b) == 1 and a < 2 * b and (b - 1) % (2 * d) == 0
        ok &= all(gcd(d + k, a) > 1 for k in K)
        ok &= all((k - a) % 2 == 0 for k in K)   # K_d ⟺ k ≡ a (mod 2)
        # 数列 a = a0 + mod*u について u の下限
        u_min = (a - a0) // mod
        table[d] = {"p": p, "K_d": K, "ell_k": ells, "P_d": Pd, "a mod": mod, "a residue": a0, "min a>2d": a, "b": b, "u_min": u_min, "ok": ok}
        all_ok &= ok
    memo = {2: (12, 3, 1), 3: (30, 10, 0), 4: (280, 245, 0), 5: (210, 126, 0)}
    memo_match = all(table[d]["a mod"] == m and table[d]["a residue"] == r and table[d]["u_min"] == u for d, (m, r, u) in memo.items())
    # §10.5.1
    fam = []
    for d, (m, r0, u0) in memo.items():
        for u in range(u0, u0 + 3):
            a = m * u + r0
            b = a - d
            h = (b - 1) // (2 * d)
            H = 2 * h - 1
            rr = Fraction(a, b)
            fails = 0
            n = 0
            for z in range(-20, 200):
                n += 1
                Q = 2 * z + H
                zp = ceil_div(a * z, b)
                Qp = 2 * zp + H
                # r(Q+1) 未満の最大奇数
                bound = rr * (Q + 1)
                if not (Qp % 2 == 1 and Qp < bound and Qp + 2 >= bound):
                    fails += 1
                # 奇数候補があればその最大
                lo = (a * Q) // b   # 候補の下端は floor(aQ/b)
                hi = ceil_div(a * (Q + 1), b) - 1
                odd = [v for v in range(lo, hi + 1) if v % 2 == 1]
                if odd and max(odd) != Qp:
                    fails += 1
                e = b * zp - a * z
                if not (0 <= e < b):
                    fails += 1
                if gcd(Q, b) != gcd(2 * e + d + 1, b) or gcd(Qp, a) != gcd(2 * e + 2 * d + 1, a):
                    fails += 1
            fam.append({"d": d, "u": u, "a": a, "b": b, "h": h, "H": H, "n_z": n, "fails": fails})
            all_ok &= fails == 0
    all_ok &= memo_match
    out = {"check": "B-N4 NB-GAP and §10.5.1", "table": {str(k): v for k, v in table.items()}, "memo table match (d=2,3,4,5)": memo_match,
           "families_10_5_1": fam, "all_pass": all_ok, "status": "success",
           "summary": "prime powers d<=30: K_d, ell_k, gcd(P_d,2d)=1, CRT, gcd(a,b)=1, a<2b, gcd(d+k,a)>1 all=%s; memo 4 rows match=%s; §10.5.1 families fails=%d" % (
               all(v["ok"] for v in table.values()), memo_match, sum(x["fails"] for x in fam))}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
