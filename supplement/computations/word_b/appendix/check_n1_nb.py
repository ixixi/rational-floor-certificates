#!/usr/bin/env python3
"""B-N1: NB（audit-04 §3.2.1）。t<=12、奇数 Q<=3000（3|Q を含む）で、真の後続候補 floor(r x)（x∈[Q,Q+1)）のうち
6 と互いに素なものが高々一つで T_t(Q) に等しい。"""
import json
from math import gcd

T0, Q0 = 12, 3000


def ceil_div(n, d):
    return -((-n) // d)


def main():
    n_checked = 0
    fails = []
    n_with = 0
    for t in range(1, T0 + 1):
        a, b = 6 * t + 3, 6 * t + 1
        for Q in range(1, Q0 + 1, 2):
            n_checked += 1
            lo = (a * Q) // b                       # floor(r x) >= floor(aQ/b)（メモ §10.4: 候補は floor(aQ/b) .. ceil(a(Q+1)/b)-1）
            hi = ceil_div(a * (Q + 1), b) - 1       # floor(r x) < a(Q+1)/b
            cands = [v for v in range(lo, hi + 1) if gcd(v, 6) == 1]
            Tt = Q + 2 * ((Q + 3 * t + 1) // b)
            if len(cands) > 1 or (len(cands) == 1 and cands[0] != Tt):
                fails.append({"t": t, "Q": Q, "cands": cands, "T": Tt})
            if cands:
                n_with += 1
                # 候補の存在は T_t(Q) が 6 と互いに素であることと同値
                if gcd(Tt, 6) != 1:
                    fails.append({"t": t, "Q": Q, "type": "T not coprime to 6 but candidate exists"})
            else:
                if gcd(Tt, 6) == 1:
                    fails.append({"t": t, "Q": Q, "type": "T coprime to 6 but no candidate"})
    out = {"check": "B-N1 NB", "T0": T0, "Q0": Q0, "n_checked": n_checked, "n_with_candidate": n_with, "n_failures": len(fails), "failures": fails[:20],
           "all_pass": not fails, "status": "success",
           "summary": "t<=%d, odd Q<=%d: %d cases, at most one 6-coprime successor and it equals T_t(Q); failures=%d" % (T0, Q0, n_checked, len(fails))}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
