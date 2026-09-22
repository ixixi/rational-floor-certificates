#!/usr/bin/env python3
"""B-8: NO-EXTERNAL（audit-03 §3.14）。a<=A の全既約対で場合分けの証人が B-1 を通り、B-2 の区間証明書が構成できる。"""
import json
import sys
from math import gcd
from obmath import obr_witness, interval_certificate

A_MAX = int(sys.argv[1]) if len(sys.argv) > 1 else 500
LMAX = 5000


def no_external_witness(a, b):
    D = a - b
    if D >= 3 and D % 2 == 1:
        c, case = 1, "odd>=3"
    elif D >= 4 and D % 2 == 0:
        c, case = 2, "even>=4"
    elif D == 1:
        c, case = -1, "D=1"
    elif D == 2:
        c, case = -2, "D=2"
    else:
        raise ValueError
    h = D - c
    return c, h, h // 2, case


def main():
    n_pairs = 0
    fails = []
    case_count = {}
    L_hist = {}
    maxL = (0, None)
    inconclusive = 0
    for a in range(3, A_MAX + 1):
        for b in range(2, a):
            if gcd(a, b) != 1:
                continue
            n_pairs += 1
            c, h, m, case = no_external_witness(a, b)
            case_count[case] = case_count.get(case, 0) + 1
            if h % 2 != 0 or m < 1 or h > a - 1:
                fails.append({"a": a, "b": b, "type": "h/m range"})
                continue
            w = obr_witness(a, b, 1, m)
            if not (w["accepted"] and w["derived_all"] and w["c"] == c and w["h"] == h):
                fails.append({"a": a, "b": b, "type": "B-1", "w": w})
                continue
            cert = interval_certificate(a, b, h, c, Lmax=LMAX)
            if cert["status"] != "success":
                inconclusive += 1
                continue
            if not cert["all_pass"]:
                fails.append({"a": a, "b": b, "type": "B-2", "checks": cert["checks"]})
                continue
            L = cert["L"]
            L_hist[L] = L_hist.get(L, 0) + 1
            if L > maxL[0]:
                maxL = (L, [a, b])
    out = {"check": "B-8 NO-EXTERNAL", "A_max": A_MAX, "n_coprime_pairs": n_pairs, "case_count": case_count,
           "L_histogram": {str(k): v for k, v in sorted(L_hist.items())}, "max_L": maxL,
           "n_inconclusive": inconclusive, "failures": fails[:50], "n_failures": len(fails),
           "all_pass": not fails and inconclusive == 0,
           "status": "inconclusive" if inconclusive else "success",
           "summary": "%d coprime pairs a<=%d: B-1 and full B-2 certificate pass for all=%s; max L=%s" % (n_pairs, A_MAX, not fails and inconclusive == 0, maxL)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
