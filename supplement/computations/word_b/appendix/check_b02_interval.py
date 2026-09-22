#!/usr/bin/env python3
"""B-2: 不変区間 I=[x_L, x_{L+1}] の証明書（audit-03 §3.9.2, §5 B-2）。"""
import json
from obmath import obr_witness, interval_certificate

WITNESSES = [
    (101, 2, 15, 1), (101, 2, 15, 2), (101, 2, 15, 3),
    (101, 100, 21, 1),
    (5, 2, 1, 1), (5, 2, 1, 2),
    (7, 5, 1, 2), (7, 5, 1, 3), (7, 5, 3, 1),
    (9, 7, 1, 2), (6, 5, 1, 1), (3, 2, 1, 1), (4, 3, 1, 1),
]
LMAX = 5000


def main():
    results = []
    all_ok = True
    inconclusive = False
    for (a, b, R, m) in WITNESSES:
        w = obr_witness(a, b, R, m)
        if not w["accepted"]:
            all_ok = False
            results.append({"witness": [a, b, R, m], "error": "B-1 rejected"})
            continue
        cert = interval_certificate(a, b, w["h"], w["c"], Lmax=LMAX)
        cert["witness"] = [a, b, R, m]
        if cert["status"] != "success":
            inconclusive = True
        elif not cert["all_pass"]:
            all_ok = False
        results.append(cert)
    out = {
        "check": "B-2 invariant interval",
        "Lmax": LMAX,
        "results": results,
        "all_pass": all_ok and not inconclusive,
        "status": "inconclusive" if inconclusive else "success",
        "summary": "; ".join("%s: L=%s I=[%s, %s] pass=%s" % (r.get("witness"), r.get("L"), r.get("x_L"), r.get("x_{L+1}"), r.get("all_pass"))
                             for r in results),
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
