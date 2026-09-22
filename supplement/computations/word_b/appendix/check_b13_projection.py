#!/usr/bin/env python3
"""B-13: 射影補題（audit-03 §3.3）。G(hM,fK) の全辺が同ラベルの G(M,K) の辺へ写る。"""
import json
from math import gcd
from obmath import edges_G, e1, e3

CASES = [(5, 2, 10, 4, 3, 2), (5, 2, 6, 2, 5, 3), (7, 5, 30, 4, 7, 2), (3, 2, 4, 3, 2, 2), (7, 5, 429, 4, 10, 2), (7, 5, 2, 8, 15, 4)]


def main():
    results = []
    all_ok = True
    for (a, b, M, K, h, f) in CASES:
        Ef = edges_G(a, b, h * M, f * K)
        Ec = set(edges_G(a, b, M, K))
        n_bad = 0
        n_direct_bad = 0
        for (q, J, z, H, e) in Ef:
            img = (q % M, J // f, z % M, H // f, e)
            if img not in Ec:
                n_bad += 1
            # 直接検査: E1, E2 (M | bz-aq-e), E3, 頂点の単元性
            if not (e1(a, b, e) and (b * (z % M) - a * (q % M) - e) % M == 0 and e3(a, b, K, J // f, H // f, e)
                    and gcd(q % M, M) == 1 and gcd(z % M, M) == 1):
                n_direct_bad += 1
        ok = n_bad == 0 and n_direct_bad == 0
        all_ok &= ok
        results.append({"a": a, "b": b, "M": M, "K": K, "h": h, "f": f, "fine_edges": len(Ef), "coarse_edges": len(Ec),
                        "not_mapped": n_bad, "direct_condition_failures": n_direct_bad, "all_pass": ok})
    out = {"check": "B-13 projection lemma", "results": results, "all_pass": all_ok, "status": "success",
           "summary": "; ".join("(%d,%d) G(%d,%d)->G(%d,%d): %d fine edges all map=%s" % (r["a"], r["b"], r["M"] * r["h"], r["K"] * r["f"], r["M"], r["K"], r["fine_edges"], r["all_pass"]) for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
