#!/usr/bin/env python3
"""B-12: DOM-A / DOM-B の有限言語一致（audit-03 §3.4, §3.5）。"""
import json
from obmath import edges_G, edges_Gprime, rad, language, units

DOM_A = [(5, 2, 8, 4, 5), (5, 2, 20, 4, 5), (5, 2, 50, 3, 4), (7, 5, 25, 4, 4), (7, 5, 18, 4, 4),
         (3, 2, 16, 4, 5), (4, 3, 27, 4, 5), (5, 2, 900, 2, 3)]
DOM_B = [(5, 2, 1, 4, 5), (5, 2, 3, 4, 5), (7, 5, 1, 4, 4), (7, 5, 3, 2, 4), (3, 2, 5, 3, 5), (4, 3, 5, 4, 5)]


def verts(M, K):
    return [(q, j) for q in units(M) for j in range(K)]


def main():
    results = []
    all_ok = True
    for (a, b, M, K, n) in DOM_A:
        r = rad(M)
        E1 = edges_G(a, b, M, K)
        E2 = edges_G(a, b, r, K)
        L1 = language(E1, K, n, verts(M, K))
        L2 = language(E2, K, n, verts(r, K))
        ok = (L1 == L2)
        all_ok &= ok
        results.append({"lemma": "DOM-A", "a": a, "b": b, "M": M, "rad": r, "K": K, "n": n,
                        "edges_G(M,K)": len(E1), "edges_G(rad,K)": len(E2), "lang_size": len(L1), "lang_size_rad": len(L2),
                        "equal": ok, "only_in_M": len(L1 - L2), "only_in_rad": len(L2 - L1)})
    for (a, b, R, K, n) in DOM_B:
        M0 = rad(2 * a * b)
        E1 = edges_G(a, b, M0 * R, K)
        E2 = edges_Gprime(a, b, R, K)
        L1 = language(E1, K, n, verts(M0 * R, K))
        L2 = language(E2, K, n, verts(R, K))
        ok = (L1 == L2)
        all_ok &= ok
        results.append({"lemma": "DOM-B", "a": a, "b": b, "M0": M0, "R": R, "K": K, "n": n,
                        "edges_G(M0R,K)": len(E1), "edges_G'(R,K)": len(E2), "lang_size": len(L1), "lang_size_prime": len(L2),
                        "equal": ok, "only_in_full": len(L1 - L2), "only_in_prime": len(L2 - L1)})
    out = {"check": "B-12 DOM-A/DOM-B finite languages", "results": results, "all_pass": all_ok, "status": "success",
           "summary": "; ".join("%s (%d,%d,%s,K=%d,n<=%d) equal=%s |L|=%d" % (r["lemma"], r["a"], r["b"], r.get("M", "R=%d" % r.get("R", 0)), r["K"], r["n"], r["equal"], r["lang_size"]) for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
