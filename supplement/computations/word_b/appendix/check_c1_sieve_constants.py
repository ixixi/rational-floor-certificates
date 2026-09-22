#!/usr/bin/env python3
"""B-C1: 自分の列挙の A_s から定数 C（最小整数）と指数の整数不等式を検査。"""
import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
FH = os.path.join(ROOT, "build", "word-appendix", "fh")
CASES = [(6, 5, 40, "5^10", 5 ** 10, 10), (9, 7, 18, "7^9", 7 ** 9, 13)]


def min_C(A, ell):
    C = 1
    while True:
        if A[ell] <= C ** ell and all(A[s] ** ell <= C ** ell * A[ell] ** (s - 1) for s in range(1, ell)):
            return C
        C += 1


def main():
    results = []
    all_ok = True
    for (a, b, ell, powname, powval, memoC) in CASES:
        path = os.path.join(FH, "%d_%d_%d.counts.json" % (a, b, ell))
        counts = json.load(open(path))
        A = counts["A"]
        C = min_C(A, ell)
        ch = {}
        ch["A_ell <= C^ell"] = A[ell] <= C ** ell
        ch["A_s^ell <= C^ell A_ell^(s-1) for 1<=s<ell"] = all(A[s] ** ell <= C ** ell * A[ell] ** (s - 1) for s in range(1, ell))
        ch["C minimal"] = (C == 1) or not (A[ell] <= (C - 1) ** ell and all(A[s] ** ell <= (C - 1) ** ell * A[ell] ** (s - 1) for s in range(1, ell)))
        ch["A_ell < %s" % powname] = A[ell] < powval
        ok = all(ch.values())
        all_ok &= ok
        results.append({"a": a, "b": b, "ell": ell, "counts_sha256": hashlib.sha256(open(path, "rb").read()).hexdigest(),
                        "A": A, "A_ell": A[ell], "C_min": C, "memo_C": memoC, "C_min == memo_C (observation)": C == memoC,
                        powname: powval, "checks": ch, "all_pass": ok})
    out = {"check": "B-C1 sieve constants", "results": results, "all_pass": all_ok, "status": "success",
           "summary": "; ".join("(%d,%d) ell=%d: A_ell=%d, C_min=%d (memo %d), A_ell<pow=%s" % (r["a"], r["b"], r["ell"], r["A_ell"], r["C_min"], r["memo_C"], list(r["checks"].values())[3]) for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
