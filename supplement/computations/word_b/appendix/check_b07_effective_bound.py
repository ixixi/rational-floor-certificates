#!/usr/bin/env python3
"""B-7: 有効上限 k_0（audit-03 §3.10 末尾）。"""
import json
from fractions import Fraction
from math import factorial

R0S = [1, 3, 15, 21, 429, 4290, 30030]
EXTRA = 60


def main():
    results = []
    all_ok = True
    for R0 in R0S:
        def rho(k):
            return Fraction(2 ** k * factorial(k), 4 * R0 * R0 * 9 ** k)
        k0 = 4
        while not rho(k0) > 1:
            k0 += 1
        ch = {}
        ch["rho monotone nondecreasing k>=4"] = all(rho(k + 1) >= rho(k) for k in range(4, k0 + EXTRA))
        ch["rho_{k+1}/rho_k = 2(k+1)/9 >= 1 for k>=4"] = all(rho(k + 1) / rho(k) == Fraction(2 * (k + 1), 9) and Fraction(2 * (k + 1), 9) >= 1 for k in range(4, k0 + EXTRA))
        ch["rho_k > 1 for k0<=k<=k0+60"] = all(rho(k) > 1 for k in range(k0, k0 + EXTRA + 1))
        ch["rho_k <= 1 for 4<=k<k0"] = all(rho(k) <= 1 for k in range(4, k0))
        ch["2^k0 k0! > 4 R0^2 9^k0"] = 2 ** k0 * factorial(k0) > 4 * R0 * R0 * 9 ** k0
        ok = all(ch.values())
        all_ok &= ok
        results.append({"R0": R0, "k0": k0, "a_bound=2*R0*3^(k0-1)": 2 * R0 * 3 ** (k0 - 1), "checks": ch, "all_pass": ok})
    out = {"check": "B-7 effective bound", "results": results, "all_pass": all_ok, "status": "success",
           "summary": "; ".join("R0=%d: k0=%d, a<=%d" % (r["R0"], r["k0"], r["a_bound=2*R0*3^(k0-1)"]) for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
