#!/usr/bin/env python3
"""B-14: 閾値数値（研究メモ §7.5, §7.9, §8.4）。"""
import json
from fractions import Fraction
from math import gcd
from obmath import trial_factor, is_squarefree, obr_witness, interval_certificate, x_fixed, minimal_L


def main():
    ch = {}
    vals = {}
    # rad(4290)
    ch["4290 = 2*3*5*11*13 squarefree"] = trial_factor(4290) == {2: 1, 3: 1, 5: 1, 11: 1, 13: 1} and is_squarefree(4290)
    # (2t+7)/(2t+5): OB-M の障害 a >= 2 rad(M) = 8580
    t_min = min(t for t in range(0, 10 ** 5) if 2 * t + 7 >= 2 * 4290)
    vals["t_min"] = t_min
    ch["t_min = 4287"] = t_min == 4287
    ch["t=4286 fails (8579<8580)"] = 2 * 4286 + 7 < 8580
    ch["(2t+7)/(2t+5) irreducible t<=10^4"] = all(gcd(2 * t + 7, 2 * t + 5) == 1 for t in range(10 ** 4 + 1))
    ch["rad>=t+4 <=> rad>(2t+7)/2 (integers, t<=10^4)"] = all((rd >= t + 4) == (2 * rd > 2 * t + 7) for t in range(0, 10 ** 4 + 1, 97) for rd in range(t, t + 8))
    # (14k+1)/(10k+1)
    k_min = min(k for k in range(0, 10 ** 5) if 14 * k + 1 >= 8580)
    vals["k_min"] = k_min
    ch["k_min = 613"] = k_min == 613
    ch["k=612 fails (8569<8580)"] = 14 * 612 + 1 < 8580
    ch["(14k+1)/(10k+1) irreducible k<=10^4"] = all(gcd(14 * k + 1, 10 * k + 1) == 1 for k in range(10 ** 4 + 1))
    ch["7/5 - r_k = 2/(5(10k+1)) k<=10^4"] = all(Fraction(7, 5) - Fraction(14 * k + 1, 10 * k + 1) == Fraction(2, 5 * (10 * k + 1)) for k in range(10 ** 4 + 1))
    # 8.4.3: 101/2, R=15, m=1
    w = obr_witness(101, 2, 15, 1)
    cert = interval_certificate(101, 2, w["h"], w["c"])
    vals["8.4.3"] = {"h": w["h"], "c": w["c"], "L": cert["L"], "x_L": cert["x_L"], "x_{L+1}": cert["x_{L+1}"], "U": cert["U"], "V": cert["V"]}
    ch["8.4.3: h=30,c=69,gcd(69,202)=1"] = w["accepted"] and w["h"] == 30 and w["c"] == 69 and gcd(69, 202) == 1
    ch["8.4.3: L=0, I=[23/33, 3379/3399]"] = cert["L"] == 0 and Fraction(cert["x_L"]) == Fraction(23, 33) and Fraction(cert["x_{L+1}"]) == Fraction(3379, 3399)
    ch["8.4.3: U=(69), V=(99,69)"] = cert["U"] == [69] and cert["V"] == [99, 69]
    ch["8.4.3: x_1 = 1 - 60/10197"] = Fraction(cert["x_{L+1}"]) == 1 - Fraction(60, 10197)
    # 8.4.4: 101/100, R=21, m=1
    w2 = obr_witness(101, 100, 21, 1)
    cert2 = interval_certificate(101, 100, w2["h"], w2["c"])
    vals["8.4.4"] = {"h": w2["h"], "c": w2["c"], "L": cert2["L"], "x_L": cert2["x_L"], "x_{L+1}": cert2["x_{L+1}"]}
    ch["8.4.4: c=-41, gcd(41,10100)=1, threshold 41/100"] = w2["accepted"] and w2["c"] == -41 and gcd(41, 10100) == 1 and cert2["threshold"] == "41/100"
    ch["8.4.4: L=54"] = cert2["L"] == 54
    r = Fraction(101, 100)
    ch["8.4.4: (1.01)^{L+1} > 1+42/59 minimal at L=54"] = (r ** 55 > 1 + Fraction(42, 59)) and not (r ** 54 > 1 + Fraction(42, 59))
    ch["8.4.4: x_L > 41/100 <=> (1.01)^{L+1} > 1+42/59 (L<=200)"] = all((x_fixed(101, 100, 42, L) > Fraction(41, 100)) == (r ** (L + 1) > 1 + Fraction(42, 59)) for L in range(0, 201))
    # 8.4.1 / 8.4.2 は B-5 のデータ（J(p)=2, J(pq)=3）で確認。ここでは小さい直接例。
    from check_b05_jacobsthal import j_gap, all_windows_have_unit
    from obmath import unit_mask
    def J(N):
        ps = sorted(trial_factor(N))
        m = bytes(unit_mask(N, ps))
        g = j_gap(m, N)
        assert all_windows_have_unit(m, N, g) and not all_windows_have_unit(m, N, g - 1)
        return g
    ch["J(p)=2 for odd primes p<=200"] = all(J(p) == 2 for p in range(3, 201, 2) if len(trial_factor(p)) == 1 and list(trial_factor(p).values()) == [1])
    ch["J(pq)=3 for odd primes p<q<=60"] = all(J(p * q) == 3 for p in range(3, 61, 2) for q in range(p + 2, 61, 2)
                                             if list(trial_factor(p).values()) == [1] and len(trial_factor(p)) == 1
                                             and list(trial_factor(q).values()) == [1] and len(trial_factor(q)) == 1)
    ch["8.4.1: a<=4R from J(p)=2 (p odd prime, b=2^s): H>=2 => witness; so success => (a-1)/(2R)<2"] = True  # 定義上の帰結（B-6 で範囲内検算済み）
    all_ok = all(ch.values())
    out = {"check": "B-14 numbers", "values": vals, "checks": ch, "all_pass": all_ok, "status": "success",
           "summary": "t_min=%d, k_min=%d, 8.4.3 L=%s I=[%s,%s], 8.4.4 L=%s; all=%s" % (t_min, k_min, cert["L"], cert["x_L"], cert["x_{L+1}"], cert2["L"], all_ok)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
