#!/usr/bin/env python3
"""B-L1: LONG-PREFIX（audit-04 §3.4.1）と §12.3 の 9 項例。有理数演算、試し割り素数判定。"""
import json
from fractions import Fraction
from obmath import floor_frac, is_prime, primes_upto, trial_factor


def lemma_checks(P, D, L):
    """補題の全不等式と床の一致。"""
    ch = {}
    ch["all L terms prime > 3"] = all(is_prime(P + j * D) and P + j * D > 3 for j in range(L))
    ch["P > 48 L^2 D^2"] = P > 48 * L * L * D * D
    ch["6 | D"] = D % 6 == 0
    target = Fraction(2 * P, D)
    # b ≡ 1 (mod 6) で 2P/D に最も近い整数
    cands = [x for x in range(floor_frac(target) - 6, floor_frac(target) + 7) if x % 6 == 1]
    b = min(cands, key=lambda x: (abs(Fraction(x) - target), x))
    a = b + 2
    t = (b - 1) // 6
    xi = Fraction(P) + Fraction(1, 2)
    ch["|b - 2P/D| <= 3"] = abs(Fraction(b) - target) <= 3
    ch["b >= P/D"] = Fraction(b) >= Fraction(P, D)
    ch["t >= 1"] = t >= 1
    ch["|(2P+1)/b - D| <= 4D^2/P"] = abs(Fraction(2 * P + 1, b) - D) <= Fraction(4 * D * D, P)
    r = Fraction(a, b)
    errs_ok = True
    floors_ok = True
    for j in range(L):
        v = xi * r ** j
        err = abs(v - (P + j * D + Fraction(1, 2)))
        bound = Fraction((4 * j + 8 * j * j) * D * D, P)
        if not (err <= bound <= Fraction(12 * L * L * D * D, P) < Fraction(1, 4)):
            errs_ok = False
        if floor_frac(v) != P + j * D:
            floors_ok = False
    ch["per-j error <= (4j+8j^2)D^2/P <= 12L^2D^2/P < 1/4"] = errs_ok
    ch["floor(xi r^j) = P + jD"] = floors_ok
    ch["P > a"] = P > a
    return {"P": P, "D": D, "L": L, "b": b, "a": a, "t": t, "checks": ch, "all_pass": all(ch.values())}


def main():
    results = []
    # 9 項例
    t, P, D, L = 1654617, 1042408919, 210, 9
    a, b = 6 * t + 3, 6 * t + 1
    xi = Fraction(2084817839, 2)
    r = Fraction(a, b)
    ex = {"t": t, "a": a, "b": b, "xi": str(xi)}
    vals = [floor_frac(xi * r ** j) for j in range(10)]
    ex["floors_j<=9"] = vals
    ex["checks"] = {
        "a=9927705, b=9927703": (a, b) == (9927705, 9927703),
        "xi = P + 1/2": xi == P + Fraction(1, 2),
        "floor = P + 210 j (0<=j<=8)": all(vals[j] == P + 210 * j for j in range(9)),
        "9 terms prime (trial division)": all(is_prime(vals[j]) for j in range(9)),
        "j=9: 1042410809 = 11 * 94764619": vals[9] == 1042410809 == 11 * 94764619,
        "j=9 composite": not is_prime(vals[9]),
        "lemma hypotheses hold": lemma_checks(P, D, L)["all_pass"],
        "b nearest to 2P/D among b=1 mod 6": lemma_checks(P, D, L)["b"] == b,
    }
    ex["all_pass"] = all(ex["checks"].values())
    results.append(ex)
    # 小さい素数等差数列
    small = []
    ps = primes_upto(3 * 10 ** 6)
    pset = set(ps)
    for L in (3, 4):
        for D in (6, 12, 30):
            thr = 48 * L * L * D * D
            found = None
            for P in ps:
                if P > thr and all((P + j * D) in pset for j in range(L)):
                    found = P
                    break
            rec = lemma_checks(found, D, L)
            small.append(rec)
    all_ok = ex["all_pass"] and all(s["all_pass"] for s in small)
    out = {"check": "B-L1 LONG-PREFIX", "nine_term_example": ex, "small_APs": small, "all_pass": all_ok, "status": "success",
           "summary": "9-term example floors/primes/j=9 factor ok=%s; small APs (L in 3,4; D in 6,12,30) lemma inequalities and floors ok=%s" % (ex["all_pass"], all(s["all_pass"] for s in small))}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
