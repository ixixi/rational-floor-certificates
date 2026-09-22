#!/usr/bin/env python3
"""B-F3: 小さい初期素数（6/5: 7..41、9/7: 11..19）の個別検査。証人: 真の約数の等式／素数後続なし／空区間（現在座標と初期座標）。"""
import json
from fractions import Fraction
from math import gcd
from obmath import is_prime, primes_upto, trial_factor

CASES = {(6, 5): [p for p in primes_upto(41) if p > 6], (9, 7): [p for p in primes_upto(19) if p > 9]}
MAX_STEPS = 40


def successor(a, b, Q):
    """全素数尾部で唯一可能な後続項。(Q', c, reason)。reason None なら後続あり。"""
    if (a, b) == (6, 5):
        r = Q % 5
        if r == 1:
            c = -1
        elif r == 4:
            c = 1
        else:
            return None, None, "no prime successor (Q mod 5 = %d not in {1,4})" % r
        return (6 * Q + c) // 5, c, None
    if (a, b) == (9, 7):
        Qn = Q + 2 * ((Q + 4) // 7)   # T_1
        return Qn, 7 * Qn - 9 * Q, None
    raise ValueError


def main():
    results = []
    all_ok = True
    maxtime = {}
    for (a, b), ps in CASES.items():
        for P in ps:
            Q = P
            L, U, B = 0, 1, 1
            lo, hi = Fraction(0), Fraction(1)   # 初期座標
            C = 0
            trail = []
            witness = None
            for j in range(MAX_STEPS):
                # 現在項の真の約数
                f = trial_factor(Q)
                if not (len(f) == 1 and list(f.values()) == [1]):
                    d = min(f)
                    witness = {"time": j, "type": "proper divisor", "Q": Q, "d": d, "e": Q // d, "eq": Q == d * (Q // d)}
                    break
                Qn, c, reason = successor(a, b, Q)
                if reason is not None:
                    witness = {"time": j, "type": reason, "Q": Q}
                    break
                # 区間更新（現在座標）
                B2 = b * B
                L2 = max(0, a * L - c * B)
                U2 = min(B2, a * U - c * B)
                # 初期座標
                C = a * C + b ** j * c
                lo2 = max(lo, Fraction(C, a ** (j + 1)))
                hi2 = min(hi, Fraction(C + b ** (j + 1), a ** (j + 1)))
                trail.append({"j": j, "Q": Q, "c": c, "L": L2, "U": U2, "B": B2, "lo": str(lo2), "hi": str(hi2)})
                if (L2 >= U2) != (lo2 >= hi2):
                    witness = {"time": j + 1, "type": "INCONSISTENT interval representations"}
                    break
                if L2 >= U2:
                    witness = {"time": j + 1, "type": "empty interval", "L": L2, "U": U2, "B": B2, "lo": str(lo2), "hi": str(hi2), "Q_next": Qn}
                    break
                L, U, B, lo, hi, Q = L2, U2, B2, lo2, hi2, Qn
            ok = witness is not None and witness["type"] != "INCONSISTENT interval representations"
            all_ok &= ok
            key = "%d/%d" % (a, b)
            maxtime[key] = max(maxtime.get(key, 0), witness["time"] if witness else 99)
            results.append({"base": key, "P": P, "witness": witness, "trail": trail, "all_pass": ok})
    ch = {"6/5 max time <= 2": maxtime.get("6/5", 99) <= 2, "9/7 max time <= 4": maxtime.get("9/7", 99) <= 4}
    all_ok &= all(ch.values())
    out = {"check": "B-F3 small initial primes", "results": results, "max_time": maxtime, "checks": ch, "all_pass": all_ok, "status": "success",
           "summary": "; ".join("%s P=%d: t=%s %s" % (r["base"], r["P"], r["witness"]["time"] if r["witness"] else None, r["witness"]["type"] if r["witness"] else "NONE") for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
