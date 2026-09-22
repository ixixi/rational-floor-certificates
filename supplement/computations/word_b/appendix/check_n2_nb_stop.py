#!/usr/bin/env python3
"""B-N2: NB-STOP プログラム（研究メモ §10.3、audit-04 §3.2.3）の区間更新の正確性・健全性。
t∈{1,2,3}、素数 a<P<400。T 軌道の語で、最終区間の内点の引き戻しと格子点からの前向き経路を検査。"""
import json
from fractions import Fraction
from obmath import primes_upto, trial_factor, psi

TS = [1, 2, 3]
PMAX = 400
NMAX = 8
DGRID = 64


def main():
    results = []
    all_ok = True
    for t in TS:
        a, b = 6 * t + 3, 6 * t + 1
        stats = {"n_P": 0, "stopped_composite": 0, "stopped_empty": 0, "reached_nmax": 0, "exact_fail": 0, "sound_fail": 0, "empty_realized": 0, "n_pull": 0, "n_paths": 0}
        for P in primes_upto(PMAX):
            if P <= a:
                continue
            stats["n_P"] += 1
            Q = P
            L, U, B = 0, 1, 1
            ivs = [(L, U, B)]
            word = []
            stop = None
            for n in range(NMAX):
                Qn = Q + 2 * ((Q + 3 * t + 1) // b)
                c = b * Qn - a * Q
                f = trial_factor(Qn)
                if not (len(f) == 1 and list(f.values()) == [1]):
                    stop = ("composite", n + 1)
                    break
                B2, L2, U2 = b * B, max(0, a * L - c * B), min(b * B, a * U - c * B)
                word.append(c)
                ivs.append((L2, U2, B2))
                if L2 >= U2:
                    stop = ("empty", n + 1)
                    break
                L, U, B, Q = L2, U2, B2, Qn
            if stop is None:
                stats["reached_nmax"] += 1
            elif stop[0] == "composite":
                stats["stopped_composite"] += 1
            else:
                stats["stopped_empty"] += 1
            nfull = len(word) if (stop is None or stop[0] == "composite") else len(word) - 1  # 非空の最終段
            # 正確性: 非空の各段 k<=nfull で、区間内点の引き戻しが各段の区間に入る
            for k in range(1, nfull + 1):
                Lk, Uk, Bk = ivs[k]
                for x in (Fraction(Lk, Bk), Fraction(Lk + Uk, 2 * Bk), Fraction(Uk - 1, Bk)):
                    stats["n_pull"] += 1
                    y = x
                    ok = Fraction(Lk, Bk) <= y < Fraction(Uk, Bk)
                    for i in range(k - 1, -1, -1):
                        y = psi(a, b, word[i], y)
                        Li, Ui, Bi = ivs[i]
                        if not (Fraction(Li, Bi) <= y < Fraction(Ui, Bi)):
                            ok = False
                    if not ok:
                        stats["exact_fail"] += 1
            # 健全性: 格子点 θ_0 から前向き
            for s in range(DGRID):
                x = Fraction(s, DGRID)
                xs = [x]
                for i, c in enumerate(word):
                    y = (a * xs[-1] - c) / b
                    if not (0 <= y < 1):
                        break
                    xs.append(y)
                if len(xs) == len(word) + 1:
                    stats["n_paths"] += 1
                for i, y in enumerate(xs):
                    Li, Ui, Bi = ivs[i]
                    if not (Fraction(Li, Bi) <= y < Fraction(Ui, Bi)):
                        stats["sound_fail"] += 1
                    if stop is not None and stop[0] == "empty" and i >= stop[1]:
                        stats["empty_realized"] += 1
        ok = stats["exact_fail"] == 0 and stats["sound_fail"] == 0 and stats["empty_realized"] == 0
        all_ok &= ok
        results.append({"t": t, "a": a, "b": b, "stats": stats, "all_pass": ok})
    out = {"check": "B-N2 NB-STOP program interval exactness/soundness", "P_max": PMAX, "n_max": NMAX, "grid": DGRID, "results": results,
           "all_pass": all_ok, "status": "success",
           "summary": "; ".join("t=%d: %d primes, composite-stop %d, empty-stop %d, reached %d steps %d; fails exact=%d sound=%d" % (
               r["t"], r["stats"]["n_P"], r["stats"]["stopped_composite"], r["stats"]["stopped_empty"], NMAX, r["stats"]["reached_nmax"], r["stats"]["exact_fail"], r["stats"]["sound_fail"]) for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
