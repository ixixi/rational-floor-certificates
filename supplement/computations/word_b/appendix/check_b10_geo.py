#!/usr/bin/env python3
"""B-10: GEO 全語区間検査の正確性と健全性（audit-03 §3.15）。"""
import itertools
import json
from fractions import Fraction
from obmath import sigma, psi

CASES = [(3, 2, 3), (5, 2, 4), (5, 2, 1), (4, 3, 5), (7, 5, 4), (7, 5, 8), (9, 7, 4)]
FULL_LATTICE = {(3, 2, 3), (5, 2, 4)}
MAXLEN = 3
DGRID = 12


def interval_run(a, b, K, j, word):
    ivs = [(j, j + 1, K)]
    L, U, B = j, j + 1, K
    for i, c in enumerate(word):
        B2 = b * B
        L2 = max(0, a * L - c * B)
        U2 = min(B2, a * U - c * B)
        ivs.append((L2, U2, B2))
        L, U, B = L2, U2, B2
        if L2 >= U2:
            return ivs, i + 1
    return ivs, None


def in_iv(x, iv):
    L, U, B = iv
    return Fraction(L, B) <= x < Fraction(U, B)


def pullback_ok(a, b, word, ivs, x_end):
    """終点値 x_end を逆向きに引き戻して各段の区間に入るか。"""
    x = Fraction(x_end)
    n = len(word)
    if not in_iv(x, ivs[n]):
        return False
    for i in range(n - 1, -1, -1):
        x = psi(a, b, word[i], x)
        if not in_iv(x, ivs[i]):
            return False
    return True


def main():
    results = []
    all_ok = True
    for (a, b, K) in CASES:
        alph = sigma(a, b)
        stats = {"n_word_cell": 0, "n_nonempty": 0, "n_empty": 0, "exact_fail": 0, "sound_fail": 0,
                 "n_real_paths": 0, "n_lattice_full": 0, "endcell_fail": 0}
        for n in range(1, MAXLEN + 1):
            for word in itertools.product(alph, repeat=n):
                for j in range(K):
                    stats["n_word_cell"] += 1
                    ivs, empty_at = interval_run(a, b, K, j, word)
                    # (i) 正確性
                    if empty_at is None:
                        stats["n_nonempty"] += 1
                        L, U, B = ivs[n]
                        pts = [Fraction(L, B), Fraction(L + U, 2 * B), Fraction(U - 1, B)]
                        if (a, b, K) in FULL_LATTICE:
                            pts = [Fraction(t, B) for t in range(L, U)]
                            stats["n_lattice_full"] += len(pts)
                        for x in pts:
                            if not pullback_ok(a, b, word, ivs, x):
                                stats["exact_fail"] += 1
                        # 終点セルとの交叉
                        for k in range(K):
                            lo = max(Fraction(L, B), Fraction(k, K))
                            hi = min(Fraction(U, B), Fraction(k + 1, K))
                            if lo < hi:
                                for x in (lo, (lo + hi) / 2):
                                    if not (pullback_ok(a, b, word, ivs, x) and Fraction(k, K) <= x < Fraction(k + 1, K)):
                                        stats["endcell_fail"] += 1
                    else:
                        stats["n_empty"] += 1
                    # (ii) 健全性: 始点セル内の格子点から前向き
                    for t in range(DGRID):
                        x = Fraction(j * DGRID + t, K * DGRID)
                        reached = 0
                        xs = [x]
                        for i, c in enumerate(word):
                            y = (a * xs[-1] - c) / b
                            if not (0 <= y < 1):
                                break
                            xs.append(y)
                            reached = i + 1
                        if reached == n:
                            stats["n_real_paths"] += 1
                        for i in range(reached + 1):
                            if (empty_at is not None and i >= empty_at) or not in_iv(xs[i], ivs[i]):
                                stats["sound_fail"] += 1
        ok = stats["exact_fail"] == 0 and stats["sound_fail"] == 0 and stats["endcell_fail"] == 0
        all_ok &= ok
        results.append({"a": a, "b": b, "K": K, "stats": stats, "all_pass": ok})
    out = {"check": "B-10 GEO", "max_word_length": MAXLEN, "grid_denominator": DGRID, "results": results,
           "all_pass": all_ok, "status": "success",
           "summary": "; ".join("(%d,%d,K=%d): %d word/cell, %d nonempty, %d empty, real paths %d, fails exact=%d sound=%d endcell=%d"
                                % (r["a"], r["b"], r["K"], r["stats"]["n_word_cell"], r["stats"]["n_nonempty"], r["stats"]["n_empty"],
                                   r["stats"]["n_real_paths"], r["stats"]["exact_fail"], r["stats"]["sound_fail"], r["stats"]["endcell_fail"]) for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
