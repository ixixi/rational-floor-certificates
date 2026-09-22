#!/usr/bin/env python3
"""B-5: Jacobsthal 関数（定義どおりの全窓走査 vs 最大間隔、J<=3^k、包含排除下界、2^k k! <= N）。"""
import json
import re
import sys
from fractions import Fraction
from math import factorial
from obmath import primes_upto, unit_mask, phi

N_MAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
N_SCAN = 3000  # J を 1 から増やす文字どおりの走査を行う範囲（それ以上は最小性の二条件検査）


def spf_sieve(n):
    spf = list(range(n + 1))
    for i in range(2, int(n ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def factor_spf(n, spf):
    f = {}
    while n > 1:
        p = spf[n]
        f[p] = f.get(p, 0) + 1
        n //= p
    return f


def all_windows_have_unit(mask_bytes, N, J):
    """開始点 s in [0,N) の長さ J の全窓に単元があるか。mask は [0,2N)。"""
    if J > N:
        return True  # 長さ N の窓は完全剰余系を含み、N>=1 なら単元 (例えば 1) を含む
    i = mask_bytes.find(b"\x00" * J)
    return i == -1 or i >= N


def j_def_scan(mask_bytes, N):
    J = 1
    while not all_windows_have_unit(mask_bytes, N, J):
        J += 1
    return J


def j_gap(mask_bytes, N):
    """単元の最大間隔 = 1 + 最長の非単元連（開始点 < N のもの）。"""
    best = 0
    for mo in re.finditer(rb"\x00+", mask_bytes):
        if mo.start() < N:
            best = max(best, mo.end() - mo.start())
    return best + 1


def j_gap_units(mask_bytes, N):
    """単元リストの隣接差（巡回差を含む）による直接計算（小さい N で照合）。"""
    us = [i for i in range(N) if mask_bytes[i]]
    g = 0
    for i in range(len(us) - 1):
        g = max(g, us[i + 1] - us[i])
    return max(g, us[0] + N - us[-1])


def main():
    spf = spf_sieve(N_MAX)
    stats = {"n_N": 0, "n_scan": 0, "max_J": 0, "max_k": 0, "fail": []}
    per_k_maxJ = {}
    J_of = {}
    for N in range(3, N_MAX + 1, 2):
        f = factor_spf(N, spf)
        if any(e > 1 for e in f.values()):
            continue
        primes = sorted(f)
        k = len(primes)
        mask = bytes(unit_mask(N, primes))
        g = j_gap(mask, N)
        # 定義の最小性: 長さ g の全窓に単元があり、長さ g-1 のある窓に単元がない
        ok_min = all_windows_have_unit(mask, N, g) and (g == 1 or not all_windows_have_unit(mask, N, g - 1))
        if N <= N_SCAN:
            Jd = j_def_scan(mask, N)
            gu = j_gap_units(mask, N)
            ok_scan = (Jd == g == gu)
            stats["n_scan"] += 1
        else:
            ok_scan = True
        J = g
        J_of[N] = J
        # J <= 3^k
        ok_3k = J <= 3 ** k
        # 包含排除下界: 長さ 3^k の全窓の単元数 >= 3^k φ(N)/N - (2^k-1)
        H = 3 ** k
        reps = (H // N) + 2
        m = mask[:N] * reps
        pre = [0]
        for v in m:
            pre.append(pre[-1] + v)
        min_count = min(pre[s + H] - pre[s] for s in range(N))
        bound = Fraction(H * phi(N), N) - (2 ** k - 1)
        ok_ie = Fraction(min_count) >= bound
        ok_prod = N >= 2 ** k * factorial(k)
        ok = ok_min and ok_scan and ok_3k and ok_ie and ok_prod
        stats["n_N"] += 1
        stats["max_J"] = max(stats["max_J"], J)
        stats["max_k"] = max(stats["max_k"], k)
        per_k_maxJ[k] = max(per_k_maxJ.get(k, 0), J)
        if not ok:
            stats["fail"].append({"N": N, "J": J, "k": k, "min": ok_min, "scan": ok_scan, "3k": ok_3k, "ie": ok_ie, "prod": ok_prod})
    # i 番目の奇素数 >= 2i+1
    ps = [p for p in primes_upto(2000) if p > 2]
    ok_odd = all(ps[i - 1] >= 2 * i + 1 for i in range(1, 201))
    # J(p)=2, J(pq)=3 の集計
    Jp = [J_of[p] for p in ps if p <= N_MAX]
    ok_Jp = all(v == 2 for v in Jp)
    Jpq = []
    for i in range(len(ps)):
        for j in range(i + 1, len(ps)):
            if ps[i] * ps[j] <= N_MAX:
                Jpq.append(J_of[ps[i] * ps[j]])
    ok_Jpq = all(v == 3 for v in Jpq)
    all_ok = not stats["fail"] and ok_odd and ok_Jp and ok_Jpq
    out = {
        "check": "B-5 Jacobsthal", "N_max": N_MAX, "N_scan_literal": N_SCAN,
        "n_odd_squarefree_N": stats["n_N"], "n_literal_scan": stats["n_scan"],
        "max_J": stats["max_J"], "max_k": stats["max_k"], "max_J_per_k": per_k_maxJ,
        "failures": stats["fail"],
        "odd_prime_index_bound_i<=200": ok_odd,
        "J(p)=2 count": len(Jp), "J(p)=2 all": ok_Jp,
        "J(pq)=3 count": len(Jpq), "J(pq)=3 all": ok_Jpq,
        "all_pass": all_ok, "status": "success",
        "summary": "%d odd squarefree N<=%d: J_def=J_gap, J<=3^k, inclusion-exclusion bound, N>=2^k k! all hold=%s; J(p)=2 (%d), J(pq)=3 (%d); max J=%d"
                   % (stats["n_N"], N_MAX, not stats["fail"], len(Jp), len(Jpq), stats["max_J"]),
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
