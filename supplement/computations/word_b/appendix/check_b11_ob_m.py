#!/usr/bin/env python3
"""B-11: OB-M の左向き構成（audit-03 §3.7.1–3.7.3）と REAL-FIN（§3.8）による真軌道実現。"""
import json
from fractions import Fraction
from math import gcd
from obmath import (rad, trial_factor, modinv, crt, aperiodic_bits, floor_frac, frac_part, e1, e3, has_period)

CASES = [(7, 5, 9), (7, 5, 3), (8, 3, 4), (13, 4, 18), (12, 5, 27), (11, 3, 25), (18, 5, 8), (17, 10, 12), (9, 2, 8), (7, 5, 25)]
N_STEPS = 40
KS = [1, 2, 4, 5, 16, 64]
T0 = 10 ** 6


def ceil_frac(x):
    x = Fraction(x)
    return -((-x.numerator) // x.denominator)


def left_construction(a, b, R, n_total, bits):
    """θ_0=0 から左向きに n_total 段。返り値: carries[n] (n=-1..-n_total), thetas[n] (n=0..-n_total), 候補数。"""
    thetas = {0: Fraction(0)}
    carries = {}
    ncand = {}
    for step in range(1, n_total + 1):
        n = -step
        th1 = thetas[n + 1]
        lo = ceil_frac(-b * th1)             # c >= -b θ_{n+1}
        hi = ceil_frac(a - b * th1) - 1      # c < a - b θ_{n+1}
        cands = [c for c in range(lo, hi + 1) if (c - (b - a)) % R == 0]
        ncand[n] = len(cands)
        if len(cands) < 2:
            raise RuntimeError("fewer than two candidates at n=%d" % n)
        c = cands[bits[step - 1]]
        carries[n] = c
        thetas[n] = (b * th1 + c) / a
    return carries, thetas, ncand


def main():
    results = []
    all_ok = True
    for (a, b, M) in CASES:
        R = rad(M)
        rec = {"a": a, "b": b, "M": M, "rad": R, "hypothesis a>=2rad(M)": a >= 2 * R}
        if not rec["hypothesis a>=2rad(M)"]:
            rec["note"] = "hypothesis violated; construction not attempted (expected rejection)"
            rec["all_pass"] = True
            results.append(rec)
            continue
        fac = trial_factor(M)
        # p|a の望遠和に必要な L の最大値
        Lmax = 0
        for p, k in fac.items():
            if a % p == 0:
                L = 1
                while (a ** L) % (p ** k) != 0:
                    L += 1
                Lmax = max(Lmax, L)
        n_total = N_STEPS + Lmax
        bits = aperiodic_bits(n_total)
        carries, thetas, ncand = left_construction(a, b, R, n_total, bits)
        ch = {}
        ch["candidates>=2 each step"] = all(v >= 2 for v in ncand.values())
        ch["candidates>=floor(a/R)"] = all(v >= a // R for v in ncand.values())
        ch["theta in [0,1)"] = all(0 <= thetas[n] < 1 for n in thetas)
        ch["1-b<=c<=a-1"] = all(1 - b <= carries[n] <= a - 1 for n in carries)
        ch["c=b-a mod R"] = all((carries[n] - (b - a)) % R == 0 for n in carries)
        ch["a theta_n - b theta_{n+1} = c_n"] = all(a * thetas[n] - b * thetas[n + 1] == carries[n] for n in carries)
        # 素数冪剰余（窓は n = -N_STEPS .. 0）
        comps = []
        per = {}
        for p, k in sorted(fac.items()):
            pk = p ** k
            q = {}
            if a % p != 0:
                case = "p∤a (backward)"
                q[0] = 1
                ainv = modinv(a, pk)
                for n in range(-1, -N_STEPS - 1, -1):
                    q[n] = (ainv * (b * q[n + 1] - carries[n])) % pk
            else:
                case = "p|a (telescoping sum)"
                L = 1
                while (a ** L) % pk != 0:
                    L += 1
                binv = modinv(b, pk)
                for n in range(0, -N_STEPS - 1, -1):
                    s = 0
                    for j in range(L):
                        s += (a ** j) * pow(binv, j + 1, pk) * carries[n - 1 - j]
                    q[n] = s % pk
            pc = {"case": case}
            pc["recurrence mod p^k"] = all((b * q[n + 1] - a * q[n] - carries[n]) % pk == 0 for n in range(-1, -N_STEPS - 1, -1))
            pc["q_n = 1 mod p"] = all(q[n] % p == 1 for n in q)
            per["%d^%d" % (p, k)] = pc
            comps.append((q, pk))
        ch["per prime power"] = all(v["recurrence mod p^k"] and v["q_n = 1 mod p"] for v in per.values())
        qM = {n: crt([(cq[n], pk) for cq, pk in comps]) for n in range(0, -N_STEPS - 1, -1)}
        ch["CRT recurrence mod M"] = all((b * qM[n + 1] - a * qM[n] - carries[n]) % M == 0 for n in range(-1, -N_STEPS - 1, -1))
        ch["gcd(q_n,M)=1"] = all(gcd(qM[n], M) == 1 for n in qM)
        # E1–E3 for several K
        eok = True
        for K in KS:
            for n in range(-1, -N_STEPS - 1, -1):
                j, k_ = floor_frac(K * thetas[n]), floor_frac(K * thetas[n + 1])
                e_ = carries[n]
                if not (0 <= j < K and 0 <= k_ < K and e1(a, b, e_) and (b * qM[n + 1] - a * qM[n] - e_) % M == 0 and e3(a, b, K, j, k_, e_)):
                    eok = False
        ch["E1-E3 for K in %s" % KS] = eok
        # REAL-FIN: i = n + N_STEPS, i = 0..N
        N = N_STEPS
        qi = [qM[i - N] for i in range(N + 1)]
        thi = [thetas[i - N] for i in range(N + 1)]
        ci = [carries[i - N] for i in range(N)]
        di = []
        dint = True
        for i in range(N):
            num = a * qi[i] + ci[i] - b * qi[i + 1]
            if num % M != 0:
                dint = False
            di.append(num // M)
        ch["d_i integer"] = dint
        S = [0]
        for j in range(N):
            S.append(a * S[j] + (b ** j) * di[j])
        bN = b ** N
        t0 = (-pow(a, -N, bN) * S[N]) % bN if bN > 1 else 0
        # T を足して全 Q_i > T0
        T = 0
        for j in range(N + 1):
            tj = (a ** j * t0 + S[j])
            assert tj % (b ** j) == 0
            tj //= b ** j
            Qj = qi[j] + M * tj
            need = (T0 - Qj) // (M * a ** j * b ** (N - j)) + 1
            T = max(T, need)
        t0 += bN * T
        tj = []
        tint = True
        for j in range(N + 1):
            num = a ** j * t0 + S[j]
            if num % (b ** j) != 0:
                tint = False
            tj.append(num // (b ** j))
        ch["t_j integer"] = tint
        ch["b t_{j+1} = a t_j + d_j"] = all(b * tj[j + 1] == a * tj[j] + di[j] for j in range(N))
        Q = [qi[j] + M * tj[j] for j in range(N + 1)]
        ch["Q_i > T0"] = all(Qj > T0 for Qj in Q)
        ch["Q_i = q_i mod M"] = all(Q[j] % M == qi[j] for j in range(N + 1))
        ch["b Q_{i+1} = a Q_i + c_i"] = all(b * Q[j + 1] == a * Q[j] + ci[j] for j in range(N))
        xi = Q[0] + thi[0]
        r = Fraction(a, b)
        xs = [xi * r ** i for i in range(N + 1)]
        ch["floor(xi r^i) = Q_i"] = all(floor_frac(xs[i]) == Q[i] for i in range(N + 1))
        ch["frac(xi r^i) = theta_i"] = all(frac_part(xs[i]) == thi[i] for i in range(N + 1))
        ch["no period P<=20 in window (observation)"] = not any(has_period(ci, P) for P in range(1, 21))
        ok = all(v for v in ch.values())
        all_ok &= ok
        rec.update({"n_steps": N_STEPS, "Lmax": Lmax, "carries_window": ci, "per_prime_power": per, "checks": ch,
                    "xi": str(xi), "Q_0": Q[0], "all_pass": ok})
        results.append(rec)
    out = {"check": "B-11 OB-M left construction + REAL-FIN", "results": results, "all_pass": all_ok, "status": "success",
           "summary": "; ".join("(%d,%d,M=%d) %s" % (r["a"], r["b"], r["M"], "hyp-violated" if not r["hypothesis a>=2rad(M)"] else "pass=%s" % r["all_pass"]) for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
