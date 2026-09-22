#!/usr/bin/env python3
"""B-4: 法 M の単元剰余（audit-03 §3.9.5 の四場合、CRT、複数 K で E1–E3）。"""
import json
from fractions import Fraction
from math import gcd
from obmath import (obr_witness, interval_certificate, aperiodic_bits, x_fixed, modinv, crt,
                    trial_factor, floor_frac, e3, e1)
from check_b03_coding import encode, backward_thetas

CASES = {
    (101, 2, 15, 1): [2 * 3 * 5 * 101, 2 ** 3 * 3 ** 2 * 5 * 101 ** 2, 2 ** 2 * 3 ** 3 * 5 ** 2 * 101],
    (101, 100, 21, 1): [2 * 3 * 5 * 7 * 101, 2 ** 3 * 3 ** 2 * 5 ** 2 * 7 * 101, 2 ** 2 * 3 * 5 ** 3 * 7 ** 2 * 101 ** 2],
    (5, 2, 1, 1): [10, 2 ** 3 * 5 ** 2, 2 ** 2 * 5 ** 3],
    (7, 5, 3, 1): [210, 2 ** 2 * 3 ** 2 * 5 ** 3 * 7, 2 ** 3 * 3 * 5 * 7 ** 2],
    (7, 5, 1, 2): [70, 2 ** 3 * 5 ** 2 * 7 ** 2],
}
KS = [1, 2, 3, 4, 7, 16, 64, 2048]
N_BLOCKS = 24
EXTRA_U_BLOCKS = 4  # 未来 e 文字の余裕


def residues_prime_power(a, b, R, p, e, word, n_win):
    """時刻 0..n_win の q_n (mod p^e) と場合名。word は n_win+余裕 文字。"""
    pe = p ** e
    if a % p == 0:
        case = "p|a"
        q = [1]
        binv = modinv(b, pe)
        for n in range(n_win):
            q.append((binv * (a * q[n] + word[n])) % pe)
    elif b % p == 0:
        case = "p|b"
        ainv = modinv(a, pe)
        q = []
        for n in range(n_win + 1):
            s = 0
            for j in range(e):
                s += (b ** j) * pow(ainv, j + 1, pe) * word[n + j]
            q.append((-s) % pe)
    elif R % p == 0:
        case = "p|R"
        q = [(-1) % pe]
        binv = modinv(b, pe)
        for n in range(n_win):
            q.append((binv * (a * q[n] + word[n])) % pe)
    elif p == 2:
        case = "p=2, a,b odd"
        q = [1]
        binv = modinv(b, pe)
        for n in range(n_win):
            q.append((binv * (a * q[n] + word[n])) % pe)
    else:
        raise ValueError("prime %d does not divide 2abR" % p)
    return case, q


def main():
    results = []
    all_ok = True
    bits = aperiodic_bits(N_BLOCKS)
    for (a, b, R, m), Ms in CASES.items():
        w = obr_witness(a, b, R, m)
        cert = interval_certificate(a, b, w["h"], w["c"], full=False)
        L, c, d = cert["L"], w["c"], w["d"]
        U, V = cert["U"], cert["V"]
        xL = x_fixed(a, b, w["h"], L)
        word = encode(bits, U, V) + U * EXTRA_U_BLOCKS
        n_win = len(word) - len(U) * EXTRA_U_BLOCKS  # 検査する時刻 0..n_win
        th = backward_thetas(a, b, word, xL)  # θ_0..θ_len(word)
        for M in Ms:
            fac = trial_factor(M)
            ch = {}
            per_prime = {}
            comps = []
            for p, e in sorted(fac.items()):
                pe = p ** e
                case, q = residues_prime_power(a, b, R, p, e, word, n_win)
                pc = {}
                pc["recurrence mod p^e"] = all((b * q[n + 1] - a * q[n] - word[n]) % pe == 0 for n in range(n_win))
                pc["units mod p"] = all(q[n] % p != 0 for n in range(n_win + 1))
                if case == "p|R":
                    pc["q_n = -1 mod p"] = all((q[n] + 1) % p == 0 for n in range(n_win + 1))
                if case == "p|b":
                    # 逆向き反復との一致: q_{n_win} から a^{-1}(b q_{n+1} - c_n) で戻す
                    ainv = modinv(a, pe)
                    qb = [None] * (n_win + 1)
                    qb[n_win] = q[n_win]
                    for n in range(n_win - 1, -1, -1):
                        qb[n] = (ainv * (b * qb[n + 1] - word[n])) % pe
                    pc["direct formula = backward iteration"] = qb == q
                    pc["q_n = -a^{-1} c_n mod p"] = all((q[n] + modinv(a, p) * word[n]) % p == 0 for n in range(n_win + 1))
                if case == "p|a":
                    pc["q_{n+1} = b^{-1} c_n mod p"] = all((q[n + 1] - modinv(b, p) * word[n]) % p == 0 for n in range(n_win))
                if case == "p=2, a,b odd":
                    pc["c_n even"] = all(word[n] % 2 == 0 for n in range(n_win))
                per_prime["%d^%d" % (p, e)] = {"case": case, "checks": pc}
                comps.append((q, pe))
            # CRT
            qM = [crt([(comps[i][0][n], comps[i][1]) for i in range(len(comps))]) for n in range(n_win + 1)]
            ch["per-prime-power all pass"] = all(all(v["checks"].values()) for v in per_prime.values())
            ch["CRT: recurrence mod M"] = all((b * qM[n + 1] - a * qM[n] - word[n]) % M == 0 for n in range(n_win))
            ch["CRT: gcd(q_n,M)=1"] = all(gcd(qM[n], M) == 1 for n in range(n_win + 1))
            ch["CRT: reduces to components"] = all(qM[n] % comps[i][1] == comps[i][0][n] for n in range(n_win + 1) for i in range(len(comps)))
            # 複数 K で E1–E3
            eok = True
            for K in KS:
                cells = [floor_frac(K * th[n]) for n in range(n_win + 1)]
                if not all(0 <= cells[n] < K for n in range(n_win + 1)):
                    eok = False
                for n in range(n_win):
                    e_ = word[n]
                    if not (e1(a, b, e_) and (b * qM[n + 1] - a * qM[n] - e_) % M == 0 and e3(a, b, K, cells[n], cells[n + 1], e_)):
                        eok = False
            ch["E1,E2,E3 for K in %s" % KS] = eok
            ok = all(ch.values())
            if not ok:
                all_ok = False
            results.append({"witness": [a, b, R, m], "M": M, "factorization": {str(p): e for p, e in sorted(fac.items())},
                            "L": L, "window_length": n_win, "per_prime_power": per_prime, "checks": ch,
                            "q_first_8": qM[:8], "all_pass": ok})
    out = {"check": "B-4 unit residues mod M", "K_list": KS, "results": results, "all_pass": all_ok, "status": "success",
           "summary": "; ".join("%s M=%d pass=%s" % (r["witness"], r["M"], r["all_pass"]) for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
