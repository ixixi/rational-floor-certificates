#!/usr/bin/env python3
"""B-R3: 9/7、ξ=11 の真の床軌道での REC-FIN 証明書（audit-04 §3.1.6）。"""
import json
from fractions import Fraction
from obmath import floor_frac, modinv, trial_factor

a, b, P = 9, 7, 11


def main():
    xi = Fraction(P)
    r = Fraction(a, b)
    Q = [floor_frac(xi * r ** n) for n in range(60)]
    c = [b * Q[n + 1] - a * Q[n] for n in range(59)]
    ch = {}
    ch["Q_0 = 11"] = Q[0] == 11
    ch["true orbit differs from T_1 orbit at n=1 (floor(99/7)=14, T_1(11)=15)"] = Q[1] == 14 and (11 + 2 * ((11 + 4) // 7)) == 15
    ch["c_0 = c_43 = -1"] = c[0] == c[43] == -1
    ch["COPY with t=(1,43), L=0"] = c[43:44] == c[0:1]
    # 置換 f_c(x) = b^{-1}(a x + c) mod 11, G_n(0)
    binv = modinv(b, P)
    G = [0]
    for n in range(59):
        G.append((binv * (a * G[n] + c[n])) % P)
    ch["G_n(0) = Q_n mod 11 for all n<=59"] = all(G[n] == Q[n] % P for n in range(60))
    ch["return at n=44: G_44(0)=0"] = G[44] == 0
    ch["11 | Q_44"] = Q[44] % P == 0
    ch["Q_44 = 697829 = 11*63439"] = Q[44] == 697829 == 11 * 63439
    f = trial_factor(Q[44])
    ch["Q_44 composite"] = len(f) > 1 or list(f.values()) != [1]
    # H_1 = G_1, H_2 = G_1 ∘ G_43 ; H_1(0)=G_1(0), H_2(0)=G_44(0) - 鳩ノ巣 i=0,j=2 → n = t_1+t_2 = 44
    ch["pigeonhole: H_0(0)=H_2(0)=0"] = G[0] == 0 and G[44] == 0
    ch["gcd(11, ab)=1"] = 11 % 3 != 0 and 11 % 7 != 0
    first_return = next(n for n in range(1, 60) if G[n] == 0)
    all_ok = all(ch.values())
    out = {"check": "B-R3 REC-FIN certificate example (9/7, xi=11)", "Q_first_12": Q[:12], "c_first_12": c[:12], "Q_44": Q[44],
           "factorization_Q44": {str(k): v for k, v in f.items()}, "first_n>=1_with_11|Q_n": first_return, "checks": ch,
           "all_pass": all_ok, "status": "success",
           "summary": "true orbit floor(11(9/7)^n): c_0=c_43=-1, G_44(0)=0, Q_44=%d=11*%d; all=%s" % (Q[44], Q[44] // 11, all_ok)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
