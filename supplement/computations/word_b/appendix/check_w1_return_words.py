#!/usr/bin/env python3
"""B-W1: 帰還語証人（研究メモ §13.1.2–13.1.3 から転記、audit-04 §3.5.1–3.5.2）。
前向き剰余列、逆向き区間、閉形式、UV≠VU、文字条件、素数冪拡大での持ち上げ位数、2ab 素数冪の単元列と CRT、複数 K の E3。"""
import json
from fractions import Fraction
from math import gcd
from obmath import modinv, crt, trial_factor, floor_frac, e1, e3, aperiodic_bits, psi, carry_alphabet

U97 = (2, -2, 2, -2, 4, -4, 2, 2, 2, 2, -4, 4, -2, 4, 4, -4, 2, 4)
V97 = (2, -2, -4, 8, -4, 4, -2, 4, -4, 4, 2, 2, 2, -4, 2, 4, 4)
MEMO_RES_U97 = [713, 202, 668, 42, 258, 128, 164, 109, 549, 604, 164, 6, 519, 667, 41, 564, 316, 713, 713]
MEMO_RES_V97 = [713, 202, 668, 654, 127, 367, 166, 111, 654, 636, 614, 279, 359, 564, 316, 713, 713, 713]
U65 = tuple(1 if ch == "+" else -1 for ch in "+++++++++++++++-+++---+++++++++--")
V65 = tuple(1 if ch == "+" else -1 for ch in "+++++++++++++++-++++++++++++--+++-+++--")

CASES = [
    {"name": "9/7", "a": 9, "b": 7, "m": 715, "q": 713, "I": (Fraction(1, 5), Fraction(3, 10)), "U": U97, "V": V97,
     "memo_res": (MEMO_RES_U97, MEMO_RES_V97), "lifts": [715 * 5, 715 * 11, 715 * 13, 715 * 55], "Ms": [30030, 4 * 9 * 49 * 715, 4290]},
    {"name": "6/5", "a": 6, "b": 5, "m": 17017, "q": 12854, "I": (Fraction(9, 10), Fraction(49, 50)), "U": U65, "V": V65,
     "memo_res": None, "lifts": [17017 * 7, 17017 * 11, 17017 * 13, 17017 * 17], "Ms": [510510, 4 * 9 * 25 * 17017]},
]
KS = [1, 2, 4, 16, 64, 2048]
N_BLOCKS = 8


def forward_res(a, b, w, q, m):
    binv = modinv(b, m)
    seq = [q]
    for c in w:
        seq.append((binv * (a * seq[-1] + c)) % m)
    return seq


def word_C(a, b, w):
    C = 0
    for j, c in enumerate(w):
        C = a * C + b ** j * c
    return C


def backward(a, b, w, x):
    vals = []
    for c in reversed(w):
        x = psi(a, b, c, x)
        vals.append(x)
    return x, vals


def order_on_fiber(a, b, w, q, mt):
    """π_w^s(q) = q (mod mt) となる最小 s>=1。途中の全剰余が単元かも返す。"""
    x = q
    s = 0
    units = True
    while True:
        seq = forward_res(a, b, w, x, mt)
        if any(gcd(v, mt) != 1 for v in seq):
            units = False
        x = seq[-1]
        s += 1
        if x == q:
            return s, units
        if s > mt:
            return None, units


def main():
    results = []
    all_ok = True
    for cs in CASES:
        a, b, m, q, U, V = cs["a"], cs["b"], cs["m"], cs["q"], cs["U"], cs["V"]
        lo, hi = cs["I"]
        ch = {}
        alph = carry_alphabet(a, b)
        ch["gcd(m,ab)=1"] = gcd(m, a * b) == 1
        ch["q unit mod m"] = gcd(q, m) == 1
        ch["letters in C(a,b)"] = all(c in alph for c in U + V)
        rU, rV = forward_res(a, b, U, q, m), forward_res(a, b, V, q, m)
        ch["forward residues all units"] = all(gcd(v, m) == 1 for v in rU + rV)
        ch["return to q"] = rU[-1] == q and rV[-1] == q
        if cs["memo_res"]:
            ch["residue lists match memo"] = rU == cs["memo_res"][0] and rV == cs["memo_res"][1]
        ch["I subset (0,1)"] = 0 < lo < hi < 1
        inter_ok = True
        img_ok = True
        closed_ok = True
        fwd_ok = True
        for w in (U, V):
            l = len(w)
            Cw = word_C(a, b, w)
            for x in (lo, hi):
                y, vals = backward(a, b, w, x)
                if not all(0 < v < 1 for v in vals):
                    inter_ok = False
                if not (lo <= y <= hi):
                    img_ok = False
                if y != (b ** l * x + Cw) / a ** l:
                    closed_ok = False
                # 前向きで戻る
                z = y
                for c in w:
                    z = (a * z - c) / b
                if z != x:
                    fwd_ok = False
        ch["backward intermediate values in (0,1)"] = inter_ok
        ch["images of I inside I"] = img_ok
        ch["closed form (b^l x + C)/a^l == iteration"] = closed_ok
        ch["forward map returns endpoints"] = fwd_ok
        ch["UV != VU"] = U + V != V + U
        # 持ち上げ位数
        lifts = []
        for mt in cs["lifts"]:
            s, us = order_on_fiber(a, b, U, q, mt)
            t, ut = order_on_fiber(a, b, V, q, mt)
            lifts.append({"m~": mt, "s": s, "t": t, "units": us and ut, "U^s V^t != V^t U^s": (U * s + V * t) != (V * t + U * s) if s and t else None})
        ch["lifts: s,t exist, units, noncommuting"] = all(l["s"] and l["t"] and l["units"] and l["U^s V^t != V^t U^s"] for l in lifts)
        # 法 M の擬軌道（M~ = lcm(M, m) で構成し M へ還元）
        pseudo = []
        for M in cs["Ms"]:
            Mt = M * m // gcd(M, m)
            fac = trial_factor(Mt)
            m_part = 1
            for p, e in fac.items():
                if m % p == 0:
                    m_part *= p ** e
            s, _ = order_on_fiber(a, b, U, q % m_part, m_part)
            t, _ = order_on_fiber(a, b, V, q % m_part, m_part)
            X0, X1 = U * s + V * t, V * t + U * s
            bits = aperiodic_bits(N_BLOCKS)
            word = []
            for eps in bits:
                word.extend(X0 if eps == 0 else X1)
            n = len(word)
            # θ: 終端を lo として逆向き
            th = [None] * (n + 1)
            th[n] = lo
            for i in range(n - 1, -1, -1):
                th[i] = psi(a, b, word[i], th[i + 1])
            pc = {}
            pc["theta in (0,1)"] = all(0 < v < 1 for v in th)
            pc["identity"] = all(a * th[i] - b * th[i + 1] == word[i] for i in range(n))
            # m 部分: 前向き
            comps = [(forward_res(a, b, word, q % m_part, m_part), m_part)] if m_part > 1 else []
            # 2ab の素数冪
            for p, e in sorted(fac.items()):
                if m % p == 0:
                    continue
                pe = p ** e
                if a % p == 0:
                    qq = [1]
                    binv = modinv(b, pe)
                    for i in range(n):
                        qq.append((binv * (a * qq[i] + word[i])) % pe)
                elif b % p == 0:
                    ainv = modinv(a, pe)
                    ext = word + list(U) * 3
                    qq = [(-sum(b ** j * pow(ainv, j + 1, pe) * ext[i + j] for j in range(e))) % pe for i in range(n + 1)]
                elif p == 2:
                    qq = [1]
                    binv = modinv(b, pe)
                    for i in range(n):
                        qq.append((binv * (a * qq[i] + word[i])) % pe)
                else:
                    raise ValueError
                comps.append((qq, pe))
            qM = [crt([(cq[i], pe) for cq, pe in comps]) for i in range(n + 1)]
            pc["recurrence mod M~"] = all((b * qM[i + 1] - a * qM[i] - word[i]) % Mt == 0 for i in range(n))
            pc["units mod M~"] = all(gcd(v, Mt) == 1 for v in qM)
            qr = [v % M for v in qM]
            pc["recurrence mod M, units mod M"] = all((b * qr[i + 1] - a * qr[i] - word[i]) % M == 0 for i in range(n)) and all(gcd(v, M) == 1 for v in qr)
            eok = True
            for K in KS:
                cells = [floor_frac(K * v) for v in th]
                for i in range(n):
                    if not (e1(a, b, word[i]) and e3(a, b, K, cells[i], cells[i + 1], word[i])):
                        eok = False
            pc["E1,E3 for K in %s" % KS] = eok
            pseudo.append({"M": M, "M~": Mt, "m_part": m_part, "s": s, "t": t, "word_length": n, "checks": pc, "all_pass": all(pc.values())})
        ch["pseudo-orbits for all M"] = all(x["all_pass"] for x in pseudo)
        ok = all(ch.values())
        all_ok &= ok
        results.append({"case": cs["name"], "|U|": len(U), "|V|": len(V), "residues_U": rU, "residues_V": rV, "C(U)": word_C(a, b, U), "C(V)": word_C(a, b, V),
                        "checks": ch, "lifts": lifts, "pseudo_orbits": pseudo, "all_pass": ok})
    out = {"check": "B-W1 return-word witnesses", "results": results, "all_pass": all_ok, "status": "success",
           "summary": "; ".join("%s: |U|=%d |V|=%d pass=%s lifts=%s" % (r["case"], r["|U|"], r["|V|"], r["all_pass"], [(l["m~"], l["s"], l["t"]) for l in r["lifts"]]) for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
