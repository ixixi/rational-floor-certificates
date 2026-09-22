#!/usr/bin/env python3
"""B-3: UV≠VU と有限接頭語の厳密 θ 列（audit-03 §3.9.3–3.9.4, §5 B-3）。"""
import json
from fractions import Fraction
from obmath import (obr_witness, interval_certificate, aperiodic_bits, psi, has_period,
                    x_fixed, phi_iter)

WITNESSES = [(101, 2, 15, 1), (101, 100, 21, 1), (5, 2, 1, 1), (7, 5, 1, 2), (7, 5, 3, 1), (9, 7, 1, 2), (6, 5, 1, 1)]
N_BLOCKS = 48


def encode(bits, U, V):
    word = []
    for eps in bits:
        word.extend(U + V if eps == 0 else V + U)
    return word


def backward_thetas(a, b, word, theta_end):
    """word[0..n-1] を前向き時刻順の文字列とし、θ_n = theta_end から逆向きに θ_0..θ_n を返す。"""
    n = len(word)
    th = [None] * (n + 1)
    th[n] = Fraction(theta_end)
    for i in range(n - 1, -1, -1):
        th[i] = psi(a, b, word[i], th[i + 1])
    return th


def block_map_interval(a, b, c, d, L, blocks, lo, hi):
    """ブロック列 blocks（各 'U' or 'V'）を終端側から合成して区間 [lo,hi] の像を返す。"""
    for blk in reversed(blocks):
        LL = L if blk == "U" else L + 1
        lo = phi_iter(a, b, c, d, LL, lo)[0]
        hi = phi_iter(a, b, c, d, LL, hi)[0]
    return lo, hi


def main():
    results = []
    all_ok = True
    bits = aperiodic_bits(N_BLOCKS)
    for (a, b, R, m) in WITNESSES:
        w = obr_witness(a, b, R, m)
        cert = interval_certificate(a, b, w["h"], w["c"], full=False)
        L, c, d = cert["L"], w["c"], w["d"]
        U, V = cert["U"], cert["V"]
        xL, xL1 = x_fixed(a, b, w["h"], L), x_fixed(a, b, w["h"], L + 1)
        ch = {}
        UV, VU = U + V, V + U
        ch["|UV|=|VU|=2L+3"] = len(UV) == len(VU) == 2 * L + 3
        ch["UV!=VU"] = UV != VU
        diff = [i for i in range(len(UV)) if UV[i] != VU[i]]
        # UV = d^L c d^{L+1} c, VU = d^{L+1} c d^L c: 位置 L で (c,d)、位置 L+1 で (d,c) が異なる
        ch["differ at position L (UV[L]=c, VU[L]=d)"] = UV[L] == c and VU[L] == d
        ch["differing positions = {L, L+1}"] = diff == [L, L + 1]
        word = encode(bits, U, V)
        n = len(word)
        ch["word letters in {c,d}"] = set(word) <= {c, d}
        # 三つの終端値
        ends = {"left": xL, "right": xL1, "mid": (xL + xL1) / 2}
        theta_ok = True
        ident_ok = True
        start_in_I = True
        for name, te in ends.items():
            th = backward_thetas(a, b, word, te)
            if not all(0 < t < 1 for t in th):
                theta_ok = False
            if not all(a * th[i] - b * th[i + 1] == word[i] for i in range(n)):
                ident_ok = False
            if not (xL <= th[0] <= xL1):
                start_in_I = False
            # ブロック境界の値も I 内
            pos = 0
            for eps in bits:
                for blk in ("U", "V") if eps == 0 else ("V", "U"):
                    if not (xL <= th[pos] <= xL1):
                        start_in_I = False
                    pos += len(U) if blk == "U" else len(V)
        ch["0<theta_n<1 all times, 3 terminal choices"] = theta_ok
        ch["a*theta_n - b*theta_{n+1} = c_n exact"] = ident_ok
        ch["block-boundary values in I"] = start_in_I
        # 入れ子区間: I_1^{(k)} の単調減少と長さ上界
        blocks = []
        for eps in bits[:12]:
            blocks.extend(["U", "V"] if eps == 0 else ["V", "U"])
        nested_ok = True
        prev = (xL, xL1)
        width = xL1 - xL
        r = Fraction(b, a)
        for k in range(1, len(blocks) + 1):
            lo, hi = block_map_interval(a, b, c, d, L, blocks[:k], xL, xL1)
            if not (prev[0] <= lo <= hi <= prev[1]):
                nested_ok = False
            if not (hi - lo <= r ** ((L + 1) * k) * width):
                nested_ok = False
            prev = (lo, hi)
        ch["nested block images shrink"] = nested_ok
        # 有限観察: 窓内で周期 P <= 2L+3 の周期性なし
        ch["no period P<=2L+3 in finite window (observation)"] = not any(has_period(word, P) for P in range(1, 2 * L + 4))
        ok = all(ch.values())
        if not ok:
            all_ok = False
        results.append({"witness": [a, b, R, m], "L": L, "U": U, "V": V, "n_blocks": N_BLOCKS,
                        "word_length": n, "checks": ch, "all_pass": ok})
    out = {"check": "B-3 aperiodic coding", "bits_prefix": bits, "results": results,
           "all_pass": all_ok, "status": "success",
           "summary": "; ".join("%s: L=%d len=%d pass=%s" % (r["witness"], r["L"], r["word_length"], r["all_pass"]) for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
