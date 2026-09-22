#!/usr/bin/env python3
"""B-9: CUT-T（audit-03 §3.13）。閉形式と一文字反復の両方で「同一非零平行移動」を判定し、
p|D ∧ p∤C_1 との同値を両方向で検査。§8.5.2 の名指し例と p ブロック以内に 0 を通ること。"""
import itertools
import json
from math import gcd
from obmath import sigma, carry_alphabet, modinv, primes_upto, obr_witness, interval_certificate

PRIMES = primes_upto(43)


def word_C(a, b, w):
    C = 0
    for j, c in enumerate(w):
        C = a * C + (b ** j) * c
    return C


def cut_data(a, b, W):
    ells = [len(w) for w in W]
    Cs = [word_C(a, b, w) for w in W]
    g = 0
    for l in ells:
        g = gcd(g, l)
    D = a ** g - b ** g
    for i in range(1, len(W)):
        D = gcd(D, abs(Cs[i] * b ** ells[0] - Cs[0] * b ** ells[i]))
    return g, Cs, D


def closed_map(a, b, w, p):
    """(傾き, 平行移動) mod p。"""
    l = len(w)
    binv = modinv(b, p)
    return (pow(a, l, p) * pow(binv, l, p)) % p, (word_C(a, b, w) * pow(binv, l, p)) % p


def iter_table(a, b, w, p):
    binv = modinv(b, p)
    tab = []
    for q in range(p):
        x = q
        for c in w:
            x = (binv * (a * x + c)) % p
        tab.append(x)
    return tab


def same_nonzero_translation_closed(maps):
    slopes = {s for s, _ in maps}
    taus = {t for _, t in maps}
    return slopes == {1} and len(taus) == 1 and next(iter(taus)) != 0


def same_nonzero_translation_iter(tables, p):
    taus = set()
    for tab in tables:
        ts = {(tab[q] - q) % p for q in range(p)}
        if len(ts) != 1:
            return False
        taus |= ts
    return len(taus) == 1 and next(iter(taus)) != 0


def check_family(a, b, words, sizes, counter, fails, limit_words=None):
    """words: 語のリスト。sizes: 語集合の大きさ。閉形式・反復・判定式の同値を全語集合×全素数で検査。"""
    ps = [p for p in PRIMES if (a * b) % p != 0]
    pre = {}
    for p in ps:
        for w in words:
            pre[(p, w)] = (closed_map(a, b, w, p), iter_table(a, b, w, p))
            # 閉形式と反復の点ごとの一致
            s, t = pre[(p, w)][0]
            tab = pre[(p, w)][1]
            if any(tab[q] != (s * q + t) % p for q in range(p)):
                fails.append({"a": a, "b": b, "p": p, "w": w, "type": "closed != iter pointwise"})
    for size in sizes:
        for W in itertools.combinations(words, size):
            g, Cs, D = cut_data(a, b, W)
            for p in ps:
                crit = (D % p == 0) and (Cs[0] % p != 0)
                closed = same_nonzero_translation_closed([pre[(p, w)][0] for w in W])
                it = same_nonzero_translation_iter([pre[(p, w)][1] for w in W], p)
                counter[0] += 1
                if closed:
                    counter[1] += 1
                if not (closed == crit == it):
                    fails.append({"a": a, "b": b, "p": p, "W": W, "D": D, "C1": Cs[0], "closed": closed, "iter": it, "crit": crit})


def zero_within_p_blocks(a, b, U, V, p):
    """全 q と 4 種のブロック列で、p 個の境界剰余（開始を含む）の中に 0 があるか。"""
    binv = modinv(b, p)

    def apply(w, q):
        for c in w:
            q = (binv * (a * q + c)) % p
        return q
    seqs = {"U^p": [U] * p, "V^p": [V] * p, "(UV)^p": [U, V] * p, "(VU)^p": [V, U] * p}
    ok = True
    for name, blocks in seqs.items():
        for q0 in range(p):
            q = q0
            hit = (q == 0)
            for blk in blocks[:p - 1]:
                q = apply(blk, q)
                if q == 0:
                    hit = True
            if not hit:
                ok = False
    return ok


def main():
    fails = []
    counter = [0, 0]  # (検査した (W,p) の数, 条件が真だった数)
    families = []
    # (1) a<=5: 全 Σ、長さ 1–2、2 語集合
    for a in range(3, 6):
        for b in range(2, a):
            if gcd(a, b) != 1:
                continue
            alph = sigma(a, b)
            words = [(c,) for c in alph] + [(c1, c2) for c1 in alph for c2 in alph]
            check_family(a, b, words, [2], counter, fails)
            families.append({"a": a, "b": b, "alphabet": "Sigma", "n_words": len(words), "sizes": [2]})
    # (2) 6<=a<=13: 𝒞(a,b)、長さ<=3、各長さ辞書順先頭 12 語、2 語集合
    for a in range(6, 14):
        for b in range(2, a):
            if gcd(a, b) != 1:
                continue
            alph = carry_alphabet(a, b)
            words = []
            for l in (1, 2, 3):
                ws = sorted(itertools.product(alph, repeat=l))[:12]
                words.extend(ws)
            check_family(a, b, words, [2], counter, fails)
            families.append({"a": a, "b": b, "alphabet": "C(a,b)", "n_words": len(words), "sizes": [2]})
    # (3) 3 語集合: (3,2),(4,3),(5,2)、長さ<=2、辞書順先頭 20 語
    for (a, b) in [(3, 2), (4, 3), (5, 2)]:
        alph = sigma(a, b)
        words = sorted([(c,) for c in alph] + [(c1, c2) for c1 in alph for c2 in alph])[:20]
        check_family(a, b, words, [3], counter, fails)
        families.append({"a": a, "b": b, "alphabet": "Sigma", "n_words": len(words), "sizes": [3]})
    # (4) 名指し例
    named = {}
    g, Cs, D = cut_data(101, 2, [(69,), (99, 69)])
    named["101/2"] = {"g": g, "C": Cs, "D": D,
                      "p=3 excluded (3|C1)": (D % 3 == 0) and (Cs[0] % 3 == 0),
                      "p=5 excluded (5∤D)": D % 5 != 0,
                      "p=11 criterion": (D % 11 == 0) and (Cs[0] % 11 != 0),
                      "p=11 tau": closed_map(101, 2, (69,), 11)[1],
                      "p=11 V map": closed_map(101, 2, (99, 69), 11),
                      "p=11 zero within p blocks": zero_within_p_blocks(101, 2, (69,), (99, 69), 11)}
    named["101/2"]["ok"] = (D == 99 and Cs[0] == 69 and named["101/2"]["p=3 excluded (3|C1)"] and named["101/2"]["p=11 criterion"]
                           and named["101/2"]["p=11 tau"] == 7 and named["101/2"]["p=11 V map"] == (1, 7)
                           and named["101/2"]["p=11 zero within p blocks"])
    g, Cs, D = cut_data(5, 2, [(1,), (3, 1)])
    named["5/2"] = {"g": g, "C": Cs, "D": D, "p=3 criterion": (D % 3 == 0) and (Cs[0] % 3 != 0),
                    "p=3 tau": closed_map(5, 2, (1,), 3)[1], "p=3 V map": closed_map(5, 2, (3, 1), 3),
                    "p=3 zero within p blocks": zero_within_p_blocks(5, 2, (1,), (3, 1), 3)}
    named["5/2"]["ok"] = (D == 3 and named["5/2"]["p=3 criterion"] and named["5/2"]["p=3 V map"][0] == 1
                         and named["5/2"]["p=3 V map"][1] == named["5/2"]["p=3 tau"] != 0 and named["5/2"]["p=3 zero within p blocks"])
    # B-1 証人の (U,V): g=1, D | a-b, p|d ∧ p∤c ⇒ 両語が q -> q + c/b
    wit = {}
    for (a, b, R, m) in [(101, 2, 15, 1), (101, 100, 21, 1), (5, 2, 1, 1), (7, 5, 1, 2), (7, 5, 3, 1), (9, 7, 1, 2), (6, 5, 1, 1)]:
        w = obr_witness(a, b, R, m)
        cert = interval_certificate(a, b, w["h"], w["c"], full=False)
        U, V = tuple(cert["U"]), tuple(cert["V"])
        g, Cs, D = cut_data(a, b, [U, V])
        d, c = w["d"], w["c"]
        good_primes = [p for p in primes_upto(200) if (a * b) % p and D % p == 0 and Cs[0] % p]
        ok = (g == 1) and ((a - b) % D == 0)
        for p in [p for p in primes_upto(200) if (a * b) % p and d % p == 0 and c % p]:
            binv = modinv(b, p)
            tau = (c * binv) % p
            ok &= closed_map(a, b, U, p) == (1, tau) and closed_map(a, b, V, p) == (1, tau)
            ok &= zero_within_p_blocks(a, b, U, V, p)
        wit[str([a, b, R, m])] = {"U": U, "V": V, "g": g, "C": Cs, "D": D, "usable primes p<=200": good_primes, "ok": ok}
    all_ok = (not fails) and all(v["ok"] for v in named.values()) and all(v["ok"] for v in wit.values())
    out = {"check": "B-9 CUT-T", "primes": PRIMES, "families": families,
           "n_(W,p)_checked": counter[0], "n_criterion_true": counter[1],
           "failures": fails[:50], "n_failures": len(fails), "named": named, "witness_pairs": wit,
           "all_pass": all_ok, "status": "success",
           "summary": "%d (W,p) pairs: closed-form ⟺ criterion ⟺ iteration in both directions, %d true; named 101/2 (D=99,C1=69,tau=7 at p=11) ok=%s, 5/2 (D=3) ok=%s"
                      % (counter[0], counter[1], named["101/2"]["ok"], named["5/2"]["ok"])}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
