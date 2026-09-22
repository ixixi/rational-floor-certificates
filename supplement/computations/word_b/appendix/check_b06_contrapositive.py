#!/usr/bin/env python3
"""B-6: 対偶と u（audit-03 §3.10）。全 (a,b,R) で gcd(d-2Rm,ab)=1 ⟺ gcd(m-u,N)=1、
H>=J(N) ⇒ 証人、証人なし ⇒ a<=2RJ(N) かつ R>=a/(2·3^k)。"""
import json
from math import gcd
from obmath import trial_factor, is_squarefree, modinv, unit_mask, obr_witness
from check_b05_jacobsthal import j_gap, all_windows_have_unit

A_MAX = 120
R_MAX = 60


def jacobsthal(N, cache={}):
    if N in cache:
        return cache[N]
    primes = sorted(trial_factor(N))
    mask = bytes(unit_mask(N, primes))
    g = j_gap(mask, N)
    assert all_windows_have_unit(mask, N, g) and (g == 1 or not all_windows_have_unit(mask, N, g - 1))
    cache[N] = g
    return g


def main():
    n_triples = n_m = n_forced = n_nowit = n_wit = 0
    fails = []
    Rs = [R for R in range(1, R_MAX + 1) if is_squarefree(R)]
    for a in range(3, A_MAX + 1):
        for b in range(2, a):
            if gcd(a, b) != 1:
                continue
            d = a - b
            ab = a * b
            fac = trial_factor(ab)
            odd_primes = [p for p in fac if p != 2]
            N = 1
            for p in odd_primes:
                N *= p
            k = len(odd_primes)
            J = jacobsthal(N)
            for R in Rs:
                if gcd(R, 2 * ab) != 1:
                    continue
                n_triples += 1
                H = (a - 1) // (2 * R)
                u = (d * modinv(2 * R, N)) % N
                witness = None
                for m in range(1, H + 1):
                    n_m += 1
                    lhs = gcd(abs(d - 2 * R * m), ab) == 1
                    rhs = gcd(abs(m - u), N) == 1
                    if lhs != rhs:
                        fails.append({"a": a, "b": b, "R": R, "m": m, "type": "u-equivalence"})
                    if lhs and witness is None:
                        witness = m
                if H >= J:
                    n_forced += 1
                    if witness is None:
                        fails.append({"a": a, "b": b, "R": R, "type": "H>=J but no witness"})
                if witness is None:
                    n_nowit += 1
                    if not (a <= 2 * R * J):
                        fails.append({"a": a, "b": b, "R": R, "type": "(B) a<=2RJ violated"})
                    if not (2 * (3 ** k) * R >= a):
                        fails.append({"a": a, "b": b, "R": R, "type": "(C) R>=a/(2·3^k) violated"})
                else:
                    n_wit += 1
                    w = obr_witness(a, b, R, witness)
                    if not (w["accepted"] and w["derived_all"]):
                        fails.append({"a": a, "b": b, "R": R, "m": witness, "type": "B-1 rejects witness"})
    out = {"check": "B-6 contrapositive and u", "A_max": A_MAX, "R_max": R_MAX,
           "n_triples": n_triples, "n_m_checked": n_m, "n_H>=J": n_forced, "n_no_witness": n_nowit, "n_witness": n_wit,
           "failures": fails[:50], "n_failures": len(fails),
           "all_pass": not fails, "status": "success",
           "summary": "%d (a,b,R) triples, %d m values: u-equivalence, H>=J forcing (%d), (B),(C) on %d no-witness triples; failures=%d"
                      % (n_triples, n_m, n_forced, n_nowit, len(fails))}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
