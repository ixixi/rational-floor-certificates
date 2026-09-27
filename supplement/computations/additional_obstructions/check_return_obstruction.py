#!/usr/bin/env python3
"""Check the explicit 5/3 return-word obstruction without loading a search graph.

Uses composite-modulus closed residue formulas, and independent closed forms for
all backward suffix maps. Standard library only. Run without Python -O.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from math import gcd, prod, isqrt
from pathlib import Path


def check(path: Path) -> dict:
    data = json.loads(path.read_text(encoding='utf-8'))
    a, b, m, q = (data[key] for key in ('a', 'b', 'modulus', 'residue'))
    primes = data['primes']
    assert a > b >= 2 and gcd(a, b) == 1
    assert len(primes) == len(set(primes))
    assert all(p >= 2 and all(p % d for d in range(2, isqrt(p)+1)) for p in primes)
    assert prod(primes) == m and gcd(m, a*b) == gcd(q, m) == 1
    U, V = data['U'], data['V']
    assert U and V and U+V != V+U
    L, H = (Fraction(*pair) for pair in data['interval'])
    assert 0 < L < H < 1
    checks = []
    for word in (U, V):
        assert all(1-b <= c < a and (c-b+a) % 2 == 0 and gcd(c, a*b) == 1 for c in word)
        C = 0
        residue_count = 1
        last = q
        for j, c in enumerate(word, 1):
            C = a*C + b**(j-1)*c
            last = (a**j*q+C)*pow(b**j, -1, m) % m
            assert gcd(last, m) == 1
            residue_count += 1
        assert last == q
        for j in range(len(word)):
            length = len(word)-j
            constant = sum(a**(length-1-i)*b**i*c for i, c in enumerate(word[j:]))
            left = (b**length*L+constant)/a**length
            right = (b**length*H+constant)/a**length
            assert 0 < left <= right < 1
            if j == 0:
                assert L <= left and right <= H
        checks.append(dict(length=len(word), unit_residues_checked=residue_count,
                           suffix_endpoint_pairs_checked=len(word), returns_to=q))
    return dict(status='verified', base=f'{a}/{b}', modulus=m, residue=q,
                interval=[str(L),str(H)], word_checks=checks,
                excluded_prime_pool=[2,3,5,7,11,13,17,19,23],
                conclusion='No certificate of the paper procedure, or its two-direction pseudo-orbit-sound extensions, using only these primes, at any cell count or prime-power exponents.',
                not_concluded='No claim of a true prime-avoiding orbit or failure of infinitely many composite terms.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('witness', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check(args.witness)
    text = json.dumps(result, indent=2)
    if args.output:
        args.output.write_text(text+'\n', encoding='utf-8')
    print(text)
