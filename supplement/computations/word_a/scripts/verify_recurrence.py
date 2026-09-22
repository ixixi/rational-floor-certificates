"""Finite prefix-return certificates for permutation recurrences.

Standard library only. This script checks finite algebraic statements and an
exact rational-floor example. It does NOT establish recurrence of every carry
word, total termination, or the desired rational-family theorem.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product, permutations
from math import gcd
from pathlib import Path
import json
import random
from typing import Sequence

Permutation = tuple[int, ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def compose(f: Permutation, g: Permutation) -> Permutation:
    """Return f o g: apply g first, then f."""
    return tuple(f[x] for x in g)


def certificate(word: Sequence[int], maps: dict[int, Permutation],
                times: Sequence[int], start: int, prefix_length: int = 0) -> dict:
    """Verify a finite copy tower and extract a congruence-return witness.

    The condition at step k is
       word[t_k:t_k + S_(k-1) + L] == word[:S_(k-1) + L],
    where S_(k-1) is the sum of the preceding t_i. If at least m times
    are supplied for permutations of m points, a witness is guaranteed.
    Fewer times can already suffice, as in the rational-floor example.
    """
    require(bool(maps), 'No transition maps supplied.')
    m = len(next(iter(maps.values())))
    require(m >= 1 and 0 <= start < m and prefix_length >= 0, 'Bad state or length.')
    for p in maps.values():
        require(len(p) == m and sorted(p) == list(range(m)), 'Transition is not a permutation.')
    require(all(c in maps for c in word), 'Missing letter map.')
    require(all(t > 0 for t in times), 'Return times must be positive.')
    total = sum(times)
    require(total + prefix_length <= len(word), 'Insufficient finite word.')
    S = 0
    for t in times:
        require(list(word[t:t + S + prefix_length]) == list(word[:S + prefix_length]),
                'Prefix-copy condition failed.')
        S += t

    identity = tuple(range(m))
    forward = [identity]
    for c in word[:total]:
        forward.append(compose(maps[c], forward[-1]))

    # H_k = G_(t_1) o ... o G_(t_k), not the chronological product.
    H = identity
    seen = {start: 0}
    images = [start]
    witness = None
    for k, t in enumerate(times, 1):
        H = compose(H, forward[t])
        image = H[start]
        images.append(image)
        if image in seen and witness is None:
            i = seen[image]
            n = sum(times[i:k])
            B = identity
            for tj in times[i:k]:
                B = compose(B, forward[tj])
            require(B == forward[n], 'Consecutive-sum composition failed.')
            require(B[start] == start, 'Witness does not return to the initial state.')
            require(list(word[n:n + prefix_length]) == list(word[:prefix_length]),
                    'Witness lost the requested output prefix.')
            witness = {'left': i, 'right': k, 'return_time': n}
        seen.setdefault(image, k)
    require(len(times) < m or witness is not None, 'Pigeonhole conclusion failed.')

    # Exhaustively check the stronger finite-sums identity for small towers.
    if len(times) <= 10:
        for flags in product((False, True), repeat=len(times)):
            n, F = 0, identity
            for take, t in zip(flags, times):
                if take:
                    n += t
                    F = compose(F, forward[t])
            require(F == forward[n], 'Finite-sums identity failed.')
            require(list(word[n:n + prefix_length]) == list(word[:prefix_length]),
                    'Finite-sums output return failed.')
    return {'modulus_size': m, 'height': len(times), 'total_time': total,
            'prefix_length': prefix_length, 'images': images, 'witness': witness}


def binary_towers(word: tuple[int, ...], height: int):
    """Enumerate all positive-time towers fitting in a given word, L=0."""
    def visit(times: tuple[int, ...], S: int):
        if len(times) == height:
            yield times
            return
        for t in range(1, len(word) - S + 1):
            if word[t:t + S] == word[:S]:
                yield from visit(times + (t,), S + t)
    yield from visit((), 0)


def exhaustive_small() -> dict:
    cases = towers = 0
    for m, length in ((2, 7), (3, 6)):
        ps = list(permutations(range(m)))
        for word in product((0, 1), repeat=length):
            for ts in binary_towers(word, m):
                towers += 1
                for f, g in product(ps, repeat=2):
                    for x in range(m):
                        result = certificate(word, {0: f, 1: g}, ts, x)
                        require(result['witness'] is not None, 'Missing exhaustive witness.')
                        cases += 1
    return {'binary_towers': towers, 'permutation_and_state_cases': cases}


def constructed_towers() -> dict:
    rng = random.Random(20260920)
    cases = 0
    largest_word = 0
    for m in range(2, 10):
        for trial in range(8):
            L = 1 + trial % 3
            word = [rng.randrange(3) for _ in range(L)]
            ts = []
            for _ in range(m):
                middle = [rng.randrange(3) for _ in range(1 + rng.randrange(3))]
                ts.append(len(word) + len(middle))
                word = word + middle + word
            maps = {}
            for c in range(3):
                p = list(range(m)); rng.shuffle(p); maps[c] = tuple(p)
            result = certificate(word, maps, ts, rng.randrange(m), L)
            require(result['witness'] is not None, 'Missing constructed witness.')
            cases += 1
            largest_word = max(largest_word, len(word))
    return {'cases': cases, 'largest_word_length': largest_word}


def exact_floor_example() -> dict:
    a, b, P, last = 9, 7, 11, 44
    x = Fraction(P)
    Q = []
    for _ in range(last + 1):
        Q.append(x.numerator // x.denominator)
        x *= Fraction(a, b)
    word = [b * v - a * u for u, v in zip(Q, Q[1:])]
    inv = pow(b, -1, P)
    maps = {c: tuple((a * z + c) * inv % P for z in range(P)) for c in set(word)}
    proof = certificate(word, maps, [1, 43], 0)
    require(word[0] == word[43] == -1, 'Example prefix copies failed.')
    require(proof['witness']['return_time'] == 44, 'Unexpected witness time.')
    require(Q[44] == 697829 == 11 * 63439 and Q[44] > P, 'Example divisibility failed.')
    return {'a': a, 'b': b, 'xi': str(P), 'initial_integer': P,
            'c0': word[0], 'c43': word[43], 'copy_times': [1, 43],
            'term_index': 44, 'term': Q[44], 'factorization': [11, 63439],
            'certificate': proof,
            'scope': 'A finite certificate; no recurrence assertion for the complete word.'}


def check_digit_bijections() -> dict:
    cases = 0
    for t in range(1, 7):
        a, b, k = 6*t+3, 6*t+1, 3*t+1
        for length in range(1, 4):
            modulus = b ** length
            # Each odd residue modulo 2*b^length represents one residue modulo b^length.
            word_to_residue = {}
            for z in range(modulus):
                Q = 2*z+1
                start = Q % modulus
                word = []
                for _ in range(length):
                    nxt = Q + 2*((Q+k)//b)
                    word.append(b*nxt-a*Q)
                    Q = nxt
                key = tuple(word)
                require(key not in word_to_residue, 'Carry/residue collision.')
                word_to_residue[key] = start
                cases += 1
            require(len(set(word_to_residue.values())) == modulus, 'Incomplete residue coverage.')
    return {'instances': cases, 'max_t': 6, 'max_length': 3}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('recurrence_checks.json'))
    args = parser.parse_args()
    result = {'status': 'all_finite_checks_passed',
              'exhaustive': exhaustive_small(),
              'constructed': constructed_towers(),
              'floor_example': exact_floor_example(),
              'digit_bijections': check_digit_bijections(),
              'scope': 'Finite identities and certificates only. No all-seed recurrence or family theorem. No Lean proof.'}
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
