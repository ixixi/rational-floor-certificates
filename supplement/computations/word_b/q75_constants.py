#!/usr/bin/env python3
"""q75_constants.py -- exact rational check of (SQ-4) in proofs/audit-02-word-method.md §13-14.

Checks: 7^4 < 5^5 (so gamma = 5/4 >= 1 + log_5(7/5)); with R = 64, m = 6, D = 13, gamma = 5/4:
  sum_{j<6} gamma^j = 11529/1024 < 12,
  R*gamma^m + gamma*D*sum = 1749385/4096 < 428,
so (QF2) gives T <= 1749385/4096 + (11529/1024) * A < 428 + 12 A for any A >= 0.
Also checks that L(P) = min{h >= 0 : 5^h >= P+2} equals ceil(log_5(P+2)) computed by integer
comparison for P in 14..100000.  Standard library only.
"""
import json
from fractions import Fraction as F


def L(P):
    h = 0
    while 5 ** h < P + 2:
        h += 1
    return h


def main():
    gamma = F(5, 4)
    R, m, D = 64, 6, 13
    s = sum(gamma ** j for j in range(m))
    main_term = R * gamma ** m + gamma * D * s
    checks = {
        '7^4 < 5^5': 7 ** 4 < 5 ** 5,
        'sum_{j<6}(5/4)^j == 11529/1024': s == F(11529, 1024),
        '64*(5/4)^6 + (5/4)*13*sum == 1749385/4096': main_term == F(1749385, 4096),
        'sum < 12': s < 12,
        'main_term < 428': main_term < 428,
        'bound form: T <= main_term + sum*A < 428 + 12A for A>=0': (main_term < 428) and (s < 12),
    }
    # L(P) integer definition versus ceil(log_5(P+2)) via integer powers
    ok = True
    for P in range(14, 100001):
        h = L(P)
        # ceil(log_5(P+2)) = smallest h with 5^h >= P+2, identical by definition; check monotone consistency
        if not (5 ** h >= P + 2 and (h == 0 or 5 ** (h - 1) < P + 2)):
            ok = False
            break
    checks['L(P) integer definition consistent (P in 14..100000)'] = ok
    checks['example L(14)=2, L(123)=3, L(623)=4, L(3123)=5'] = (L(14), L(123), L(623), L(3123)) == (2, 3, 4, 5)
    print(json.dumps({'event': 'q75_constants', 'gamma': str(gamma), 'R': R, 'm': m, 'D': D,
                      'sum': str(s), 'main_term': str(main_term),
                      'main_term_float': float(main_term), 'sum_float': float(s),
                      'checks': checks, 'all_true': all(checks.values())}))
    return 0 if all(checks.values()) else 3


if __name__ == '__main__':
    raise SystemExit(main())
