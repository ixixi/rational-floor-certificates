"""Exact integer checks of proved prime-tail reductions, not a termination proof.
Only Python standard library is used.  Run: python3 check_reductions.py
"""
from math import gcd
from pathlib import Path
import json


def ceil_div(n: int, d: int) -> int:
    if d <= 0:
        raise ValueError('positive denominator required')
    return -((-n) // d)


def possible_successors(a: int, b: int, q: int) -> range:
    # floor(r x) for x in [q,q+1); the upper endpoint is excluded.
    return range(a*q//b, (a*(q+1)-1)//b + 1)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def fork_covered(a: int, b: int) -> bool:
    d = a-b
    return all(gcd(k,b)>1 or gcd(d+k,a)>1 or gcd(d-k,a)>1
               or ((a%3==0)!=(k%3==0))
               for k in range(1,d) if k%2 == a%2)


def lower_fork_covered(a: int, b: int) -> bool:
    d = a-b
    return all(gcd(d+k,a)>1 for k in range(1,d) if k%2 == a%2)


def check() -> dict:
    counts = {'gap2_unit6_one_step': 0, 'gap2_conjugacy': 0,
              'gap2_digit_identities': 0, 'general_covered_prime_sources': 0,
              'ordinary_ceiling_conjugacy': 0, 'ordinary_digit_identities': 0}
    sample_digits = {}
    for t in range(1,41):
        a,b = 6*t+3, 6*t+1
        delta = t%2
        H = 3*t-1-delta
        for q in range(1,2001,2):
            if gcd(q,6) != 1:
                continue
            candidates = [v for v in possible_successors(a,b,q) if gcd(v,6)==1]
            T = q + 2*((q+3*t+1)//b)
            assert len(candidates) <= 1, (t,q,candidates)
            assert candidates == ([T] if gcd(T,6)==1 else []), (t,q,candidates,T)
            counts['gap2_unit6_one_step'] += 1
            z = (q-H)//2
            zp = ceil_div(a*z-delta,b)
            assert 2*zp+H == T
            counts['gap2_conjugacy'] += 1
            e = b*zp-a*z+delta
            carry = b*T-a*q
            assert 0 <= e <= b-1
            assert carry == 2*(e-(3*t-1))
            assert (T%3==0) == (e%3==2)
            assert (gcd(carry,a*b)==1) == (gcd(e-(3*t-1),a*b)==1)
            counts['gap2_digit_identities'] += 1
        if t <= 4:
            sample_digits[str(t)] = [e for e in range(b) if gcd(e-(3*t-1),a*b)==1]
    covered = []
    for b in range(2,65):
        for a in range(b+1,2*b):
            if gcd(a,b)!=1 or not fork_covered(a,b):
                continue
            covered.append([a,b])
            for q in range(max(a,b,2)+1,801):
                if not is_prime(q):
                    continue
                candidates = [v for v in possible_successors(a,b,q) if is_prime(v)]
                assert len(candidates)<=1, (a,b,q,candidates)
                counts['general_covered_prime_sources'] += 1
    ceiling_examples = []
    for d in range(1,21):
        for h in range(1,151):
            b = 2*d*h+1
            a = b+d
            if not lower_fork_covered(a,b):
                continue
            H=2*h-1
            ceiling_examples.append([d,a,b])
            for z in range(-25,101):
                q=2*z+H
                # Largest odd integer in the exact successor interval.
                odd = [v for v in possible_successors(a,b,q) if v%2]
                largest=2*ceil_div(a*z,b)+H
                assert odd and largest==max(odd), (d,a,b,z,odd,largest)
                counts['ordinary_ceiling_conjugacy'] += 1
                zp=ceil_div(a*z,b)
                e=b*zp-a*z
                qp=2*zp+H
                assert gcd(q,b)==gcd(2*e+d+1,b)
                assert gcd(qp,a)==gcd(2*e+2*d+1,a)
                counts['ordinary_digit_identities'] += 1
    return {'status':'all finite exact checks passed; infinite termination NOT established',
            'counts':counts,'gap2_digit_sets_t_1_to_4':sample_digits,
            'fork_covered_reduced_pairs_b_at_most_64':covered,
            'ordinary_ceiling_examples':ceiling_examples,
            'scope':'Integer arithmetic and one-step algebra only. Not a proof of the desired infinite-family compositeness theorem.'}

if __name__=='__main__':
    result=check()
    path=Path(__file__).with_name('reduction_checks.json')
    path.write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ('fork_covered_reduced_pairs_b_at_most_64','ordinary_ceiling_examples')},indent=2))
