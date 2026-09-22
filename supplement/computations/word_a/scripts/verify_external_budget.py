#!/usr/bin/env python3
"""Exact checks for an external-prime-budget obstruction.

These finite checks exercise the formulas; the general theorem is proved in
external_prime_budget.md. No randomized primality test or floating point is used.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction
from functools import lru_cache
from math import gcd, prod
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


@lru_cache(None)
def prime_factors(n: int) -> tuple[int, ...]:
    if n < 1:
        raise ValueError('positive integer required')
    out: list[int] = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return tuple(out)


@lru_cache(None)
def jacobsthal(n: int) -> int:
    if n == 1:
        return 1
    units = [j for j in range(n) if gcd(j, n) == 1]
    return max(y-x for x, y in zip(units, units[1:] + [units[0] + n]))


def point(a: int, b: int, h: int, length: int) -> Fraction:
    # Fixed point of the backward word d^length (d-h).
    return 1 - Fraction(h * b**length, a**(length+1) - b**(length+1))


def interval_certificate(a: int, b: int, R: int, m: int) -> dict:
    d, h = a-b, 2*R*m
    c = d-h
    require(a > b >= 2 and gcd(a,b) == 1, 'base')
    require(gcd(R,2*a*b) == 1 and R >= 1, 'external modulus')
    require(h <= a-1 and m >= 1 and gcd(c,a*b) == 1, 'witness')
    require(1-b <= c < d <= a-1, 'carry range')
    require((c-(b-a)) % 2 == 0, 'carry parity')
    threshold = max(Fraction(0), Fraction(-c,b))
    length = 0
    while point(a,b,h,length) <= threshold:
        length += 1
        if length > 100000:
            raise RuntimeError('inconclusive: interval search cutoff')
    lo, hi = point(a,b,h,length), point(a,b,h,length+1)
    require(0 < lo < hi < 1, 'strict invariant interval')
    U, V = [d]*length+[c], [d]*(length+1)+[c]
    for w in (U,V):
        lower, upper = lo, hi
        for letter in reversed(w):
            lower = (b*lower + letter)/a
            upper = (b*upper + letter)/a
            require(0 < lower <= upper < 1, 'inside fractional interval')
        require(lo <= lower <= upper <= hi, 'return into common interval')
        ell = len(w)-1
        for x in (lo, hi):
            formula = 1+Fraction(b,a)**(ell+1)*(x-1)-Fraction(h,a)*Fraction(b,a)**ell
            y = x
            for letter in reversed(w):
                y = (b*y+letter)/a
            require(formula == y, 'word affine formula')
    require(U+V != V+U, 'noncommuting return words')
    return {'a':a,'b':b,'R':R,'m':m,'h':h,'d':d,'c':c,
            'L':length,'interval':[str(lo),str(hi)],'U':U,'V':V}


def check_lifts(cert: dict) -> int:
    a,b,R,d,c = (cert[k] for k in ('a','b','R','d','c'))
    U,V = cert['U'], cert['V']
    # A finite portion of the equal-length encoding UV/VU using Thue-Morse.
    word: list[int] = []
    for i in range(8):
        word.extend(U+V if i.bit_count()%2 == 0 else V+U)
    lo, hi = map(Fraction,cert['interval'])
    theta = (lo+hi)/2
    for letter in reversed(word):
        prev = (b*theta+letter)/a
        require(0 < prev < 1, 'finite exact real path')
        require(a*prev-b*theta == letter, 'real recurrence')
        theta = prev
    count = 0
    for p in prime_factors(2*a*b*R):
        for exponent in (1,2,3):
            modulus = p**exponent
            q = [0]*(len(word)+1)
            if b % p:
                q[0] = -1 % modulus if R%p == 0 else 1
                bi = pow(b,-1,modulus)
                for i,letter in enumerate(word):
                    q[i+1] = bi*(a*q[i]+letter)%modulus
            else:
                q[-1] = 1
                ai = pow(a,-1,modulus)
                for i in range(len(word)-1,-1,-1):
                    q[i] = ai*(b*q[i+1]-word[i])%modulus
            for i,letter in enumerate(word):
                require((b*q[i+1]-a*q[i]-letter)%modulus == 0,'lift recurrence')
                require(q[i]%p != 0 and q[i+1]%p != 0,'unit lift')
                if R%p == 0:
                    require(q[i]%p == -1%p and q[i+1]%p == -1%p,'external constant reduction')
                count += 1
    return count


def carry_sum(a: int, b: int, word: list[int]) -> int:
    C=0
    power=1
    for c in word:
        C=a*C+power*c
        power*=b
    return C


def translation_divisor(a: int, b: int, words: list[list[int]]) -> tuple[int,int]:
    if not words or any(not w for w in words):
        raise ValueError('nonempty words required')
    period=0
    for w in words:
        period=gcd(period,len(w))
    Cs=[carry_sum(a,b,w) for w in words]
    lengths=[len(w) for w in words]
    D=a**period-b**period
    for C,ell in zip(Cs[1:],lengths[1:]):
        D=gcd(D,C*b**lengths[0]-Cs[0]*b**ell)
    return D,Cs[0]


def check_translation_criterion() -> int:
    count=0
    small_primes=(3,5,7,11,13,17,19,23,29,31)
    for a in range(3,19):
        for b in range(2,a):
            if gcd(a,b)!=1:
                continue
            d=a-b
            alphabet=[c for c in range(1-b,a) if (c-d)%2==0 and gcd(c,a*b)==1]
            for c in alphabet:
                for L in range(4):
                    words=[[d]*L+[c],[d]*(L+1)+[c]]
                    D,C0=translation_divisor(a,b,words)
                    for p in small_primes:
                        if a*b%p==0:
                            continue
                        expected=(D%p==0 and C0%p!=0)
                        affine=[]
                        bi=pow(b,-1,p)
                        for w in words:
                            alpha,beta=1,0
                            for letter in w:
                                alpha=a*bi*alpha%p
                                beta=bi*(a*beta+letter)%p
                            affine.append((alpha,beta))
                        actual=(all(alpha==1 for alpha,beta in affine)
                                and affine[0][1]!=0
                                and all(beta==affine[0][1] for alpha,beta in affine))
                        require(expected==actual,'exact translation-prime characterization')
                        count+=1
    return count


def check_prime_cut(cert: dict, p: int) -> None:
    a,b,d,c = (cert[k] for k in ('a','b','d','c'))
    require(prime_factors(p) == (p,), 'prime')
    require(d%p == 0 and c%p != 0, 'translation condition')
    bi=pow(b,-1,p)
    shift=bi*c%p
    for w in (cert['U'],cert['V']):
        for q in range(p):
            y=q
            for letter in w:
                y=bi*(a*y+letter)%p
            require(y == (q+shift)%p,'same nonzero macro translation')
    for q in range(p):
        require(0 in [(q+j*shift)%p for j in range(p)],'forced zero in at most p blocks')


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-a',type=int,default=60)
    parser.add_argument('--output',type=Path,default=Path('external_budget_checks.json'))
    args=parser.parse_args()
    bases=tests=witnesses=jacobsthal_forced=lift_transitions=0
    max_length=0
    chosen: list[dict]=[]
    for a in range(3,args.max_a+1):
        for b in range(2,a):
            if gcd(a,b) != 1:
                continue
            bases += 1
            odd = tuple(p for p in prime_factors(a*b) if p!=2)
            N=prod(odd)
            J=jacobsthal(N)
            require(J <= 3**len(odd),'elementary Jacobsthal bound')
            external=[p for p in (3,5,7,11) if (a*b)%p]
            products={1,*external}
            products.update(external[i]*external[j] for i in range(len(external)) for j in range(i+1,len(external)))
            for R in sorted(products):
                tests += 1
                H=(a-1)//(2*R)
                m=next((j for j in range(1,H+1) if gcd(a-b-2*R*j,a*b)==1),None)
                if H>=J:
                    jacobsthal_forced += 1
                    require(m is not None,'Jacobsthal guarantees a witness')
                if m is None:
                    continue
                witnesses += 1
                cert=interval_certificate(a,b,R,m)
                max_length=max(max_length,cert['L'])
                # Independently exercise prime-power lifts for a deterministic subset.
                if witnesses%13 == 0:
                    lift_transitions += check_lifts(cert)
    for a,b,R,m,p in ((101,2,15,1,11),(101,100,21,1,None),(5,2,1,1,3)):
        cert=interval_certificate(a,b,R,m)
        cert['odd_radical_ab']=prod(p for p in prime_factors(a*b) if p!=2)
        cert['jacobsthal']=jacobsthal(cert['odd_radical_ab'])
        lift_transitions += check_lifts(cert)
        if p is not None:
            check_prime_cut(cert,p)
            cert['eliminating_prime_for_this_two_word_language']=p
            cert['translation_divisor'],cert['first_carry_sum']=translation_divisor(a,b,[cert['U'],cert['V']])
        chosen.append(cert)
    translation_checks=check_translation_criterion()
    result={'status':'all finite checks passed','translation_prime_criterion_checks':translation_checks,'max_a':args.max_a,'reduced_bases':bases,
            'base_external_set_cases':tests,'arithmetic_obstruction_witnesses':witnesses,
            'jacobsthal_guaranteed_cases':jacobsthal_forced,
            'largest_L_in_small_base_checks':max_length,
            'prime_power_unit_transitions_checked':lift_transitions,
            'examples':chosen,
            'scope':'Checks of a general analytic obstruction theorem and a conditional macro-language elimination lemma. Not an infinite-family compositeness theorem and not Lean formalization.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='examples'},ensure_ascii=False,indent=2))
    for cert in chosen:
        print({k:v for k,v in cert.items() if k not in ('U','V')})


if __name__=='__main__':
    main()
