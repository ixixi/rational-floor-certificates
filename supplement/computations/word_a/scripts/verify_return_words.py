#!/usr/bin/env python3
"""Exact, self-contained checks for the return-word research note.

Python standard library only. No floating point, primality oracle, graph
library, generated word lists, or assertions whose removal changes checking.
This checks finite certificates, not the sought infinite-family theorem.
"""
from __future__ import annotations

import json
from fractions import Fraction
from math import gcd
from pathlib import Path
from typing import Any, Sequence

Q = Fraction

def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def inspect_interval(a: int, b: int, word: Sequence[int],
                     interval: tuple[Q, Q]) -> dict[str, Any]:
    """Check every backwards suffix image, including the complete word."""
    lo, hi = interval
    require(0 < lo < hi < 1, 'interval is not strictly inside (0,1)')
    x, y = lo, hi
    least, greatest = lo, hi
    for c in reversed(word):
        x, y = (b*x + c)/a, (b*y + c)/a
        least, greatest = min(least, x), max(greatest, y)
        require(0 < x <= y < 1, 'an intermediate fractional interval escapes')
    require(lo <= x <= y <= hi, 'return interval is not invariant')
    # Independently form the whole-word affine numerator, then run forwards.
    C, bn, an = 0, 1, 1
    for c in word:
        C, bn, an = a*C + bn*c, b*bn, a*an
    require(x == (C + bn*lo)/an and y == (C + bn*hi)/an,
            'whole-word formula disagrees with reverse composition')
    for start, finish in ((x,lo),(y,hi)):
        z = start
        for c in word:
            z = (a*z - c)/b
            require(0 < z < 1, 'forward interval endpoint escapes')
        require(z == finish, 'forward endpoint mismatch')
    return {'length': len(word), 'image': [str(x), str(y)],
            'all_suffix_min': str(least), 'all_suffix_max': str(greatest)}


def inspect_residue(a: int, b: int, modulus: int, root: int,
                    word: Sequence[int]) -> list[int]:
    require(gcd(a*b, modulus) == 1, 'noninvertible residue modulus')
    require(gcd(root, modulus) == 1, 'nonunit root')
    inv_b = pow(b, -1, modulus)
    residues = [root]
    for c in word:
        require(1-b <= c <= a-1, 'carry outside universal range')
        require((c - (b-a)) % 2 == 0, 'wrong carry parity')
        require(gcd(c, a*b) == 1, 'carry has a factor from a or b')
        z = (a*residues[-1] + c)*inv_b % modulus
        require(gcd(z, modulus) == 1, 'nonunit intermediate residue')
        residues.append(z)
    require(residues[-1] == root, 'residue word does not return to root')
    return residues


WITNESSES: list[dict[str, Any]] = [
    {'name': 'nine_sevenths_S13', 'a': 9, 'b': 7, 'modulus': 715,
     'root': 713, 'interval': ('1/5', '3/10'),
     'U': [2,-2,2,-2,4,-4,2,2,2,2,-4,4,-2,4,4,-4,2,4],
     'V': [2,-2,-4,8,-4,4,-2,4,-4,4,2,2,2,-4,2,4,4]},
    {'name': 'six_fifths_S13', 'a': 6, 'b': 5, 'modulus': 1001,
     'root': 380, 'interval': ('4/5', '19/20'),
     'U': [1]*15 + [-1,1,-1,1,-1,1,1,1,1,-1,-1,-1],
     'V': [1]*15 + [-1,1,-1,1,1,1,-1,-1,1,1,-1,-1]},
    {'name': 'six_fifths_S17', 'a': 6, 'b': 5, 'modulus': 17017,
     'root': 12854, 'interval': ('9/10', '49/50'),
     'U': [1]*15 + [-1,1,1,1,-1,-1,-1] + [1]*9 + [-1,-1],
     'V': [1]*15 + [-1] + [1]*12 + [-1,-1,1,1,1,-1,1,1,1,-1,-1]},
]


def check_witness(w: dict[str, Any]) -> dict[str, Any]:
    a,b,m,q = w['a'],w['b'],w['modulus'],w['root']
    U,V = w['U'],w['V']
    require(U+V != V+U, 'return words commute')
    I = tuple(Q(x) for x in w['interval'])
    answer = {'name':w['name'], 'a':a, 'b':b, 'modulus':m,
              'root':q, 'interval':w['interval'], 'noncommuting':True}
    for label, word in [('U',U),('V',V)]:
        answer[label] = inspect_interval(a,b,word,I)
        answer[label]['word'] = word
        answer[label]['residues'] = inspect_residue(a,b,m,q,word)
    return answer


def check_prime17_blocker(w: dict[str, Any]) -> dict[str, Any]:
    a,b,p = w['a'],w['b'],17
    edges: list[list[Any]] = []
    for q in range(1,p):
        for label in ('U','V'):
            z=q
            for c in w[label]:
                z=(a*z+c)*pow(b,-1,p)%p
                if z==0:
                    break
            else:
                edges.append([q,label,z])
    expected = [[4,'U',16],[4,'V',16],[5,'U',1],[6,'V',4],
                [8,'V',9],[9,'U',9],[10,'V',14],[11,'U',13],
                [11,'V',8],[14,'U',2],[15,'U',4],[16,'V',12]]
    require(edges == expected, 'prime-17 edge table mismatch')
    rank={1:0,2:0,3:0,4:2,5:1,6:3,7:0,8:1,9:0,10:2,
          11:2,12:0,13:0,14:1,15:3,16:1}
    for q,label,z in edges:
        if q==z:
            require(q==9 and label=='U', 'unexpected internal periodic edge')
        else:
            require(rank[q] > rank[z], 'rank does not strictly decrease')
    return {'prime':p,'edges':edges,'rank':rank,
            'only_recurrent_edge':[9,'U',9]}


def check_general_interval_examples() -> dict[str, Any]:
    """Finite formula checks, explicitly not a substitute for the general proof."""
    cases=0
    for b in range(2,65):
        for a in range(b+1,2*b):
            if gcd(a,b)!=1:
                continue
            r=Q(a,b);d=a-b;L=2
            while r**(L-1)*(2-r) <= 1:
                L+=1
            def point(k: int) -> Q:
                return 1-Q(2)/sum((r**j for j in range(k)),Q(0))
            I=(point(L),point(L+1))
            U=[d]*(L-1)+[-d];V=[d]*L+[-d]
            inspect_interval(a,b,U,I);inspect_interval(a,b,V,I)
            require(U+V != V+U,'unexpected commutation')
            cases+=1
    return {'reduced_pairs_checked':cases,'denominator_limit':64,
            'scope':'checks of the analytic formula only'}


def main() -> None:
    results = {'status':'all_finite_checks_passed',
               'scope':'return-word obstruction certificates and one language blocker; not a compositeness proof for a new base',
               'witnesses':[check_witness(w) for w in WITNESSES],
               'prime17_language_blocker':check_prime17_blocker(WITNESSES[0]),
               'general_formula_checks':check_general_interval_examples()}
    output=Path(__file__).with_name('verified_results.json')
    output.write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':results['status'],
                      'certificates':len(WITNESSES),
                      'general_formula_checks':results['general_formula_checks'],
                      'output':str(output)},ensure_ascii=False))

if __name__=='__main__':
    main()
