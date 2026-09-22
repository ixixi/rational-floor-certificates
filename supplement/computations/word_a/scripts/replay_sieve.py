"""Reproduce the quantitative prime-prefix sieve, without third-party Python modules.

Default: compiles and runs both exact C++ counters, compares every length count,
then verifies constants, small rational-interval counts, digit permutations,
and the nine-prime example. Requires Python 3.10+ and GNU g++ with C++17.

--quick checks embedded records and formulas but does NOT rerun the large counts.
Neither mode proves total termination or a new all-coefficient theorem.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from math import gcd, isqrt, log
from pathlib import Path
import json
import shutil
import subprocess
import tempfile

def check(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)

def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))

def digit(t: int, z: int) -> tuple[int, int]:
    a, b, delta = 6*t+3, 6*t+1, t % 2
    nxt = -((delta - a*z)//b)
    e = b*nxt-a*z+delta
    check(0 <= e < b, 'digit out of range')
    return nxt, e

def check_bijections() -> int:
    tested = 0
    for t in range(1, 7):
        b = 6*t+1
        for length in range(1, 4):
            seen = set()
            for z0 in range(b**length):
                z, code = z0, 0
                for _ in range(length):
                    z, e = digit(t, z)
                    code = b*code+e
                check(code not in seen, 'digit collision')
                seen.add(code)
                tested += 1
            check(len(seen) == b**length, 'digit coverage failure')
    return tested

def small_count(a: int, b: int, length: int) -> list[int]:
    """Initial-fraction intervals, exact fractions, direct polynomial roots."""
    carries = [c for c in range(1-b,a)
               if (c-(b-a)) % 2 == 0 and gcd(c,a*b)==1]
    primes = [p for p in range(3,length+2) if is_prime(p) and a*b % p]
    counts = [0]*(length+1)
    def visit(n: int, C: int, low: Fraction, high: Fraction,
              forbidden: tuple[frozenset[int], ...]) -> None:
        counts[n] += 1
        if n == length:
            return
        for c in carries:
            Cn = a*C+c*b**n
            an, bn = a**(n+1), b**(n+1)
            l, h = max(low,Fraction(Cn,an)), min(high,Fraction(Cn+bn,an))
            if l >= h:
                continue
            ff = tuple(S | {(-Cn*pow(an,-1,p)) % p}
                       for S,p in zip(forbidden,primes))
            if any(len(S)==p for S,p in zip(ff,primes)):
                continue
            visit(n+1,Cn,l,h,ff)
    visit(0,0,Fraction(0),Fraction(1),tuple(frozenset({0}) for _ in primes))
    return counts


SOURCE_CURRENT = '// Exhaustive necessary-condition carry-word counts. Not a primality proof.\n// Requires GNU C++17 (__int128). All interval arithmetic is exact.\n#include <algorithm>\n#include <array>\n#include <cstdint>\n#include <cstdlib>\n#include <iostream>\n#include <numeric>\n#include <vector>\nusing I=__int128_t;\nusing U=uint64_t;\nint a,b,N,J; std::vector<int> cs,ps;\nstd::vector<std::array<int,20>> wt;\nstd::array<U,20> full;\nstd::vector<U> counts;\nstd::vector<I> bp;\nU cap=1000000000ULL, visits=0;\nbool prime(int x){for(int d=2;d*d<=x;++d)if(x%d==0)return false;return x>=2;}\nint power(int x,int k,int p){int z=1;while(k){if(k&1)z=z*x%p;x=x*x%p;k>>=1;}return z;}\nvoid dfs(int n,I lo,I hi,const std::array<int,20>& roots,const std::array<U,20>& masks){\n if(++visits>cap){std::cerr<<"INCONCLUSIVE: resource cap reached\\n";std::exit(2);}\n ++counts[n]; if(n==N)return;\n for(int c:cs){\n  I l=std::max(I(0),I(a)*lo-I(c)*bp[n]);\n  I h=std::min(bp[n+1],I(a)*hi-I(c)*bp[n]);\n  if(l>=h)continue;\n  std::array<int,20> rr{};std::array<U,20> mm{};\n  bool ok=true;\n  for(int j=0;j<J;++j){int p=ps[j];int v=(roots[j]-c*wt[n][j])%p;if(v<0)v+=p;\n   rr[j]=v;mm[j]=masks[j]|(U(1)<<v);\n   if(mm[j]==full[j]){ok=false;break;}\n  }\n  if(ok)dfs(n+1,l,h,rr,mm);\n }\n}\nint main(int argc,char**argv){\n if(argc!=4){std::cerr<<"usage: count_words a b length\\n";return 1;}\n a=std::atoi(argv[1]);b=std::atoi(argv[2]);N=std::atoi(argv[3]);\n if(!(a>b&&b>=2&&std::gcd(a,b)==1&&N>=1&&N<=40&&a<=50))return 1;\n for(int c=1-b;c<a;++c)if(std::gcd(std::abs(c),a*b)==1&&(c-(b-a))%2==0)cs.push_back(c);\n for(int p=3;p<=N+1;++p)if(prime(p)&&a*b%p)ps.push_back(p);\n J=ps.size();if(J>20)return 1;wt.resize(N);\n for(int j=0;j<J;++j){int p=ps[j];int v=power(a,p-2,p);int mult=b*v%p;\n  full[j]=(U(1)<<p)-1;\n  for(int n=0;n<N;++n){wt[n][j]=v;v=v*mult%p;}\n }\n bp.resize(N+1);bp[0]=1;\n const I imax=I(((__uint128_t(1)<<127)-1));\n for(int n=0;n<N;++n){if(bp[n]>imax/(b*(2*a+2*b+1))){std::cerr<<"Arithmetic bound exceeded\\n";return 1;}bp[n+1]=bp[n]*b;}\n counts.assign(N+1,0);std::array<int,20> roots{};std::array<U,20> masks; masks.fill(1);\n dfs(0,0,1,roots,masks);\n std::cout<<"{\\"status\\":\\"complete\\",\\"a\\":"<<a<<",\\"b\\":"<<b<<",\\"length\\":"<<N<<",\\"counts\\":[";\n for(int n=0;n<=N;++n){if(n)std::cout<<",";std::cout<<counts[n];}\n std::cout<<"],\\"nodes\\":"<<visits<<",\\"primes\\":[";\n for(int j=0;j<J;++j){if(j)std::cout<<",";std::cout<<ps[j];}\n std::cout<<"]}\\n";\n}\n'

SOURCE_INITIAL = '// Recalculation using initial-fraction intervals and polynomial roots.\n// Each interval endpoint is represented with common denominator a^N.\n#include <algorithm>\n#include <array>\n#include <cstdint>\n#include <cstdlib>\n#include <iostream>\n#include <numeric>\n#include <vector>\nusing I=__int128_t; using U=uint64_t;\nint a,b,N,J;std::vector<int> cs,ps;std::vector<I> ap,bp;\nstd::vector<std::array<int,20>> inverses;\nstd::array<U,20> full;std::vector<U> counts;U visits=0;\nbool prime(int p){if(p<2)return false;for(int d=2;d*d<=p;++d)if(p%d==0)return false;return true;}\nint powmod(int v,int n,int p){int z=1;while(n){if(n&1)z=z*v%p;v=v*v%p;n>>=1;}return z;}\nvoid dfs(int n,I C,I low,I high,const std::array<U,20>& masks){\n if(++visits>1000000000ULL){std::cerr<<"INCONCLUSIVE: node cap\\n";std::exit(2);}++counts[n];if(n==N)return;\n for(int c:cs){\n  I Cnext=I(a)*C+I(c)*bp[n];\n  I l=std::max(low,Cnext*ap[N-n-1]);\n  I h=std::min(high,(Cnext+bp[n+1])*ap[N-n-1]);\n  if(l>=h)continue;\n  bool ok=true;std::array<U,20> mm{};\n  for(int j=0;j<J;++j){int p=ps[j];int residue=int(Cnext%p);if(residue<0)residue+=p;\n   int root=(p-residue)*inverses[n+1][j]%p;\n   mm[j]=masks[j]|(U(1)<<root);if(mm[j]==full[j]){ok=false;break;}\n  }\n  if(ok)dfs(n+1,Cnext,l,h,mm);\n }\n}\nint main(int argc,char**argv){\n if(argc!=4)return 1;a=std::atoi(argv[1]);b=std::atoi(argv[2]);N=std::atoi(argv[3]);\n if(!(a>b&&b>=2&&std::gcd(a,b)==1&&a<=50&&N>=1&&N<=40))return 1;\n const I imax=I(((__uint128_t(1)<<127)-1));ap.resize(N+1);bp.resize(N+1);ap[0]=bp[0]=1;\n for(int n=0;n<N;++n){if(ap[n]>imax/(a*(4*a+4*b+4))){std::cerr<<"Arithmetic bound exceeded\\n";return 1;}ap[n+1]=ap[n]*a;bp[n+1]=bp[n]*b;}\n for(int c=1-b;c<a;++c)if(std::gcd(std::abs(c),a*b)==1&&(c-(b-a))%2==0)cs.push_back(c);\n for(int p=3;p<=N+1;++p)if(prime(p)&&a*b%p)ps.push_back(p);J=ps.size();if(J>20)return 1;\n inverses.resize(N+1);for(int j=0;j<J;++j){int p=ps[j];full[j]=(U(1)<<p)-1;int inv=powmod(a,p-2,p),v=1;\n  for(int n=0;n<=N;++n){inverses[n][j]=v;v=v*inv%p;}}\n counts.assign(N+1,0);std::array<U,20> masks;masks.fill(1);dfs(0,0,0,ap[N],masks);\n std::cout<<"{\\"status\\":\\"complete\\",\\"a\\":"<<a<<",\\"b\\":"<<b<<",\\"length\\":"<<N<<",\\"counts\\":[";\n for(int n=0;n<=N;++n){if(n)std::cout<<",";std::cout<<counts[n];}std::cout<<"],\\"nodes\\":"<<visits<<"}\\n";\n}\n'

REFERENCE = {'status': 'all_checks_passed', 'digit_seed_cases': 109134, 'cases': [{'a': 9, 'b': 7, 'block_length': 18, 'word_count': 18035747, 'counts': [1, 5, 19, 67, 199, 530, 1315, 3130, 7250, 16511, 37155, 82942, 183838, 404586, 883163, 1909362, 4083475, 8631875, 18035747], 'constant': 13, 'exponent': 0.47700804396896485, 'exact_constant_inequalities': True, 'complete_count_agreement': True, 'small_fraction_recount': True}, {'a': 6, 'b': 5, 'block_length': 40, 'word_count': 3955763, 'counts': [1, 2, 4, 8, 15, 28, 50, 79, 124, 191, 285, 417, 601, 864, 1233, 1757, 2493, 3522, 4950, 6965, 9717, 13582, 18786, 26085, 35937, 49661, 67971, 93166, 126734, 172576, 233228, 315696, 423604, 568869, 757642, 1010562, 1335866, 1766366, 2315828, 3038864, 3955763], 'constant': 10, 'exponent': 0.23596256717285963, 'exact_constant_inequalities': True, 'complete_count_agreement': True, 'small_fraction_recount': True}], 'prime_prefix': {'L': 9, 'D': 210, 'P': 1042408919, 'a': 9927705, 'b': 9927703, 't': 1654617, 'xi': '2084817839/2', 'primes': [1042408919, 1042409129, 1042409339, 1042409549, 1042409759, 1042409969, 1042410179, 1042410389, 1042410599]}, 'next_composite': 1042410809, 'scope': 'Finite exact counts and formulas; no total-termination proof; no Lean verification.'}

def run_counter(source: str, a: int, b: int, length: int, folder: Path,
                name: str, compiler: str) -> dict:
    cpp, executable = folder/(name+'.cpp'), folder/name
    cpp.write_text(source)
    subprocess.run([compiler, '-O3', '-std=c++17', str(cpp), '-o', str(executable)],
                   check=True, capture_output=True, text=True)
    process = subprocess.run([str(executable),str(a),str(b),str(length)],
                             check=True,capture_output=True,text=True)
    data=json.loads(process.stdout)
    check(data.get('status')=='complete','counter did not complete')
    return data

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick',action='store_true')
    parser.add_argument('--output',type=Path,default=Path('sieve_replay_results.json'))
    args=parser.parse_args()
    results=[]
    compiler=shutil.which('g++')
    if not args.quick and compiler is None:
        raise SystemExit('Full replay requires GNU g++. No full-count claim was established.')
    with tempfile.TemporaryDirectory(prefix='prime_sieve_') as tmp:
        for case in REFERENCE['cases']:
            a,b,length=(case[k] for k in ('a','b','block_length'))
            counts=case['counts']
            if not args.quick:
                one=run_counter(SOURCE_CURRENT,a,b,length,Path(tmp),'current',compiler)
                two=run_counter(SOURCE_INITIAL,a,b,length,Path(tmp),'initial',compiler)
                check(one['counts']==two['counts']==counts,'complete count mismatch')
                check(one['nodes']==two['nodes'],'node count mismatch')
            check(small_count(a,b,8)==counts[:9],'small rational recount mismatch')
            A,C=counts[-1],case['constant']
            check(A<=C**length,'s=0 constant inequality failed')
            for s,A_s in enumerate(counts[1:length],1):
                check(A_s**length<=C**length*A**(s-1),'constant inequality failed')
            den=2 if (a,b)==(9,7) else 4
            check(A<b**(length//den),'strict exponent bound failed')
            results.append(dict(a=a,b=b,length=length,counts=counts,constant=C,
                                exponent=log(A)/(length*log(b)),
                                full_recalculation=not args.quick))
    example=REFERENCE['prime_prefix']
    a,b,P,D,L=(example[k] for k in ('a','b','P','D','L'))
    check(gcd(a,b)==1 and a==6*example['t']+3 and b==6*example['t']+1,'base mismatch')
    check(P>a and P>48*L*L*D*D,'AP transplant bound failed')
    x=Fraction(example['xi'])
    for j in range(L):
        q=x.numerator//x.denominator
        check(q==P+j*D and is_prime(q),'prime prefix verification failed')
        x*=Fraction(a,b)
    next_q=x.numerator//x.denominator
    check(next_q==1042410809==11*94764619,'next composite verification failed')
    total=check_bijections()
    result=dict(status='all_checks_passed',full_recalculation=not args.quick,
                digit_seed_cases=total,cases=results,prime_prefix=example,
                next_composite=next_q,
                limitation='No total-termination proof; no new all-coefficient compositeness theorem; no Lean verification.')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status=result['status'],full_recalculation=not args.quick,
                         digit_seed_cases=total,output=str(args.output)),indent=2))

if __name__=='__main__':
    main()
