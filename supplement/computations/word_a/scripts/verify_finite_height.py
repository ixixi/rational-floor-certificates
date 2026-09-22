"""Reproduce the exact finite-height exclusion for bases 6/5 and 9/7.

Run: python3 verify_finite_height.py --output finite_height_verification.json
Optional: --witnesses complete_witnesses.json

Requirements: Python 3.10+, GNU-compatible C++17 compiler (__int128).
Only standard libraries are used. Both complete counters are embedded here;
no previous project files or external certificate data are required.
The two enumerators use different fractional-interval coordinates and
independent seed-congruence calculations. Small exhaustive Fraction oracles
and separate exact witness checks are also performed.

This does NOT prove unbounded termination or an infinite family theorem.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
from itertools import product
import json
from math import gcd, isqrt
from pathlib import Path
import shutil
import subprocess
import tempfile

SOURCE_A = '// Complete carry-word cover of seeds 0<P<=b^N. All arithmetic is exact.\n// This is a finite-height certificate, NOT a proof for unbounded seeds.\n#include <algorithm>\n#include <array>\n#include <cstdint>\n#include <cstdlib>\n#include <iostream>\n#include <numeric>\n#include <string>\n#include <vector>\nusing I=__int128_t; using U=uint64_t;\nint a,b,N,J; std::vector<int> cs,ps,ainv;\nstd::vector<std::array<int,20>> wt;\nstd::array<U,20> full;\nstd::vector<U> counts;\nstd::vector<I> bp,ap;\nU cap=1000000000ULL, visits=0, even=0, small=0, excluded=0, surviving=0;\nstd::vector<I> survivors,small_seeds;\nbool prime(int x){for(int d=2;d*d<=x;++d)if(x%d==0)return false;return x>=2;}\nint power(int x,int k,int p){int z=1;while(k){if(k&1)z=z*x%p;x=x*x%p;k>>=1;}return z;}\nint mod(I x,int m){int r=int(x%m);return r<0?r+m:r;}\nint inverse(int x,int m){for(int y=1;y<m;y++)if(x*y%m==1)return y;std::abort();}\nstd::string dec(I x){if(x==0)return "0";std::string s;bool neg=x<0;if(neg)x=-x;while(x){s.push_back(char(\'0\'+x%10));x/=10;}if(neg)s+=\'-\';std::reverse(s.begin(),s.end());return s;}\nvoid dfs(int n,I lo,I hi,I seed,I q,const std::array<int,20>& roots,const std::array<U,20>& masks){\n if(++visits>cap){std::cerr<<"INCONCLUSIVE: resource cap reached\\n";std::exit(2);}\n ++counts[n];\n if(n==N){\n  if(seed<=std::max(a,N+1)){small++;small_seeds.push_back(seed);return;}\n  if(seed%2==0){even++;return;}\n  for(int j=0;j<J;j++)if(masks[j]&(U(1)<<mod(seed,ps[j]))){excluded++;return;}\n  surviving++;survivors.push_back(seed);return;\n }\n for(int c:cs){\n  I l=std::max(I(0),I(a)*lo-I(c)*bp[n]);\n  I h=std::min(bp[n+1],I(a)*hi-I(c)*bp[n]);\n  if(l>=h)continue;\n  std::array<int,20> rr{};std::array<U,20> mm{};\n  bool ok=true;\n  for(int j=0;j<J;++j){int p=ps[j];int v=(roots[j]-c*wt[n][j])%p;if(v<0)v+=p;\n   rr[j]=v;mm[j]=masks[j]|(U(1)<<v);\n   if(mm[j]==full[j]){ok=false;break;}\n  }\n  if(!ok)continue;\n  int digit=mod(-I(mod(I(a)*q+c,b))*ainv[n+1],b);\n  I s=seed+bp[n]*digit;\n  I numer=I(a)*(q+ap[n]*digit)+c;\n  if(numer%b!=0){std::cerr<<"lifting error\\n";std::exit(3);}\n  dfs(n+1,l,h,s,numer/b,rr,mm);\n }\n}\nint main(int argc,char**argv){\n if(argc!=4){std::cerr<<"usage: finite_seed_cover a b N\\n";return 1;}\n a=std::atoi(argv[1]);b=std::atoi(argv[2]);N=std::atoi(argv[3]);\n if(!(a>b&&b>=2&&std::gcd(a,b)==1&&N>=1&&N<=40&&a<=12))return 1;\n for(int c=1-b;c<a;++c)if(std::gcd(std::abs(c),a*b)==1&&(c-(b-a))%2==0)cs.push_back(c);\n for(int p=3;p<=N+1;++p)if(prime(p)&&a*b%p)ps.push_back(p);\n J=ps.size();if(J>20)return 1;wt.resize(N);\n for(int j=0;j<J;++j){int p=ps[j];int v=power(a,p-2,p);int mult=b*v%p;\n  full[j]=(U(1)<<p)-1;\n  for(int n=0;n<N;++n){wt[n][j]=v;v=v*mult%p;}\n }\n bp.resize(N+1);ap.resize(N+1);bp[0]=ap[0]=1;\n const I imax=I(((__uint128_t(1)<<127)-1));\n for(int n=0;n<N;++n){if(ap[n]>imax/(a*(4*a+4*b+4))){std::cerr<<"Arithmetic bound exceeded\\n";return 1;}bp[n+1]=bp[n]*b;ap[n+1]=ap[n]*a;}\n ainv.resize(N+1);for(int n=0;n<=N;n++)ainv[n]=inverse(mod(ap[n],b),b);\n counts.assign(N+1,0);std::array<int,20> roots{};std::array<U,20> masks; masks.fill(1);\n dfs(0,0,1,0,0,roots,masks);\n std::sort(survivors.begin(),survivors.end());std::sort(small_seeds.begin(),small_seeds.end());\n std::cout<<"{\\"status\\":\\"complete\\",\\"a\\":"<<a<<",\\"b\\":"<<b<<",\\"N\\":"<<N<<",\\"height\\":\\""<<dec(bp[N])<<"\\",\\"counts\\":[";\n for(int n=0;n<=N;++n){if(n)std::cout<<",";std::cout<<counts[n];}\n std::cout<<"],\\"nodes\\":"<<visits<<",\\"even\\":"<<even<<",\\"small\\":"<<small<<",\\"excluded\\":"<<excluded<<",\\"surviving\\":"<<surviving<<",\\"survivors\\":[";\n for(size_t j=0;j<survivors.size();j++){if(j)std::cout<<",";std::cout<<"\\""<<dec(survivors[j])<<"\\"";}\n std::cout<<"],\\"small_seeds\\":[";\n for(size_t j=0;j<small_seeds.size();j++){if(j)std::cout<<",";std::cout<<"\\""<<dec(small_seeds[j])<<"\\"";}\n std::cout<<"],\\"primes\\":[";for(int j=0;j<J;j++){if(j)std::cout<<",";std::cout<<ps[j];}std::cout<<"]}\\n";\n}\n'

SOURCE_B = '// Independent finite-height enumeration: initial-coordinate intervals and\n// polynomial congruence solved only at the leaves. No seed-lifting code.\n// This checks a bounded-height theorem, not termination for unbounded seeds.\n#include <algorithm>\n#include <array>\n#include <cstdint>\n#include <cstdlib>\n#include <iostream>\n#include <numeric>\n#include <string>\n#include <vector>\nusing I=__int128_t; using U=uint64_t;\nint a,b,N,J;std::vector<int> cs,ps;std::vector<I> ap,bp;\nstd::vector<std::array<int,20>> inverses;\nstd::array<U,20> full;std::vector<U> counts;\nU visits=0,even=0,small=0,excluded=0,surviving=0;\nstd::vector<I> survivors,small_seeds; I invlast,bN;\nbool prime(int p){if(p<2)return false;for(int d=2;d*d<=p;++d)if(p%d==0)return false;return true;}\nint powmod(int v,int n,int p){int z=1;while(n){if(n&1)z=z*v%p;v=v*v%p;n>>=1;}return z;}\nint mod(I v,int p){int z=int(v%p);return z<0?z+p:z;}\nI inverse(I a,I m){I b=m,x=1,y=0;while(b){I q=a/b;I r=a-q*b;a=b;b=r;I t=x-q*y;x=y;y=t;}if(a!=1)std::abort();x%=m;return x<0?x+m:x;}\nstd::string dec(I x){if(!x)return "0";bool neg=x<0;if(neg)x=-x;std::string s;while(x){s.push_back(char(\'0\'+x%10));x/=10;}if(neg)s.push_back(\'-\');std::reverse(s.begin(),s.end());return s;}\nI mulmod(I x,I y,I m){\n x%=m;if(x<0)x+=m;I z=0;\n while(y){if(y&1){z+=x;if(z>=m)z-=m;}y>>=1;x+=x;if(x>=m)x-=m;}\n return z;\n}\nvoid dfs(int n,I C,I low,I high,const std::array<U,20>& masks){\n if(++visits>1000000000ULL){std::cerr<<"INCONCLUSIVE: node cap\\n";std::exit(2);}++counts[n];\n if(n==N){\n  I seed=mulmod(-C,invlast,bN);\n  if(seed<=std::max(a,N+1)){small++;small_seeds.push_back(seed);return;}\n  if(seed%2==0){even++;return;}\n  for(int j=0;j<J;++j)if(masks[j]&(U(1)<<mod(seed,ps[j]))){excluded++;return;}\n  surviving++;survivors.push_back(seed);return;\n }\n for(int c:cs){\n  I Cnext=I(a)*C+I(c)*bp[n];\n  I l=std::max(low,Cnext*ap[N-n-1]);\n  I h=std::min(high,(Cnext+bp[n+1])*ap[N-n-1]);\n  if(l>=h)continue;\n  bool ok=true;std::array<U,20> mm{};\n  for(int j=0;j<J;++j){int p=ps[j];int root=mod(-I(mod(Cnext,p))*inverses[n+1][j],p);\n   mm[j]=masks[j]|(U(1)<<root);if(mm[j]==full[j]){ok=false;break;}\n  }\n  if(ok)dfs(n+1,Cnext,l,h,mm);\n }\n}\nint main(int argc,char**argv){\n if(argc!=4)return 1;a=std::atoi(argv[1]);b=std::atoi(argv[2]);N=std::atoi(argv[3]);\n if(!(a>b&&b>=2&&std::gcd(a,b)==1&&a<=12&&N>=1&&N<=40))return 1;\n const I imax=I(((__uint128_t(1)<<127)-1));ap.resize(N+1);bp.resize(N+1);ap[0]=bp[0]=1;\n for(int n=0;n<N;++n){if(ap[n]>imax/(a*(4*a+4*b+4))){std::cerr<<"Arithmetic bound exceeded\\n";return 1;}ap[n+1]=ap[n]*a;bp[n+1]=bp[n]*b;}\n bN=bp[N];invlast=inverse(ap[N],bp[N]);\n for(int c=1-b;c<a;++c)if(std::gcd(std::abs(c),a*b)==1&&(c-(b-a))%2==0)cs.push_back(c);\n for(int p=3;p<=N+1;++p)if(prime(p)&&a*b%p)ps.push_back(p);J=ps.size();if(J>20)return 1;\n inverses.resize(N+1);for(int j=0;j<J;++j){int p=ps[j];full[j]=(U(1)<<p)-1;int inv=powmod(a,p-2,p),v=1;\n  for(int n=0;n<=N;++n){inverses[n][j]=v;v=v*inv%p;}}\n counts.assign(N+1,0);std::array<U,20> masks;masks.fill(1);dfs(0,0,0,ap[N],masks);\n std::sort(survivors.begin(),survivors.end());std::sort(small_seeds.begin(),small_seeds.end());\n std::cout<<"{\\"status\\":\\"complete\\",\\"a\\":"<<a<<",\\"b\\":"<<b<<",\\"N\\":"<<N<<",\\"height\\":\\""<<dec(bp[N])<<"\\",\\"counts\\":[";\n for(int n=0;n<=N;++n){if(n)std::cout<<",";std::cout<<counts[n];}\n std::cout<<"],\\"nodes\\":"<<visits<<",\\"even\\":"<<even<<",\\"small\\":"<<small<<",\\"excluded\\":"<<excluded<<",\\"surviving\\":"<<surviving<<",\\"survivors\\":[";\n for(size_t j=0;j<survivors.size();j++){if(j)std::cout<<",";std::cout<<"\\""<<dec(survivors[j])<<"\\"";}\n std::cout<<"],\\"small_seeds\\":[";for(size_t j=0;j<small_seeds.size();j++){if(j)std::cout<<",";std::cout<<"\\""<<dec(small_seeds[j])<<"\\"";}\n std::cout<<"],\\"primes\\":[";for(int j=0;j<J;j++){if(j)std::cout<<",";std::cout<<ps[j];}std::cout<<"]}\\n";\n}\n'


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def primes_up_to(limit: int) -> list[int]:
    sieve = bytearray(b'\x01') * (limit + 1)
    if limit >= 1:
        sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p::p] = b'\x00' * ((limit-p*p)//p+1)
    return [p for p in range(2, limit+1) if sieve[p]]


def oracle(a: int, b: int, N: int) -> dict:
    """Independent small-instance oracle: literal products, Fraction, pow inverse."""
    cs = [c for c in range(1-b, a)
          if (c-(b-a)) % 2 == 0 and gcd(c,a*b) == 1]
    ps = [p for p in primes_up_to(N+1) if p != 2 and a*b % p]
    counts, survivors, small_seeds = [], [], []
    even = small = excluded = 0
    for length in range(N+1):
        count = 0
        for word in product(cs, repeat=length):
            C, lo, hi = 0, Fraction(0), Fraction(1)
            masks = [{0} for _ in ps]
            valid = True
            for j,c in enumerate(word):
                C = a*C + b**j*c
                aa, bb = a**(j+1), b**(j+1)
                lo,hi = max(lo,Fraction(C,aa)), min(hi,Fraction(C+bb,aa))
                if lo >= hi:
                    valid = False
                    break
                for mask,p in zip(masks,ps):
                    mask.add((-C*pow(aa,-1,p)) % p)
                    if len(mask)==p:
                        valid = False
                if not valid:
                    break
            if not valid:
                continue
            count += 1
            if length != N:
                continue
            seed = (-C*pow(a**N,-1,b**N)) % b**N
            if seed <= max(a,N+1):
                small += 1
                small_seeds.append(str(seed))
            elif seed % 2 == 0:
                even += 1
            elif any(seed % p in mask for p,mask in zip(ps,masks)):
                excluded += 1
            else:
                survivors.append(str(seed))
        counts.append(count)
    survivors.sort(key=int)
    small_seeds.sort(key=int)
    return dict(status='complete',a=a,b=b,N=N,height=str(b**N),counts=counts,
                nodes=sum(counts),even=even,small=small,excluded=excluded,
                surviving=len(survivors),survivors=survivors,
                small_seeds=small_seeds,primes=ps)


def find_stop(a: int, b: int, seed: int, primes: list[int], cap: int) -> dict:
    """Produce a proper factor or an exact incompatibility; no primality oracle."""
    q,lo,hi,B = seed,0,1,1
    for n in range(cap+1):
        for p in primes:
            if 1<p<q and q%p == 0:
                return dict(seed=str(seed),kind='proper_divisor',step=n,
                            term=str(q),divisor=p,cofactor=str(q//p))
        if n == cap:
            raise RuntimeError(f'INCONCLUSIVE: no witness for seed {seed}')
        if (a,b)==(6,5):
            if q%5 not in (1,4):
                return dict(seed=str(seed),kind='no_prime_successor',step=n+1,
                            previous_term=str(q),remainder=q%5)
            c = -1 if q%5==1 else 1
            nxt = (6*q+c)//5
        elif (a,b)==(9,7):
            nxt = q+2*((q+4)//7)
            c = 7*nxt-9*q
        else:
            raise ValueError('Witness finder supports only the two adopted cases')
        require(b*nxt==a*q+c,'Integer recurrence failure')
        lo,hi,B = max(0,a*lo-c*B),min(b*B,a*hi-c*B),b*B
        if lo>=hi:
            return dict(seed=str(seed),kind='empty_interval',step=n+1,
                        low=str(lo),high=str(hi),denominator=str(B))
        q = nxt
    raise RuntimeError('Unreachable')


def check_stop(a: int, b: int, w: dict) -> None:
    """Check the witness separately using initial-coordinate Fraction intervals."""
    seed = int(w['seed'])
    lo,hi,C,q = Fraction(0),Fraction(1),0,seed
    for n in range(w['step']+1):
        if w['kind']=='proper_divisor' and n==w['step']:
            p,k=int(w['divisor']),int(w['cofactor'])
            require(q==int(w['term']) and q==p*k and p>1 and k>1,
                    'Invalid proper-divisor certificate')
            return
        if n == w['step']:
            raise RuntimeError('Incompatibility witness was not verified')
        if (a,b)==(6,5):
            if q%5 not in (1,4):
                require(w['kind']=='no_prime_successor' and n+1==w['step']
                        and q==int(w['previous_term']) and q%5==w['remainder'],
                        'Unexpected missing successor')
                return
            c=-1 if q%5==1 else 1
            nxt=(6*q+c)//5
        elif (a,b)==(9,7):
            nxt=q+2*((q+4)//7)
            c=7*nxt-9*q
        else:
            raise ValueError('Unsupported base')
        require(b*nxt==a*q+c,'Verifier recurrence failure')
        C=a*C+b**n*c
        lo,hi=max(lo,Fraction(C,a**(n+1))),min(hi,Fraction(C+b**(n+1),a**(n+1)))
        if lo>=hi:
            require(w['kind']=='empty_interval' and n+1==w['step'],
                    'Unexpected empty interval')
            return
        q=nxt
    raise RuntimeError('Witness verifier did not return')


def check_periodic_bound() -> int:
    """Check the finite-period divisibility formula on exact floor orbits."""
    tested=0
    for a in range(3,13):
        for b in range(2,a):
            if gcd(a,b)!=1:
                continue
            r=Fraction(a,b)
            for denominator in (1,2,5,7):
                for numerator in range(1,denominator+1):
                    xi=Fraction(a+11)+Fraction(numerator,denominator)
                    xx=[xi*r**n for n in range(25)]
                    qq=[x.numerator//x.denominator for x in xx]
                    cc=[b*qq[n+1]-a*qq[n] for n in range(24)]
                    for start in range(12):
                        for period in range(1,5):
                            for length in range(period,13-start):
                                if any(cc[start+i]!=cc[start+i-period]
                                       for i in range(period,length)):
                                    continue
                                difference=qq[start+period]-qq[start]
                                require(difference>0,'Nonpositive test difference')
                                require(difference%b**(length-period)==0,
                                        'Finite-period divisibility failure')
                                require(Fraction(difference)<r**period*(qq[start]+1)-qq[start],
                                        'Finite-period height bound failure')
                                tested+=1
    return tested


def compile_counter(source: str, stem: str, directory: Path, compiler: str) -> Path:
    cpp=directory/(stem+'.cpp')
    executable=directory/stem
    cpp.write_text(source,encoding='utf-8')
    result=subprocess.run([compiler,'-O3','-std=c++17',str(cpp),'-o',str(executable)],
                          capture_output=True,text=True,timeout=60)
    if result.returncode:
        raise RuntimeError('C++ compilation failed:\n'+result.stderr)
    return executable


def run_counter(executable: Path, a: int,b: int,N: int) -> dict:
    run=subprocess.run([str(executable),str(a),str(b),str(N)],
                       capture_output=True,text=True,timeout=180)
    if run.returncode:
        raise RuntimeError('Enumeration did not complete:\n'+run.stderr)
    result=json.loads(run.stdout)
    require(result.get('status')=='complete','Enumeration not complete')
    require(result['nodes']==sum(result['counts']),'Node/count mismatch')
    require(result['counts'][-1]==sum(result[k] for k in ('even','small','excluded','surviving')),
            'Leaf partition mismatch')
    return result


def digest(obj: object) -> str:
    return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('finite_height_verification.json'))
    parser.add_argument('--witnesses',type=Path,help='Optional complete survivor/stop witness output')
    parser.add_argument('--compiler',default='g++')
    args=parser.parse_args()
    compiler=shutil.which(args.compiler)
    if compiler is None:
        raise SystemExit('GNU-compatible C++17 compiler with __int128 support is required.')
    tiny_cases=[(3,2,5),(4,3,5),(5,3,5),(6,5,6),(7,5,5),(9,7,5)]
    adopted=[(6,5,40),(9,7,18)]
    report=dict(status='running',formal_verification=False,
                scope='Finite-height prime-prefix exclusion only; no unbounded termination claim',
                small_cases=[],cases=[])
    all_witnesses={}
    with tempfile.TemporaryDirectory(prefix='finite-height-') as temp:
        directory=Path(temp)
        exeA=compile_counter(SOURCE_A,'counter_a',directory,compiler)
        exeB=compile_counter(SOURCE_B,'counter_b',directory,compiler)
        for a,b,N in tiny_cases:
            x=run_counter(exeA,a,b,N);y=run_counter(exeB,a,b,N);z=oracle(a,b,N)
            require(x==y==z,f'Small exhaustive oracle disagreement: {(a,b,N)}')
            report['small_cases'].append(dict(a=a,b=b,N=N,all_fields_agree=True,
                                             words=x['counts'][-1]))
        trial_primes=primes_up_to(10000)
        for a,b,N in adopted:
            x=run_counter(exeA,a,b,N);y=run_counter(exeB,a,b,N)
            require(x==y,f'Full recount disagreement: {(a,b,N)}')
            ww=[find_stop(a,b,int(s),trial_primes,N) for s in x['survivors']]
            small_primes=[p for p in primes_up_to(max(a,N+1)) if p>a]
            ws=[find_stop(a,b,p,trial_primes,N) for p in small_primes]
            for w in ww+ws:
                check_stop(a,b,w)
            summary={k:v for k,v in x.items() if k not in ('survivors','small_seeds')}
            summary.update(all_fields_agree=True,survivor_digest=digest(x['survivors']),
                           witness_digest=digest(ww),survivor_witnesses_checked=len(ww),
                           maximum_survivor_stop_step=max([w['step'] for w in ww],default=0),
                           maximum_survivor_divisor=max([w.get('divisor',0) for w in ww],default=0),
                           survivor_step_counts=dict(Counter(w['step'] for w in ww)),
                           small_prime_witnesses=ws,
                           conclusion=f'No all-prime prefix of {N+1} terms with a<floor(xi)<=b^{N}')
            report['cases'].append(summary)
            all_witnesses[f'{a}/{b}']=dict(survivors=x['survivors'],witnesses=ww,small=ws)
            print(f'{a}/{b}: {x["counts"][-1]} words; {len(ww)} survivors all rejected; height={b**N}')
    report['finite_period_checks']=check_periodic_bound()
    report['status']='all_checks_passed'
    args.output.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    if args.witnesses:
        args.witnesses.write_text(json.dumps(all_witnesses,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(f'Verified report: {args.output}')
    print('The result is finite-height only. It is not an infinite-family compositeness theorem.')

if __name__=='__main__':
    main()
