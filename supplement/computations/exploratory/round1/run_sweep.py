#!/usr/bin/env python3
"""Repeat the bounded inverse search. Compile search.cpp to ./search first.
Each unfinished resource-limited case is explicitly inconclusive.
"""
import argparse, concurrent.futures, json, math, pathlib, subprocess


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--max-a',type=int,default=80)
    p.add_argument('--cells',type=int,default=4)
    p.add_argument('--edge-cap',type=int,default=100000)
    p.add_argument('--timeout',type=float,default=4)
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--output',type=pathlib.Path,default=pathlib.Path('sweep_recomputed.jsonl'))
    args=p.parse_args()
    executable=pathlib.Path(__file__).resolve().parent/'search'
    if not executable.exists():
        p.error('Compile first: g++ -O2 -std=c++17 search.cpp -o search')
    primes='3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67'
    def run(pair):
        a,b=pair
        try:
            result=subprocess.run([str(executable),str(a),str(b),str(args.cells),primes,str(args.edge_cap)],
                                  capture_output=True,text=True,timeout=args.timeout,check=True)
            return json.loads(result.stdout)
        except (subprocess.TimeoutExpired,subprocess.CalledProcessError,json.JSONDecodeError) as exc:
            return dict(a=a,b=b,K=args.cells,status='inconclusive',reason=type(exc).__name__)
    jobs=[(a,b) for a in range(3,args.max_a+1) for b in range(2,a) if math.gcd(a,b)==1]
    with args.output.open('w',encoding='utf-8') as out,concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        for result in pool.map(run,jobs):
            out.write(json.dumps(result)+'\n');out.flush()
            if result['status']=='success':
                print(f"success: {result['a']}/{result['b']}",flush=True)
    print(f'Completed {len(jobs)} bounded cases; data: {args.output}')


if __name__=='__main__':
    main()
