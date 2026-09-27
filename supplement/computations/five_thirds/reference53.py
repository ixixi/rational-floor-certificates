#!/usr/bin/env python3
"""Literal small-instance reference for the 5/3 word certificate.

Computes SCCs by a Boolean reachability matrix, not DFS-based SCC algorithms.
Checks prime lifts by following every possible nonzero starting residue.
Compares all vertices and all carry words with producer dumps through prime 17.
Standard library only. This reference is deliberately limited to small graphs.
"""
from __future__ import annotations
import argparse
from collections import deque
from dataclasses import dataclass
from math import gcd
from pathlib import Path
import json

Word = tuple[int, ...]
Edge = tuple[int, int, Word]
@dataclass(frozen=True)
class Graph:
    cells: tuple[tuple[int, int], ...]
    edges: tuple[Edge, ...]
    @property
    def n(self) -> int:
        return len(self.cells)

def graph(cells, edges) -> Graph:
    return Graph(tuple(cells), tuple(sorted(set(edges))))

def initial() -> Graph:
    a,b,K=5,3,3
    alphabet=(-2,2,4)
    return graph([(j,j+1) for j in range(K)],
        [(j,k,(c,)) for j in range(K) for k in range(K) for c in alphabet
         if a*j-b*(k+1)<c*K<a*(j+1)-b*k])

def scc_by_reachability(g: Graph) -> list[list[int]]:
    if g.n>5000:
        raise ValueError('This reference is limited to 5,000 vertices.')
    reachable=[1<<u for u in range(g.n)]
    for u,v,_ in g.edges:
        reachable[u] |= 1<<v
    for k in range(g.n):
        target_bit=1<<k
        row=reachable[k]
        for u in range(g.n):
            if reachable[u]&target_bit:
                reachable[u] |= row
    remaining=set(range(g.n));comps=[]
    while remaining:
        root=min(remaining)
        members=[u for u in sorted(remaining)
                 if reachable[root]&(1<<u) and reachable[u]&(1<<root)]
        remaining.difference_update(members);comps.append(members)
    return comps

def periodic(vertices: list[int], edges: list[Edge]) -> bool:
    adj={u:[] for u in vertices}
    for e in edges: adj[e[0]].append(e)
    h={min(vertices):0};todo=deque(h)
    while todo:
        u=todo.popleft()
        for _,v,w in adj[u]:
            if v not in h:
                h[v]=h[u]+len(w);todo.append(v)
    if len(h)!=len(vertices):raise AssertionError('component not reachable')
    d=0
    for u,v,w in edges:d=gcd(d,h[u]+len(w)-h[v])
    if d<=0:raise AssertionError('nonpositive period')
    letters={}
    for u,v,w in edges:
        for i,c in enumerate(w):
            phase=(h[u]+i)%d
            if phase in letters and letters[phase]!=c:return False
            letters[phase]=c
    return True

def simplify(g: Graph) -> Graph:
    comps=scc_by_reachability(g)
    cid={v:i for i,C in enumerate(comps) for v in C}
    inside=[[] for C in comps]
    for e in g.edges:
        if cid[e[0]]==cid[e[1]]:inside[cid[e[0]]].append(e)
    kept=[e for C,E in zip(comps,inside) if E and not periodic(C,E) for e in E]
    adj=[[] for _ in range(g.n)]
    for e in kept:adj[e[0]].append(e)
    anchors=[v for v in range(g.n) if len(adj[v])>=2]
    ids={v:i for i,v in enumerate(anchors)}
    edges=[]
    for u in anchors:
        for _,v,w in adj[u]:
            labels=list(w);seen=set()
            while v not in ids:
                if v in seen or len(adj[v])!=1:raise AssertionError('invalid chain')
                seen.add(v);_,v,next_word=adj[v][0];labels.extend(next_word)
            edges.append((ids[u],ids[v],tuple(labels)))
    return graph([g.cells[u] for u in anchors],edges)

def reverse(g: Graph) -> Graph:
    return graph(g.cells,[(v,u,w[::-1]) for u,v,w in g.edges])

def reduce(g: Graph) -> Graph:
    g=simplify(g)
    for _ in range(10):
        if not g.n:break
        old=g.n
        g=reverse(simplify(reverse(g)))
        g=simplify(g)
        if g.n==old:break
    return g

def lift(g: Graph,p: int) -> Graph:
    inverse=pow(3,-1,p);edges=[]
    for u,v,w in g.edges:
        for q in range(1,p):
            residue=q
            for carry in w:
                residue=((5*residue+carry)*inverse)%p
                if residue==0:break
            else:
                edges.append((u*(p-1)+q-1,v*(p-1)+residue-1,w))
    active=sorted({u for u,_,_ in edges}|{v for _,v,_ in edges})
    ids={v:i for i,v in enumerate(active)}
    return graph([g.cells[v//(p-1)] for v in active],
                 [(ids[u],ids[v],w) for u,v,w in edges])

def read_dump(path: Path) -> Graph:
    with path.open() as f:
        n,m,D=map(int,f.readline().split())
        if D!=3:raise AssertionError('different cell denominator')
        cells=[tuple(map(int,f.readline().split())) for _ in range(n)]
        edges=[]
        for _ in range(m):
            u,v,length,*word=map(int,f.readline().split())
            if len(word)!=length:raise AssertionError('word length')
            edges.append((u,v,tuple(word)))
        if f.read().strip():raise AssertionError('trailing data')
    g=graph(cells,edges)
    if g.n!=n or len(g.edges)!=m:raise AssertionError('duplicate data')
    return g

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compare',type=Path,required=True)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    g=initial();counts=dict(vertices=0,edges=0,letters=0);stages=[]
    for stage,p in enumerate((0,7,11,13,17)):
        if p:g=lift(g,p)
        vin,ein=g.n,len(g.edges)
        for name in ('in','out'):
            if name=='out':g=reduce(g)
            supplied=read_dump(args.compare/f'graph_{stage}_{name}.txt')
            if g!=supplied:raise AssertionError(f'full data mismatch: {stage} {name}')
            counts['vertices']+=g.n;counts['edges']+=len(g.edges)
            counts['letters']+=sum(len(w) for _,_,w in g.edges)
        stages.append(dict(p=p,vin=vin,ein=ein,vout=g.n,eout=len(g.edges)))
    result=dict(status='all_elements_match',compared_graphs=10,**counts,stages=stages)
    text=json.dumps(result,indent=2)
    if args.output:args.output.write_text(text+'\n')
    print(text)
if __name__=='__main__':main()
