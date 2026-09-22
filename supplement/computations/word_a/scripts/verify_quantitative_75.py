"""Reproduce the quantitative 7/5 prime-tail certificate.

Run: python3 verify_quantitative_75.py --output quantitative_75_verification.json
Requires Python 3.10+ and a GNU-compatible C++17 compiler with __int128.
Uses only standard libraries. Both complete C++ graph implementations are
embedded. Their full scientific arrays are compared, not merely hashes.
A separate Python checker disregards their exported edge lists and enumerates
every legal edge to verify block ranks, cyclic-visit ranks, and phases.
No prior project files or external certificates are required.

This proves a logarithmic waiting-time bound for 7/5. It does not prove an
infinite family of distinct rational bases and is not a Lean formalization.
"""
from __future__ import annotations
import argparse
from array import array
import filecmp
from fractions import Fraction
import hashlib
import json
from math import gcd
from pathlib import Path
import shutil
import struct
import subprocess
import tempfile

SOURCE_A = '// Experimental implementation used for the selected C++ runs.\n// Not a formal checker. Uses signed 64-bit arithmetic: do not extrapolate\n// beyond the recorded input sizes without adding overflow checks.\n// Compile: g++ -O3 -std=c++17 experimental_graph.cpp -o experimental_graph\n// Full final graph: ./experimental_graph 7 5 2048 4290\n// Mixed: ./experimental_graph 7 5 32 2 3 5 11 13 -4 -4 -4\n// Exact labelled-graph experiment. No floating point in edge tests.\n#include <algorithm>\n#include <array>\n#include <chrono>\n#include <cstdint>\n#include <cstdlib>\n#include <fstream>\n#include <iostream>\n#include <numeric>\n#include <queue>\n#include <stdexcept>\n#include <unordered_map>\n#include <vector>\nusing namespace std;\nusing I=long long;\nI mod(I a,I b){I z=a%b;return z<0?z+b:z;}\nI fl(I a,I b){return (a-mod(a,b))/b;}\nI inv(I a,I m){I b=m,u=1,v=0;while(b){I t=a/b; a-=t*b;swap(a,b);u-=t*v;swap(u,v);}if(a!=1)throw runtime_error("inverse");return mod(u,m);}\nstruct Ed{int u,v,e;};\nstruct Hash{size_t operator()(uint64_t x)const{x+=0x9e3779b97f4a7c15ULL;x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;x=(x^(x>>27))*0x94d049bb133111ebULL;return x^(x>>31);}};\nvector<I> stage(int a,int b,I M,int K,const vector<I>&W){\n int n=W.size();if(!n)return{};\n unordered_map<I,int,Hash> ids;ids.reserve(n*1.4);\n for(int i=0;i<n;i++)ids[W[i]]=i;\n I g=gcd((I)b,M),md=M/g,iv=(md==1?0:inv(b/g,md));\n vector<Ed> es;es.reserve(n*3);\n vector<int> cnt(n+1),rcnt(n+1);\n for(int u=0;u<n;u++){\n  I q=W[u]/K;int j=W[u]%K;\n  for(int e=1-b;e<a;e++){\n   if((e-(b-a))%2 != 0 || gcd((I)e,(I)a*b)!=1)continue;\n   I t=(I)a*q+e;if(t%g)continue;\n   int lo=max((I)0,fl((I)a*j-(I)e*K,b));\n   int hi=min((I)K-1,fl((I)a*(j+1)-(I)e*K-1,b));\n   if(lo>hi)continue;\n   I z0=(I)(((__int128)(t/g)*iv%md+md)%md);\n   for(I l=0;l<g;l++){\n    I z=z0+l*md;\n    for(int k=lo;k<=hi;k++){\n     auto it=ids.find(z*K+k);if(it==ids.end())continue;\n     int v=it->second;es.push_back({u,v,e});cnt[u+1]++;rcnt[v+1]++;\n    }\n   }\n  }\n }\n ids.clear();ids.rehash(0);\n partial_sum(cnt.begin(),cnt.end(),cnt.begin());partial_sum(rcnt.begin(),rcnt.end(),rcnt.begin());\n vector<int> adj(es.size()),rev(es.size()),ct=cnt,rt=rcnt;\n for(auto e:es){adj[ct[e.u]++]=e.v;rev[rt[e.v]++]=e.u;}\n ct.clear();ct.shrink_to_fit();rt.clear();rt.shrink_to_fit();\n vector<unsigned char> seen(n);vector<int> order;order.reserve(n);\n vector<pair<int,int>> stack;\n for(int root=0;root<n;root++)if(!seen[root]){\n  stack.push_back({root,cnt[root]});seen[root]=1;\n  while(!stack.empty()){\n   auto &p=stack.back();int u=p.first;\n   if(p.second<cnt[u+1]){int v=adj[p.second++];if(!seen[v]){seen[v]=1;stack.push_back({v,cnt[v]});}}\n   else{order.push_back(u);stack.pop_back();}\n  }\n }\n vector<int> comp(n,-1),sizes,roots,st;\n for(auto it=order.rbegin();it!=order.rend();++it){\n  int root=*it;if(comp[root]>=0)continue;\n  int c=sizes.size(),size=0;roots.push_back(root);comp[root]=c;st.push_back(root);\n  while(!st.empty()){\n   int u=st.back();st.pop_back();size++;\n   for(int k=rcnt[u];k<rcnt[u+1];k++){int v=rev[k];if(comp[v]<0){comp[v]=c;st.push_back(v);}}\n  }\n  sizes.push_back(size);\n }\n rev.clear();rev.shrink_to_fit();rcnt.clear();rcnt.shrink_to_fit();\n int nc=sizes.size();\n for(int u=0;u<n;u++)if(W[u]<W[roots[comp[u]]])roots[comp[u]]=u;\n vector<int> h(n,-1),ds(nc),nies(nc),que;\n for(int c=0;c<nc;c++){\n  que.clear();que.push_back(roots[c]);h[roots[c]]=0;\n  for(size_t t=0;t<que.size();t++){\n   int u=que[t];\n   for(int k=cnt[u];k<cnt[u+1];k++){int v=adj[k];if(comp[v]==c&&h[v]<0){h[v]=h[u]+1;que.push_back(v);}}\n  }\n }\n for(auto e:es)if(comp[e.u]==comp[e.v]){int c=comp[e.u];nies[c]++;ds[c]=gcd(ds[c],abs(h[e.u]+1-h[e.v]));}\n vector<int> ofs(nc+1);int cyc=0;\n for(int c=0;c<nc;c++){if(nies[c]){if(!ds[c])throw runtime_error("d=0");cyc++;}ofs[c+1]=ofs[c]+ds[c];}\n vector<int> lab(ofs.back(),1000000000);vector<unsigned char> bad(nc);\n for(auto e:es)if(comp[e.u]==comp[e.v]){int c=comp[e.u],s=ofs[c]+h[e.u]%ds[c];if(lab[s]==1000000000)lab[s]=e.e;else if(lab[s]!=e.e)bad[c]=1;}\n\n // Condensation DAG path statistics, counting parallel interblock edges.\n vector<vector<int>> dag(nc);vector<int> indeg(nc),pathlen(nc,1),pathcyc(nc);\n int maxd=0;for(int c=0;c<nc;c++){pathcyc[c]=nies[c]>0;maxd=max(maxd,ds[c]);}\n for(auto e:es)if(comp[e.u]!=comp[e.v]){dag[comp[e.u]].push_back(comp[e.v]);indeg[comp[e.v]]++;}\n queue<int> ready;for(int c=0;c<nc;c++)if(!indeg[c])ready.push(c);\n int maxpath=0,maxcycpath=0,ndone=0;\n while(!ready.empty()){int c=ready.front();ready.pop();ndone++;maxpath=max(maxpath,pathlen[c]);maxcycpath=max(maxcycpath,pathcyc[c]);\n  for(int d:dag[c]){pathlen[d]=max(pathlen[d],pathlen[c]+1);pathcyc[d]=max(pathcyc[d],pathcyc[c]+(nies[d]>0));if(--indeg[d]==0)ready.push(d);}}\n if(ndone!=nc)throw runtime_error("cyclic condensation");\n cerr<<"PATHSTAT "<<maxpath<<" "<<maxcycpath<<" "<<maxd<<"\\n";\n\n // Canonical exact scientific arrays for independent bytewise comparison.\n string prefix="/mnt/data/continued_research/graphA";\n vector<array<int32_t,3>> ce;ce.reserve(es.size());\n for(auto e:es)ce.push_back({int32_t(W[e.u]),int32_t(W[e.v]),int32_t(e.e)});\n sort(ce.begin(),ce.end());ofstream fe(prefix+"_edges.bin",ios::binary);\n fe.write(reinterpret_cast<const char*>(ce.data()),ce.size()*sizeof(ce[0]));\n vector<array<int32_t,4>> cv;cv.reserve(n);\n for(int u=0;u<n;u++)cv.push_back({int32_t(W[u]),int32_t(W[roots[comp[u]]]),h[u],ds[comp[u]]});\n sort(cv.begin(),cv.end());ofstream fv(prefix+"_vertices.bin",ios::binary);\n fv.write(reinterpret_cast<const char*>(cv.data()),cv.size()*sizeof(cv[0]));\n vector<array<int32_t,7>> cm;cm.reserve(nc);\n for(int c=0;c<nc;c++)cm.push_back({int32_t(W[roots[c]]),sizes[c],nies[c],ds[c],int(!bad[c]&&nies[c]>0),pathlen[c],pathcyc[c]});\n sort(cm.begin(),cm.end());ofstream fm(prefix+"_components.bin",ios::binary);\n fm.write(reinterpret_cast<const char*>(cm.data()),cm.size()*sizeof(cm[0]));\n vector<I>U;int cert=0;\n for(int c=0;c<nc;c++)if(nies[c]&&!bad[c])cert++;\n for(int u=0;u<n;u++)if(bad[comp[u]])U.push_back(W[u]);\n cout<<"{\\"a\\":"<<a<<",\\"b\\":"<<b<<",\\"M\\":"<<M<<",\\"K\\":"<<K<<",\\"V\\":"<<n<<",\\"E\\":"<<es.size()<<",\\"SCC\\":"<<nc<<",\\"cyclic\\":"<<cyc<<",\\"cert\\":"<<cert<<",\\"U\\":"<<U.size()<<",\\"failed\\":[";\n bool first=true;for(int c=0;c<nc;c++)if(bad[c]){if(!first)cout<<",";first=false;cout<<"["<<sizes[c]<<","<<nies[c]<<","<<ds[c]<<"]";}\n cout<<"]}"<<endl;\n return U;\n}\nint main(int argc,char**argv){\n if(argc<4){cerr<<"usage: lift a b K [prime or -refinement_factor ...]"<<endl;return 1;}\n int a=atoi(argv[1]),b=atoi(argv[2]),K=atoi(argv[3]);I M=1;vector<I> W;\n for(int j=0;j<K;j++)W.push_back(j);\n for(int t=4;t<argc;t++){\n  int p=atoi(argv[t]);vector<I> next;\n  if(p>0){\n   if(W.size()*(size_t)p>2200000){cout<<"{\\"status\\":\\"cap\\",\\"next_multiplier\\":"<<p<<",\\"U\\":"<<W.size()<<"}"<<endl;break;}\n   next.reserve(W.size()*(p-1));\n   for(I key:W){I q=key/K;int j=key%K;for(int l=0;l<p;l++){I z=q+M*l;if(gcd(z,M*p)==1)next.push_back(z*K+j);}}\n   M*=p;\n  }else{\n   int f=-p;if(W.size()*(size_t)f>2200000){cout<<"{\\"status\\":\\"cap\\"}"<<endl;break;}\n   next.reserve(W.size()*f);\n   for(I key:W){I q=key/K;int j=key%K;for(int l=0;l<f;l++)next.push_back(q*(K*f)+f*j+l);}\n   K*=f;\n  }\n  W.clear();W.shrink_to_fit();W=stage(a,b,M,K,next);\n  if(W.empty())break;\n }\n ofstream o("/mnt/data/continued_research/last_states.bin",ios::binary);\n o.write((char*)&M,sizeof(M));o.write((char*)&K,sizeof(K));I len=W.size();o.write((char*)&len,sizeof(len));o.write((char*)W.data(),len*sizeof(I));\n}\n'

SOURCE_B = '// Independent check of the complete 7/5 prime-tail graph at M=429, K=2048.\n// Direct strict inequalities; iterative Tarjan SCCs; all-edge phase verification.\n#include <algorithm>\n#include <array>\n#include <cstdint>\n#include <fstream>\n#include <iostream>\n#include <numeric>\n#include <queue>\n#include <stdexcept>\n#include <string>\n#include <vector>\nusing namespace std;\nstruct Edge{int v,c;};\nstruct Frame{int u;size_t next;};\nint main(){\n const int a=7,b=5,M=429,K=2048;\n vector<int> residues,ri(M,-1),cs;\n for(int q=0;q<M;q++)if(gcd(q,M)==1){ri[q]=residues.size();residues.push_back(q);}\n for(int c=1-b;c<a;c++)if((c-(b-a))%2==0&&gcd(abs(c),a*b)==1)cs.push_back(c);\n int n=residues.size()*K,J=cs.size(),inverse=0;\n for(int u=1;u<M;u++)if(b*u%M==1){inverse=u;break;}\n if(!inverse)throw runtime_error("inverse");\n vector<vector<int>> targets(K*J);\n for(int j=0;j<K;j++)for(int ci=0;ci<J;ci++)for(int k=0;k<K;k++){\n  int c=cs[ci];if(a*j-b*(k+1)<c*K&&c*K<a*(j+1)-b*k)targets[j*J+ci].push_back(k);\n }\n vector<vector<Edge>> out(n);size_t nedges=0;\n for(int qi=0;qi<(int)residues.size();qi++)for(int j=0;j<K;j++){\n  int q=residues[qi],u=qi*K+j;\n  for(int ci=0;ci<J;ci++){\n   int z=((a*q+cs[ci])*inverse%M+M)%M;if(ri[z]<0)continue;\n   for(int k:targets[j*J+ci]){out[u].push_back({ri[z]*K+k,cs[ci]});nedges++;}\n  }\n }\n vector<int> index(n,-1),low(n),owner(n,-1),stack,roots,sizes;\n vector<unsigned char> active(n);vector<Frame> calls;int clock=0;\n auto visit=[&](int u){index[u]=low[u]=clock++;active[u]=1;stack.push_back(u);calls.push_back({u,0});};\n for(int root=0;root<n;root++)if(index[root]<0){\n  visit(root);\n  while(!calls.empty()){\n   Frame &f=calls.back();int u=f.u;\n   if(f.next<out[u].size()){\n    int v=out[u][f.next++].v;\n    if(index[v]<0){visit(v);continue;}\n    if(active[v])low[u]=min(low[u],index[v]);\n   }else{\n    calls.pop_back();\n    if(low[u]==index[u]){\n     int c=sizes.size(),size=0,r=u;\n     while(true){int v=stack.back();stack.pop_back();active[v]=0;owner[v]=c;size++;r=min(r,v);if(v==u)break;}\n     sizes.push_back(size);roots.push_back(r);\n    }\n    if(!calls.empty())low[calls.back().u]=min(low[calls.back().u],low[u]);\n   }\n  }\n }\n int nc=sizes.size();vector<int> h(n,-1),period(nc),ie(nc);\n for(int c=0;c<nc;c++){\n  queue<int> todo;h[roots[c]]=0;todo.push(roots[c]);int reached=0;\n  while(!todo.empty()){\n   int u=todo.front();todo.pop();reached++;\n   for(auto e:out[u])if(owner[e.v]==c&&h[e.v]<0){h[e.v]=h[u]+1;todo.push(e.v);}\n  }\n  if(reached!=sizes[c])throw runtime_error("SCC reachability mismatch");\n }\n for(int u=0;u<n;u++)for(auto e:out[u])if(owner[u]==owner[e.v]){\n  int c=owner[u];ie[c]++;period[c]=gcd(period[c],abs(h[u]+1-h[e.v]));\n }\n vector<vector<int>> labels(nc),dag(nc);vector<int> indeg(nc),pathlen(nc,1),pathcyc(nc);vector<unsigned char> bad(nc);\n int cyclic=0,certified=0,maxperiod=0;\n for(int c=0;c<nc;c++){\n  if(ie[c]){if(!period[c])throw runtime_error("zero period");cyclic++;pathcyc[c]=1;}\n  labels[c].assign(period[c],1000);maxperiod=max(maxperiod,period[c]);\n }\n for(int u=0;u<n;u++)for(auto e:out[u]){\n  int c=owner[u],d=owner[e.v];\n  if(c==d){int phase=h[u]%period[c];if(labels[c][phase]==1000)labels[c][phase]=e.c;else if(labels[c][phase]!=e.c)bad[c]=1;}\n  else{dag[c].push_back(d);indeg[d]++;}\n }\n for(int c=0;c<nc;c++)if(ie[c]&&!bad[c])certified++;\n queue<int> ready;for(int c=0;c<nc;c++)if(!indeg[c])ready.push(c);\n int done=0,maxpath=0,maxcycpath=0;\n while(!ready.empty()){\n  int c=ready.front();ready.pop();done++;maxpath=max(maxpath,pathlen[c]);maxcycpath=max(maxcycpath,pathcyc[c]);\n  for(int d:dag[c]){pathlen[d]=max(pathlen[d],pathlen[c]+1);pathcyc[d]=max(pathcyc[d],pathcyc[c]+(ie[d]>0));if(--indeg[d]==0)ready.push(d);}\n }\n if(done!=nc)throw runtime_error("Condensation not acyclic");\n // Check the path bounds as inequalities on every edge, not just the final counts.\n for(int c=0;c<nc;c++){\n  if(pathlen[c]<1||pathcyc[c]<(ie[c]>0))throw runtime_error("Path initialization");\n  for(int d:dag[c])if(pathlen[d]<pathlen[c]+1||pathcyc[d]<pathcyc[c]+(ie[d]>0))throw runtime_error("Path inequality");\n }\n auto key=[&](int u){return residues[u/K]*K+u%K;};\n vector<array<int32_t,3>> ce;ce.reserve(nedges);\n for(int u=0;u<n;u++)for(auto e:out[u])ce.push_back({key(u),key(e.v),e.c});\n sort(ce.begin(),ce.end());string prefix="/mnt/data/continued_research/graphB";\n ofstream fe(prefix+"_edges.bin",ios::binary);fe.write(reinterpret_cast<const char*>(ce.data()),ce.size()*sizeof(ce[0]));\n vector<array<int32_t,4>> cv;cv.reserve(n);\n for(int u=0;u<n;u++)cv.push_back({key(u),key(roots[owner[u]]),h[u],period[owner[u]]});\n sort(cv.begin(),cv.end());ofstream fv(prefix+"_vertices.bin",ios::binary);fv.write(reinterpret_cast<const char*>(cv.data()),cv.size()*sizeof(cv[0]));\n vector<array<int32_t,7>> cm;cm.reserve(nc);\n for(int c=0;c<nc;c++)cm.push_back({key(roots[c]),sizes[c],ie[c],period[c],int(ie[c]>0&&!bad[c]),pathlen[c],pathcyc[c]});\n sort(cm.begin(),cm.end());ofstream fm(prefix+"_components.bin",ios::binary);fm.write(reinterpret_cast<const char*>(cm.data()),cm.size()*sizeof(cm[0]));\n cout<<"{\\"a\\":7,\\"b\\":5,\\"M\\":429,\\"K\\":2048,\\"V\\":"<<n<<",\\"E\\":"<<nedges<<",\\"SCC\\":"<<nc<<",\\"cyclic\\":"<<cyclic<<",\\"cert\\":"<<certified<<",\\"max_component_path\\":"<<maxpath<<",\\"max_cyclic_path\\":"<<maxcycpath<<",\\"max_period\\":"<<maxperiod<<"}\\n";\n}\n'


def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)


def compile_one(source: str, name: str, folder: Path, compiler: str) -> Path:
    cpp=folder/(name+'.cpp');exe=folder/name
    cpp.write_text(source,encoding='utf-8')
    result=subprocess.run([compiler,'-O3','-std=c++17',str(cpp),'-o',str(exe)],
                          capture_output=True,text=True,timeout=60)
    require(result.returncode==0,'Compilation failed:\n'+result.stderr)
    return exe


def records(path: Path, size: int):
    data=path.read_bytes()
    require(len(data)%(4*size)==0,'Malformed binary array')
    yield from struct.iter_unpack('='+'i'*size,data)


def check_certificate(prefix: Path) -> dict:
    """Ignore the exported edge list. Enumerate every legal edge anew in Python."""
    a,b,M,K=7,5,429,2048
    space=M*K
    require(array('i').itemsize==4,'This checker requires 32-bit array ints')
    owner=array('i',[-1])*space
    distance=array('i',[0])*space
    period=array('i',[0])*space
    rank=array('i',[0])*space
    cycle_count=array('i',[0])*space
    declared_size=array('i',[0])*space
    actual_size=array('i',[0])*space
    declared_internal=array('i',[0])*space
    actual_internal=array('i',[0])*space
    cyc=bytearray(space)
    nblocks=0
    for root,size,internal,d,cert,r,c in records(Path(str(prefix)+'_components.bin'),7):
        require(0<=root<space and rank[root]==0,'Invalid/duplicate block root')
        require(size>0 and internal>=0 and 1<=r<=65 and 0<=c<=6,'Block bounds')
        iscyclic=internal>0
        require(cert==int(iscyclic),'Uncertified cyclic block')
        require((1<=d<=13) if iscyclic else d==0,'Period bounds')
        require(c>=int(iscyclic),'Cycle-rank initial condition')
        rank[root],cycle_count[root],period[root]=r,c,d
        declared_size[root],declared_internal[root],cyc[root]=size,internal,int(iscyclic)
        nblocks+=1
    nvertices=0
    for key,root,h,d in records(Path(str(prefix)+'_vertices.bin'),4):
        require(0<=key<space and gcd(key//K,M)==1 and owner[key]==-1,'Bad vertex')
        require(0<=root<space and rank[root]>0 and h>=0,'Bad vertex metadata')
        require(d==period[root],'Node/block period mismatch')
        owner[key],distance[key]=root,h
        actual_size[root]+=1;nvertices+=1
    for q in range(M):
        if gcd(q,M)==1:
            for j in range(K):
                require(owner[q*K+j]>=0,'Missing legal initial state')
    require(nvertices==491520,'Unexpected legal state count')
    for root in range(space):
        require(actual_size[root]==declared_size[root],'Block-size mismatch')
    carries=[c for c in range(1-b,a) if (c-(b-a))%2==0 and gcd(c,a*b)==1]
    require(carries==[-4,-2,2,4,6],'Carry alphabet mismatch')
    cells={}
    for j in range(K):
        for c in carries:
            low=max(0,(a*j-c*K)//b)
            high=min(K-1,(a*(j+1)-c*K-1)//b)
            cells[j,c]=range(low,high+1)
    labels={};edges=0
    inv=pow(b,-1,M)
    for q in range(M):
        if gcd(q,M)!=1:
            continue
        zlist={c:(a*q+c)*inv%M for c in carries}
        for j in range(K):
            u=q*K+j;ru=owner[u]
            for c in carries:
                z=zlist[c]
                if gcd(z,M)!=1:
                    continue
                for k in cells[j,c]:
                    v=z*K+k;rv=owner[v]
                    require(rv>=0,'Edge target missing')
                    edges+=1
                    if ru==rv:
                        require(cyc[ru] and period[ru]>0,'Internal edge in edgeless block')
                        d=period[ru]
                        require((distance[v]-distance[u]-1)%d==0,'Phase increment')
                        phase=distance[u]%d
                        old=labels.setdefault((ru,phase),c)
                        require(old==c,'Nonperiodic phase output')
                        actual_internal[ru]+=1
                    else:
                        require(rank[rv]>=rank[ru]+1,'Non-increasing block rank')
                        require(cycle_count[rv]>=cycle_count[ru]+cyc[rv],
                                'Cyclic-visit count inequality')
    require(edges==891990,'Unexpected complete edge count')
    for root in range(space):
        require(actual_internal[root]==declared_internal[root],'Internal edge count mismatch')
    return dict(complete_state_coverage=True,complete_python_edge_enumeration=True,
                V=nvertices,E=edges,blocks=nblocks,periodic_blocks=sum(cyc),
                block_rank_bound=65,maximum_cross_block_edges=64,
                periodic_visit_bound=6,period_bound=13,
                phase_entries=len(labels))


def coefficient_check() -> dict:
    gamma=Fraction(5,4)
    # log_5(7/5)<1/4, verified without evaluating any logarithm.
    require(7**4<5**5,'Growth comparison')
    slope=sum(gamma**j for j in range(6))
    constant=64*gamma**6+13*gamma*slope
    require(slope<12 and constant<428,'Published integer constants do not follow')
    return dict(growth_check='7^4 < 5^5',exact_slope=str(slope),
                exact_constant=str(constant),published_constant=428,
                published_log_coefficient=12,
                integer_log='min { h>=0 : 5^h >= P+2 }')


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('quantitative_75_verification.json'))
    parser.add_argument('--compiler',default='g++')
    # Output-directory handling: keep the C++ sources and the scientific
    # arrays in a persistent directory so that they can be dumped and hashed.
    # Without --workdir the behaviour is unchanged (temporary directory).
    parser.add_argument('--workdir',type=Path,default=None,
                        help='New persistent directory for sources and arrays (must not exist)')
    args=parser.parse_args()
    compiler=shutil.which(args.compiler)
    require(compiler is not None,'GNU-compatible C++17 compiler required')
    import contextlib
    if args.workdir is None:
        context=tempfile.TemporaryDirectory(prefix='quantitative-75-')
    else:
        args.workdir.mkdir(parents=True,exist_ok=False)
        context=contextlib.nullcontext(str(args.workdir))
    with context as td:
        root=Path(td)
        source_a=SOURCE_A.replace('/mnt/data/continued_research/graphA',str(root/'graphA'))
        source_a=source_a.replace('/mnt/data/continued_research/last_states.bin',str(root/'unused_last_states.bin'))
        source_b=SOURCE_B.replace('/mnt/data/continued_research/graphB',str(root/'graphB'))
        exe_a=compile_one(source_a,'graph_a',root,compiler)
        exe_b=compile_one(source_b,'graph_b',root,compiler)
        aa=subprocess.run([str(exe_a),'7','5','2048','429'],capture_output=True,text=True,timeout=120)
        bb=subprocess.run([str(exe_b)],capture_output=True,text=True,timeout=120)
        require(aa.returncode==0 and bb.returncode==0,'Graph construction did not complete')
        data_a=json.loads(aa.stdout.strip().splitlines()[-1]);data_b=json.loads(bb.stdout)
        for key in ('a','b','M','K','V','E','SCC','cyclic','cert'):
            require(data_a[key]==data_b[key],f'Graph summary mismatch: {key}')
        arrays={}
        for suffix in ('edges','vertices','components'):
            pa,pb=root/f'graphA_{suffix}.bin',root/f'graphB_{suffix}.bin'
            require(filecmp.cmp(pa,pb,shallow=False),f'Full scientific array disagreement: {suffix}')
            arrays[suffix]=dict(bytes=pa.stat().st_size,exact_bytewise_agreement=True,
                                sha256=hashlib.sha256(pa.read_bytes()).hexdigest())
        checked=check_certificate(root/'graphB')
    report=dict(status='all_checks_passed',graph=data_b,full_array_comparisons=arrays,
                python_certificate_check=checked,inequalities=coefficient_check(),
                conclusion='For every real xi with P=floor(xi)>13, gcd(floor(xi*(7/5)^n),4290)>1 occurs by '
                           'index 428+12*ceil(log_5(P+2)); hence this applies after every tail shift.',
                scope='Quantitative strengthening for 7/5 only; not an infinite rational-base family theorem',
                formal_verification=False)
    args.output.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,ensure_ascii=False,indent=2))

if __name__=='__main__':
    main()
