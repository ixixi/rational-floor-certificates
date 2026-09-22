#!/usr/bin/env python3
"""Reproduce the 5/2 word-edge certificate from scratch.

Requires Python >=3.10 and a C++17 compiler (g++ by default).
No Python packages, prior project files, or downloaded certificate data needed.
All graph words and arithmetic are exact. Typical raw graph space: 350 MiB;
raw graphs are removed after comparison unless --keep-graphs is specified.
A timeout, a resource cutoff, or a discrepancy is INCONCLUSIVE/ERROR, not success.

Usage:
    python3 verify_five_halves.py --workdir check-52
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
from collections import deque
from fractions import Fraction
from typing import Any

SOURCE_A = '// Exact certificate construction A for floor(xi*(5/2)^n).\n// Integer interval enumeration, root-mask prime lifts, Kosaraju components.\n// All resource cutoffs are failures/inconclusive, never a successful certificate.\n// Build: g++ -std=c++17 -O2 construction_a.cpp -o construction_a\n// Run: ./construction_a OUTPUT_DIRECTORY\n#include <algorithm>\n#include <chrono>\n#include <cstdint>\n#include <iostream>\n#include <numeric>\n#include <queue>\n#include <string>\n#include <vector>\n#include <stdexcept>\n#include <fstream>\n#include <filesystem>\n#include <limits>\nusing namespace std;\nusing I=int64_t;\nint a=5,b=2,K=4;size_t cap=9000000,wordcap=1000000;\nusing U=uint64_t;\nvector<U> tags;\nU mod_product=1;\nstring directory;\nint stage_number=0;\nstruct E {int v;string w;};using G=vector<vector<E>>;\nint mod(I x,int p){int r=x%p;return r<0?r+p:r;}\nint inv(int a,int p){int r=1;for(int n=p-2;n;n>>=1,a=I(a)*a%p)if(n&1)r=I(r)*a%p;return r;}\nint flo(int x,int b){int r=x%b;if(r<0)r+=b;return (x-r)/b;}\nint cval(char x){return int((unsigned char)x)-128;}\nchar enc(int c){return char(c+128);}\n\n// Sort by an intrinsic vertex name (residue modulo the primes used, cell).\n// All edge multiplicities are retained in this normalization.\nvoid canonicalize(G& g){\n size_t n=g.size(); if(tags.size()!=n)throw runtime_error("tag count mismatch");\n vector<int> order(n),idx(n);iota(order.begin(),order.end(),0);\n sort(order.begin(),order.end(),[&](int x,int y){return tags[x]<tags[y];});\n G sorted(n);vector<U> nt(n);\n for(size_t i=0;i<n;i++){idx[order[i]]=i;nt[i]=tags[order[i]];if(i&&nt[i]==nt[i-1])throw runtime_error("duplicate tag");}\n for(size_t i=0;i<n;i++){\n  sorted[i]=move(g[order[i]]);\n  for(auto& e:sorted[i]) e.v=idx[e.v];\n  sort(sorted[i].begin(),sorted[i].end(),[](const E&x,const E&y){return x.v<y.v||(x.v==y.v&&x.w<y.w);});\n }\n g=move(sorted);tags=move(nt);\n}\nvoid little(ofstream&f,U x,int bytes){for(int i=0;i<bytes;i++){f.put(char(x&255));x>>=8;}}\nvoid dump(const G&g,const string&suffix){\n string name=directory+"/"+to_string(stage_number)+"_"+suffix+".bin";\n ofstream f(name,ios::binary);if(!f)throw runtime_error("cannot open graph output");\n f.write("WORDGR01",8);little(f,mod_product,8);little(f,K,4);little(f,g.size(),8);\n for(size_t u=0;u<g.size();u++){\n  little(f,tags[u],8);little(f,g[u].size(),4);\n  for(const auto&e:g[u]){\n   if(e.w.empty()||e.w.size()>wordcap)throw runtime_error("invalid word length");\n   little(f,tags[e.v],8);little(f,e.w.size(),4);f.write(e.w.data(),e.w.size());\n  }\n }\n if(!f)throw runtime_error("graph output write failed");\n}\n\nstruct Summary{size_t n,e,cyc,cert,badn,branch,maxword,totalword;};\nG prune(G g,Summary& s){\n int n=g.size();s.n=n;s.e=0;for(auto&v:g)s.e+=v.size();\n vector<vector<int>>rev(n);for(int u=0;u<n;u++)for(auto&e:g[u])rev[e.v].push_back(u);\n vector<unsigned char>vis(n);vector<int>ord;ord.reserve(n);vector<pair<int,size_t>>stk;\n for(int root=0;root<n;root++)if(!vis[root]){vis[root]=1;stk.push_back({root,0});while(!stk.empty()){\n  auto&f=stk.back();int u=f.first;if(f.second<g[u].size()){int v=g[u][f.second++].v;if(!vis[v]){vis[v]=1;stk.push_back({v,0});}}else{ord.push_back(u);stk.pop_back();}\n }}\n vector<int>owner(n,-1),roots,sizes,st;\n for(auto it=ord.rbegin();it!=ord.rend();++it){int root=*it;if(owner[root]>=0)continue;int c=roots.size(),sz=0;roots.push_back(root);owner[root]=c;st.push_back(root);while(!st.empty()){int u=st.back();st.pop_back();sz++;for(int v:rev[u])if(owner[v]<0){owner[v]=c;st.push_back(v);}}sizes.push_back(sz);}\n rev.clear();rev.shrink_to_fit();\n int nc=roots.size();vector<I>h(n,-1),d(nc);vector<int>nie(nc),que;\n for(int c=0;c<nc;c++){h[roots[c]]=0;que.clear();que.push_back(roots[c]);for(size_t i=0;i<que.size();i++){int u=que[i];for(auto&e:g[u])if(owner[e.v]==c&&h[e.v]<0){h[e.v]=h[u]+e.w.size();que.push_back(e.v);}}}\n for(int u=0;u<n;u++)for(auto&e:g[u])if(owner[u]==owner[e.v]){int c=owner[u];nie[c]++;d[c]=gcd(d[c],abs(h[u]+I(e.w.size())-h[e.v]));}\n vector<unsigned char>bad(nc);vector<vector<int>>lab(nc);s.cyc=s.cert=s.badn=0;\n for(int c=0;c<nc;c++)if(nie[c]){s.cyc++;if(d[c]<=0)throw runtime_error("cycle length zero");if(d[c]>(I)wordcap)bad[c]=1;else lab[c].assign(d[c],999);}\n for(int u=0;u<n;u++)for(auto&e:g[u])if(owner[u]==owner[e.v]){int c=owner[u];if(bad[c])continue;I ph=h[u]%d[c];for(char letter:e.w){int v=cval(letter);if(lab[c][ph]==999)lab[c][ph]=v;else if(lab[c][ph]!=v){bad[c]=1;break;}ph++;if(ph==d[c])ph=0;}}\n for(int c=0;c<nc;c++)if(nie[c]){if(bad[c])s.badn+=sizes[c];else s.cert++;}\n // Drop intercomponent transitions: only eventual tails are needed.\n for(int u=0;u<n;u++){\n  auto&v=g[u];v.erase(remove_if(v.begin(),v.end(),[&](const E&e){return !bad[owner[u]]||owner[e.v]!=owner[u];}),v.end());\n  sort(v.begin(),v.end(),[](const E&x,const E&y){return x.v<y.v||(x.v==y.v&&x.w<y.w);});\n  v.erase(unique(v.begin(),v.end(),[](const E&x,const E&y){return x.v==y.v&&x.w==y.w;}),v.end());\n }\n // Recheck pure functional components after deduplication. Keeping one anchor\n // is safe even if all labels periodic; next prune will remove it.\n vector<int>id(n,-1);int count=0;\n for(int u=0;u<n;u++)if(bad[owner[u]]&&g[u].size()!=1&&g[u].size()>0)id[u]=count++;\n for(int c=0;c<nc;c++)if(bad[c]){bool has=false;for(int u=0;u<n&&!has;u++)if(owner[u]==c&&id[u]>=0)has=true;if(!has)id[roots[c]]=count++;}\n G out(count);vector<U> nt(count);for(int u=0;u<n;u++)if(id[u]>=0)nt[id[u]]=tags[u];s.maxword=s.totalword=0;\n for(int u=0;u<n;u++)if(id[u]>=0)for(auto&e:g[u]){\n  string w=e.w;int v=e.v;size_t steps=0;\n  while(id[v]<0){if(g[v].size()!=1)throw runtime_error("bad compressed path");w+=g[v][0].w;v=g[v][0].v;if(++steps>size_t(n)||w.size()>wordcap)throw runtime_error("inconclusive word cap");}\n  s.maxword=max(s.maxword,w.size());s.totalword+=w.size();out[id[u]].push_back({id[v],move(w)});\n }\n s.branch=count;tags=move(nt);return out;\n}\nG lift(const G&g,int p){\n if(size_t(g.size())*p>cap)throw runtime_error("inconclusive lift cap");\n vector<int>id(g.size()*p,-1);G h;vector<U> nt;\n if(mod_product%p==0)throw runtime_error("repeated prime");\n if(mod_product>numeric_limits<U>::max()/U(K*p))throw runtime_error("tag overflow");\n int mi=inv(mod_product%p,p);\n auto get=[&](int u,int q){int&v=id[size_t(u)*p+q];if(v<0){v=h.size();h.emplace_back();U oldq=tags[u]/K;U cell=tags[u]%K;\n U newq=oldq+mod_product*U(mod(I(q)-I(oldq%p),p)*mi%p);nt.push_back(newq*K+cell);}return v;};\n int ai=inv(a%p,p),bi=inv(b%p,p),ratio=a*bi%p,invr=b*ai%p;\n for(int u=0;u<(int)g.size();u++)for(auto&e:g[u]){\n  vector<unsigned char>forbid(p);forbid[0]=1;int weight=ai,root=0,alpha=1,beta=0,used=1;\n  for(char z:e.w){int c=cval(z);root=mod(root-I(c)*weight,p);if(!forbid[root]){forbid[root]=1;used++;}weight=weight*invr%p;alpha=alpha*ratio%p;beta=mod(I(ratio)*beta+I(c)*bi,p);if(used==p)break;}\n  if(used==p)continue;\n  for(int q=1;q<p;q++)if(!forbid[q]){int z=mod(I(alpha)*q+beta,p);if(!z)throw runtime_error("missed zero");int source=get(u,q),target=get(e.v,z);h[source].push_back({target,e.w});}\n }\n tags=move(nt);mod_product*=p;return h;\n}\nbool prime(int n){for(int d=2;d*d<=n;d++)if(n%d==0)return false;return n>=2;}\n\nint main(int argc,char**argv){\n if(argc!=2){cerr<<"Usage: construction_a OUTPUT_DIRECTORY\\n";return 1;}\n try{\n  directory=argv[1];filesystem::create_directories(directory);\n  G g(K);tags.resize(K);iota(tags.begin(),tags.end(),0);\n  for(int j=0;j<K;j++)for(int c:{-1,1,3}){\n   int lo=max(0,flo(a*j-c*K,b)),hi=min(K-1,flo(a*(j+1)-c*K-1,b));\n   for(int k=lo;k<=hi;k++)g[j].push_back({k,string(1,enc(c))});\n  }\n  vector<int> primes={1,3,7,11,13,17,19,23,29,31};\n  for(int p:primes){\n   auto clock=chrono::steady_clock::now();\n   if(p!=1){if(!prime(p)||a*b%p==0)throw runtime_error("invalid prime");g=lift(g,p);}\n   canonicalize(g);dump(g,"input");\n   Summary s{};g=prune(move(g),s);\n   canonicalize(g);dump(g,"output");\n   size_t ne=0;for(auto&v:g)ne+=v.size();\n   cout<<"{\\"stage\\":"<<stage_number<<",\\"p\\":"<<p<<",\\"mod_product\\":"<<mod_product\n    <<",\\"input_vertices\\":"<<s.n<<",\\"input_edges\\":"<<s.e\n    <<",\\"cyclic\\":"<<s.cyc<<",\\"certified\\":"<<s.cert<<",\\"retained\\":"<<s.badn\n    <<",\\"macro_vertices\\":"<<g.size()<<",\\"macro_edges\\":"<<ne\n    <<",\\"max_word\\":"<<s.maxword<<",\\"total_word\\":"<<s.totalword\n    <<",\\"seconds\\":"<<chrono::duration<double>(chrono::steady_clock::now()-clock).count()<<"}"<<endl;\n   stage_number++;\n   if(g.empty())break;\n  }\n  if(!g.empty()){cerr<<"INCONCLUSIVE: graph is not empty\\n";return 2;}\n  cout<<"{\\"success\\":true,\\"prime_product_with_2\\":"<<2*mod_product<<"}"<<endl;\n }catch(const exception&e){cerr<<"INCONCLUSIVE/ERROR: "<<e.what()<<"\\n";return 2;}\n}\n'
SOURCE_B = '// Verification construction B for floor(xi*(5/2)^n).\n// Direct cell-pair tests, direct modular simulation along every word,\n// iterative Tarjan components, and checked forward/reverse connectivity.\n// This is a separately coded algorithmic cross-check, NOT a clean-room\n// provenance claim and NOT a proof-assistant/kernel formalization.\n// Build: g++ -std=c++17 -O2 checker_b.cpp -o checker_b\n// Run: ./checker_b OUTPUT_DIRECTORY\n#include <algorithm>\n#include <chrono>\n#include <cstdint>\n#include <filesystem>\n#include <fstream>\n#include <iostream>\n#include <numeric>\n#include <stdexcept>\n#include <string>\n#include <utility>\n#include <vector>\n\nnamespace {\nusing Word = std::string;\nusing U64 = std::uint64_t;\nusing I64 = std::int64_t;\nconstexpr int A=5, B=2, CELLS=4;\nconstexpr std::size_t VERTEX_LIMIT=9000000;\nconstexpr std::size_t WORD_LIMIT=1000000;\n\nvoid require(bool x, const char* message) {\n    if (!x) throw std::runtime_error(message);\n}\nint residue(I64 x, int p) {\n    I64 y=x%p;\n    return int(y<0 ? y+p : y);\n}\nint inverse_by_search(int x, int p) {\n    for (int y=1; y<p; ++y) if (I64(x)*y%p==1) return y;\n    throw std::runtime_error("noninvertible coefficient");\n}\nint carry(char c) {return int(static_cast<unsigned char>(c))-128;}\nstruct Arc {int target; Word letters;};\nstruct Graph {\n    std::vector<std::vector<Arc>> out;\n    std::vector<U64> name;\n    U64 mod_product=1;\n};\nstruct Counts {\n    std::size_t input_vertices=0, input_edges=0, cyclic=0, certified=0;\n    std::size_t retained=0, macro_vertices=0, macro_edges=0;\n    std::size_t max_word=0, total_word=0;\n    std::size_t max_certified_period=0, max_certified_size=0;\n};\n\n// Canonical state name = (CRT residue)*4 + fractional-cell number.\nvoid normalize(Graph& graph) {\n    const int n=int(graph.out.size());\n    require(graph.name.size()==std::size_t(n),"name count mismatch");\n    std::vector<std::pair<U64,int>> permutation;\n    permutation.reserve(n);\n    for (int v=0; v<n; ++v) permutation.emplace_back(graph.name[v],v);\n    std::sort(permutation.begin(),permutation.end());\n    std::vector<int> new_index(n);\n    std::vector<U64> names(n);\n    for (int v=0; v<n; ++v) {\n        require(v==0 || permutation[v-1].first!=permutation[v].first,\n                "duplicate canonical name");\n        names[v]=permutation[v].first;\n        new_index[permutation[v].second]=v;\n    }\n    std::vector<std::vector<Arc>> edges(n);\n    for (int v=0; v<n; ++v) {\n        edges[v]=std::move(graph.out[permutation[v].second]);\n        for (auto& e:edges[v]) {\n            require(0<=e.target && e.target<n,"edge endpoint outside graph");\n            e.target=new_index[e.target];\n            require(!e.letters.empty() && e.letters.size()<=WORD_LIMIT,\n                    "empty or excessive edge word");\n        }\n        std::sort(edges[v].begin(),edges[v].end(),[](const Arc&x,const Arc&y){\n            return x.target==y.target ? x.letters<y.letters : x.target<y.target;\n        });\n    }\n    graph.name=std::move(names);\n    graph.out=std::move(edges);\n}\nvoid write_number(std::ofstream& stream, U64 x, int length) {\n    char buffer[8];\n    for (int k=0;k<length;k++) buffer[k]=char((x>>(8*k))&255);\n    stream.write(buffer,length);\n}\nvoid save_graph(const Graph& graph,const std::string& filename) {\n    std::ofstream f(filename,std::ios::binary);\n    require(bool(f),"could not create graph output");\n    f.write("WORDGR01",8);\n    write_number(f,graph.mod_product,8);\n    write_number(f,CELLS,4);\n    write_number(f,graph.out.size(),8);\n    for (int v=0;v<int(graph.out.size());++v) {\n        write_number(f,graph.name[v],8);\n        write_number(f,graph.out[v].size(),4);\n        for (const auto&e:graph.out[v]) {\n            write_number(f,graph.name[e.target],8);\n            write_number(f,e.letters.size(),4);\n            f.write(e.letters.data(),e.letters.size());\n        }\n    }\n    require(bool(f),"graph output write failed");\n}\nGraph initial_graph() {\n    Graph g;\n    g.out.resize(CELLS);\n    g.name.resize(CELLS);\n    for (int j=0;j<CELLS;++j) {\n        g.name[j]=j;\n        // Deliberately test every target, rather than use the interval formula.\n        for (int k=0;k<CELLS;++k) for (int c=-1;c<=4;++c) {\n            if (c%2==0) continue;\n            if (A*j-B*(k+1)<c*CELLS && c*CELLS<A*(j+1)-B*k)\n                g.out[j].push_back({k,Word(1,char(c+128))});\n        }\n    }\n    return g;\n}\n\n// Construct all Cartesian states, then remove only completely isolated ones.\n// Modular trajectories are directly evaluated at every position of every word.\nGraph add_prime(const Graph& old,int p) {\n    require(old.mod_product%p!=0,"repeated prime");\n    require(A%p!=0 && B%p!=0,"prime divides base coefficients");\n    const std::size_t count=old.out.size()*std::size_t(p-1);\n    require(count<=VERTEX_LIMIT,"INCONCLUSIVE: vertex limit");\n    const int inv_b=inverse_by_search(B%p,p);\n    const int inv_m=inverse_by_search(old.mod_product%p,p);\n    Graph full;\n    full.out.resize(count);\n    full.name.resize(count);\n    full.mod_product=old.mod_product*U64(p);\n    for (int u=0;u<int(old.out.size());++u) {\n        for (int q=1;q<p;++q) {\n            const int source=u*(p-1)+q-1;\n            const U64 oldq=old.name[u]/CELLS;\n            const U64 cell=old.name[u]%CELLS;\n            const int lift=residue((I64(q)-I64(oldq%p))*inv_m,p);\n            const U64 combined=oldq+old.mod_product*U64(lift);\n            full.name[source]=combined*CELLS+cell;\n            for (const Arc& edge:old.out[u]) {\n                int z=q;\n                for (char letter:edge.letters) {\n                    z=residue((I64(A)*z+carry(letter))*inv_b,p);\n                    if (z==0) break;\n                }\n                if (z!=0) full.out[source].push_back({edge.target*(p-1)+z-1,edge.letters});\n            }\n        }\n    }\n    std::vector<unsigned char> incident(count,0);\n    for (int u=0;u<int(count);++u) for(const auto&e:full.out[u]) {\n        incident[u]=1;incident[e.target]=1;\n    }\n    std::vector<int> renumber(count,-1);\n    Graph result;result.mod_product=full.mod_product;\n    for(int u=0;u<int(count);++u) if(incident[u]) {\n        renumber[u]=int(result.name.size());\n        result.name.push_back(full.name[u]);\n    }\n    result.out.resize(result.name.size());\n    for(int u=0;u<int(count);++u) if(incident[u]) {\n        auto& edges=result.out[renumber[u]];\n        edges=std::move(full.out[u]);\n        for(auto&e:edges) {\n            require(renumber[e.target]>=0,"removed nonisolated target");\n            e.target=renumber[e.target];\n        }\n    }\n    return result;\n}\n\n// Iterative Tarjan, independent of construction A\'s reverse-order Kosaraju.\nstd::vector<int> components(const Graph& g,int& component_count) {\n    const int n=int(g.out.size());\n    std::vector<int> number(n,-1),low(n),owner(n,-1),active;\n    std::vector<unsigned char> on_stack(n,0);\n    struct Frame {int vertex; std::size_t next_edge;};\n    std::vector<Frame> call_stack;\n    int time=0;component_count=0;\n    for (int root=0;root<n;++root) {\n        if(number[root]>=0)continue;\n        number[root]=low[root]=time++;\n        active.push_back(root);on_stack[root]=1;\n        call_stack.push_back({root,0});\n        while(!call_stack.empty()) {\n            int u=call_stack.back().vertex;\n            auto& next=call_stack.back().next_edge;\n            if(next<g.out[u].size()) {\n                int v=g.out[u][next++].target;\n                if(number[v]<0) {\n                    number[v]=low[v]=time++;\n                    active.push_back(v);on_stack[v]=1;\n                    call_stack.push_back({v,0});\n                } else if(on_stack[v]) {\n                    low[u]=std::min(low[u],number[v]);\n                }\n            } else {\n                call_stack.pop_back();\n                if(low[u]==number[u]) {\n                    while(true) {\n                        require(!active.empty(),"Tarjan stack underflow");\n                        int v=active.back();active.pop_back();on_stack[v]=0;\n                        owner[v]=component_count;\n                        if(v==u)break;\n                    }\n                    ++component_count;\n                }\n                if(!call_stack.empty()) {\n                    int parent=call_stack.back().vertex;\n                    low[parent]=std::min(low[parent],low[u]);\n                }\n            }\n        }\n    }\n    require(active.empty(),"Tarjan stack not exhausted");\n    for(int c:owner)require(c>=0 && c<component_count,"unassigned component");\n    return owner;\n}\n\nGraph remove_and_compress(Graph g,Counts& stats) {\n    const int n=int(g.out.size());\n    stats.input_vertices=n;\n    for(const auto&edges:g.out)stats.input_edges+=edges.size();\n    int nc=0;auto owner=components(g,nc);\n    std::vector<int> root(nc,-1),size(nc,0);\n    for(int v=0;v<n;++v) {\n        int c=owner[v];++size[c];\n        if(root[c]<0)root[c]=v;\n    }\n    // Explicitly check strong connectivity in both directions. Also check that\n    // the integer component number is a strict rank on every interblock edge.\n    std::vector<std::vector<int>> reverse(n);\n    for(int u=0;u<n;++u)for(const auto&e:g.out[u]) {\n        reverse[e.target].push_back(u);\n        if(owner[u]!=owner[e.target])\n            require(owner[u]>owner[e.target],"condensation rank does not decrease");\n    }\n    std::vector<I64> distance(n,-1);\n    std::vector<unsigned char> back_seen(n,0);\n    std::vector<int> stack;\n    for(int c=0;c<nc;++c) {\n        require(size[c]>0 && root[c]>=0,"empty component");\n        int seen=0;\n        distance[root[c]]=0;stack.push_back(root[c]);\n        while(!stack.empty()) {\n            int u=stack.back();stack.pop_back();++seen;\n            for(const auto&e:g.out[u])if(owner[e.target]==c && distance[e.target]<0) {\n                distance[e.target]=distance[u]+I64(e.letters.size());\n                stack.push_back(e.target);\n            }\n        }\n        require(seen==size[c],"component not forward connected");\n        seen=0;back_seen[root[c]]=1;stack.push_back(root[c]);\n        while(!stack.empty()) {\n            int v=stack.back();stack.pop_back();++seen;\n            for(int u:reverse[v])if(owner[u]==c && !back_seen[u]) {\n                back_seen[u]=1;stack.push_back(u);\n            }\n        }\n        require(seen==size[c],"component not reverse connected");\n    }\n    reverse.clear();reverse.shrink_to_fit();\n    std::vector<I64> period(nc,0);\n    std::vector<std::size_t> inside_edges(nc,0);\n    for(int u=0;u<n;++u)for(const auto&e:g.out[u])if(owner[u]==owner[e.target]) {\n        int c=owner[u];++inside_edges[c];\n        I64 gap=distance[u]+I64(e.letters.size())-distance[e.target];\n        if(gap<0)gap=-gap;\n        period[c]=std::gcd(period[c],gap);\n    }\n    std::vector<unsigned char> bad(nc,0);\n    std::vector<std::vector<int>> phases(nc);\n    for(int c=0;c<nc;++c)if(inside_edges[c]) {\n        ++stats.cyclic;\n        require(period[c]>0,"cyclic block has zero period");\n        if(period[c]>I64(WORD_LIMIT))bad[c]=1;\n        else phases[c].assign(std::size_t(period[c]),1000);\n    }\n    for(int u=0;u<n;++u)for(const auto&e:g.out[u])if(owner[u]==owner[e.target]) {\n        int c=owner[u];if(bad[c])continue;\n        require((distance[u]+I64(e.letters.size())-distance[e.target])%period[c]==0,\n                "phase increment incorrect");\n        for(std::size_t k=0;k<e.letters.size();++k) {\n            const I64 phase=(distance[u]+I64(k))%period[c];\n            int letter=carry(e.letters[k]);\n            int& recorded=phases[c][phase];\n            if(recorded==1000)recorded=letter;\n            else if(recorded!=letter){bad[c]=1;break;}\n        }\n    }\n    for(int c=0;c<nc;++c)if(inside_edges[c]) {\n        if(bad[c])stats.retained+=size[c];\n        else {\n            ++stats.certified;\n            stats.max_certified_period=std::max(stats.max_certified_period,std::size_t(period[c]));\n            stats.max_certified_size=std::max(stats.max_certified_size,std::size_t(size[c]));\n            for(int letter:phases[c])require(letter!=1000,"unused periodic phase");\n        }\n    }\n    // Keep all and only internal edges in uncertified components. Deduplicate\n    // only identical edges, never distinct words with the same endpoints.\n    for(int u=0;u<n;++u) {\n        std::vector<Arc> keep;\n        if(bad[owner[u]])for(auto&e:g.out[u])if(owner[e.target]==owner[u])\n            keep.push_back(std::move(e));\n        std::sort(keep.begin(),keep.end(),[](const Arc&x,const Arc&y){\n            return x.target==y.target ? x.letters<y.letters : x.target<y.target;\n        });\n        keep.erase(std::unique(keep.begin(),keep.end(),[](const Arc&x,const Arc&y){\n            return x.target==y.target && x.letters==y.letters;\n        }),keep.end());\n        g.out[u]=std::move(keep);\n    }\n    std::vector<unsigned char> anchor(n,0),has_anchor(nc,0);\n    for(int u=0;u<n;++u)if(bad[owner[u]]) {\n        require(!g.out[u].empty(),"retained component has a dead end");\n        if(g.out[u].size()>1){anchor[u]=1;has_anchor[owner[u]]=1;}\n    }\n    for(int c=0;c<nc;++c)if(bad[c] && !has_anchor[c])anchor[root[c]]=1;\n    Graph result;result.mod_product=g.mod_product;\n    std::vector<int> mapping(n,-1);\n    for(int u=0;u<n;++u)if(anchor[u]) {\n        mapping[u]=int(result.name.size());result.name.push_back(g.name[u]);\n    }\n    result.out.resize(result.name.size());\n    for(int u=0;u<n;++u)if(anchor[u])for(const auto&first:g.out[u]) {\n        Word full_word=first.letters;\n        int v=first.target;\n        std::size_t traversed=1;\n        while(!anchor[v]) {\n            require(g.out[v].size()==1,"nonunique suppressed continuation");\n            const auto& next=g.out[v][0];\n            full_word.append(next.letters);v=next.target;\n            require(++traversed<=std::size_t(n)+1,"closed suppressed cycle");\n            require(full_word.size()<=WORD_LIMIT,"INCONCLUSIVE: word limit");\n        }\n        require(mapping[v]>=0,"missing compressed endpoint");\n        ++stats.macro_edges;\n        stats.max_word=std::max(stats.max_word,full_word.size());\n        stats.total_word+=full_word.size();\n        result.out[mapping[u]].push_back({mapping[v],std::move(full_word)});\n    }\n    stats.macro_vertices=result.out.size();\n    return result;\n}\n} // namespace\n\nint main(int argc,char**argv) {\n    if(argc!=2){std::cerr<<"Usage: checker_b OUTPUT_DIRECTORY\\n";return 1;}\n    try {\n        const std::string directory=argv[1];\n        std::filesystem::create_directories(directory);\n        Graph graph=initial_graph();\n        const std::vector<int> primes={1,3,7,11,13,17,19,23,29,31};\n        int stage=0;\n        for(int p:primes) {\n            auto begin=std::chrono::steady_clock::now();\n            if(p!=1)graph=add_prime(graph,p);\n            normalize(graph);\n            save_graph(graph,directory+"/"+std::to_string(stage)+"_input.bin");\n            Counts counts;\n            graph=remove_and_compress(std::move(graph),counts);\n            normalize(graph);\n            save_graph(graph,directory+"/"+std::to_string(stage)+"_output.bin");\n            std::cout<<"{\\"stage\\":"<<stage<<",\\"p\\":"<<p\n                <<",\\"mod_product\\":"<<graph.mod_product\n                <<",\\"input_vertices\\":"<<counts.input_vertices\n                <<",\\"input_edges\\":"<<counts.input_edges\n                <<",\\"cyclic\\":"<<counts.cyclic\n                <<",\\"certified\\":"<<counts.certified\n                <<",\\"retained\\":"<<counts.retained\n                <<",\\"macro_vertices\\":"<<counts.macro_vertices\n                <<",\\"macro_edges\\":"<<counts.macro_edges\n                <<",\\"max_word\\":"<<counts.max_word\n                <<",\\"total_word\\":"<<counts.total_word\n                <<",\\"max_certified_period\\":"<<counts.max_certified_period\n                <<",\\"max_certified_size\\":"<<counts.max_certified_size\n                <<",\\"seconds\\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()\n                <<"}"<<std::endl;\n            ++stage;\n            if(graph.out.empty())break;\n        }\n        require(graph.out.empty(),"INCONCLUSIVE: final graph is not empty");\n        std::cout<<"{\\"success\\":true,\\"prime_product_with_2\\":"<<2*graph.mod_product<<"}"<<std::endl;\n    } catch(const std::exception& error) {\n        std::cerr<<"INCONCLUSIVE/ERROR: "<<error.what()<<"\\n";return 2;\n    }\n}\n'
PRIMES = (1, 3, 7, 11, 13, 17, 19, 23, 29, 31)
CHECK_FIELDS = (
    "stage", "p", "mod_product", "input_vertices", "input_edges",
    "cyclic", "certified", "retained", "macro_vertices", "macro_edges",
    "max_word", "total_word",
)
EXPECTED_FINAL = {"mod_product": 20056049013, "input_vertices": 2856938,
                  "input_edges": 3754612, "cyclic": 1084, "certified": 1084,
                  "retained": 0, "macro_vertices": 0, "macro_edges": 0}
Graph = dict[int, list[tuple[int, tuple[int, ...]]]]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def reference_initial() -> Graph:
    """A third initial enumeration using exact rational intersections."""
    g: Graph = {j: [] for j in range(4)}
    for j in range(4):
        for k in range(4):
            for c in (-1, 1, 3):
                lo = max(Fraction(j, 4), (c + 2*Fraction(k, 4))/5)
                hi = min(Fraction(j+1, 4), (c + 2*Fraction(k+1, 4))/5)
                if lo < hi:
                    g[j].append((k, (c,)))
    return g


def reference_lift(g: Graph, product: int, p: int) -> Graph:
    inv2, invm = pow(2, -1, p), pow(product, -1, p)
    h: Graph = {}

    def name(u: int, q: int) -> int:
        old, cell = divmod(u, 4)
        combined = old + product*((q-old)*invm % p)
        return 4*combined+cell

    for u, edges in g.items():
        for q in range(1, p):
            source = name(u, q)
            for v, word in edges:
                z = q
                for c in word:
                    z = (5*z+c)*inv2 % p
                    if z == 0:
                        break
                else:
                    target = name(v, z)
                    h.setdefault(source, []).append((target, word))
                    h.setdefault(target, [])
    return h


def reference_prune(g: Graph) -> Graph:
    """Small graph check by all-source reachability, not an SCC library."""
    reach: dict[int, set[int]] = {}
    for root in g:
        reached = {root}
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v, _ in g[u]:
                if v not in reached:
                    reached.add(v)
                    queue.append(v)
        reach[root] = reached
    unseen = set(g)
    retained_components: list[set[int]] = []
    surviving: Graph = {}
    while unseen:
        root = min(unseen)
        component = {v for v in unseen if v in reach[root] and root in reach[v]}
        unseen.difference_update(component)
        internal = {u: [(v, w) for v, w in g[u] if v in component]
                    for u in component}
        if not any(internal.values()):
            continue
        distances = {root: 0}
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v, w in internal[u]:
                if v not in distances:
                    distances[v] = distances[u]+len(w)
                    queue.append(v)
        require(set(distances) == component, "reference component disconnected")
        d = 0
        for u, edges in internal.items():
            for v, w in edges:
                d = math.gcd(d, abs(distances[u]+len(w)-distances[v]))
        require(d > 0, "reference period zero")
        labels: dict[int, int] = {}
        conflict = False
        for u, edges in internal.items():
            for v, w in edges:
                for i, c in enumerate(w):
                    phase = (distances[u]+i) % d
                    if phase in labels and labels[phase] != c:
                        conflict = True
                    labels[phase] = c
        if conflict:
            retained_components.append(component)
            for u in component:
                surviving[u] = sorted(set(internal[u]))
    anchors = {u for u in surviving if len(surviving[u]) > 1}
    for component in retained_components:
        if not (component & anchors):
            anchors.add(min(component))
    compressed: Graph = {u: [] for u in anchors}
    for u in anchors:
        for v, word in surviving[u]:
            letters = list(word)
            traversed = 0
            while v not in anchors:
                require(len(surviving[v]) == 1, "reference ambiguous chain")
                v, following = surviving[v][0]
                letters.extend(following)
                traversed += 1
                require(traversed <= len(surviving), "reference unanchored cycle")
            compressed[u].append((v, tuple(letters)))
    return compressed


def reference_bytes(g: Graph, product: int) -> bytes:
    parts = [b"WORDGR01", struct.pack("<QIQ", product, 4, len(g))]
    for u in sorted(g):
        edges = sorted(g[u])
        parts.append(struct.pack("<QI", u, len(edges)))
        for v, word in edges:
            parts.append(struct.pack("<QI", v, len(word)))
            parts.append(bytes(c+128 for c in word))
    return b"".join(parts)


def check_reference(directory: Path) -> list[dict[str, int]]:
    g = reference_initial()
    product = 1
    checked = []
    for stage, p in enumerate(PRIMES[:5]):
        if p != 1:
            g = reference_lift(g, product, p)
            product *= p
        for suffix in ("input", "output"):
            if suffix == "output":
                g = reference_prune(g)
            expected = reference_bytes(g, product)
            actual = (directory/f"{stage}_{suffix}.bin").read_bytes()
            require(expected == actual, f"Python reference mismatch at {stage}/{suffix}")
        checked.append({"stage": stage, "p": p,
                        "macro_vertices": len(g),
                        "macro_edges": sum(map(len, g.values()))})
    return checked


def compare_complete_graphs(a_dir: Path, b_dir: Path) -> list[dict[str, Any]]:
    records = []
    for stage in range(len(PRIMES)):
        for suffix in ("input", "output"):
            filename = f"{stage}_{suffix}.bin"
            ha, size = hashlib.sha256(), 0
            with (a_dir/filename).open("rb") as a, (b_dir/filename).open("rb") as b:
                while True:
                    left, right = a.read(1024*1024), b.read(1024*1024)
                    require(left == right, f"Graph bytes differ: {filename}, offset {size}")
                    if not left:
                        break
                    size += len(left)
                    ha.update(left)
            records.append({"name": filename, "bytes": size, "sha256": ha.hexdigest()})
    return records


def run_command(command: list[str], output: Path, error: Path, timeout: int,
                memory_mb: int) -> None:
    limiter = None
    if os.name == "posix" and memory_mb:
        import resource

        def limit_memory() -> None:
            n = memory_mb*1024*1024
            resource.setrlimit(resource.RLIMIT_AS, (n, n))
        limiter = limit_memory
    with output.open("wb") as out, error.open("wb") as err:
        completed = subprocess.run(command, stdout=out, stderr=err,
                                   timeout=timeout, preexec_fn=limiter)
    require(completed.returncode == 0,
            f"Command failed ({completed.returncode}); inspect {error}")


def load_stages(path: Path) -> list[dict[str, Any]]:
    lines = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    require(len(lines) == len(PRIMES)+1, f"Unexpected number of records in {path}")
    require(lines[-1] == {"success": True, "prime_product_with_2": 40112098026},
            f"No final success in {path}")
    for i, p in enumerate(PRIMES):
        require(lines[i]["stage"] == i and lines[i]["p"] == p,
                f"Incorrect stage order in {path}")
    return lines[:-1]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workdir", type=Path, help="A new directory; must not already exist")
    parser.add_argument("--cxx", default="g++", help="C++17 compiler")
    parser.add_argument("--timeout", type=int, default=600, help="Seconds per subprocess")
    parser.add_argument("--memory-mb", type=int, default=4096,
                        help="POSIX address-space cap per subprocess, 0 disables")
    parser.add_argument("--keep-graphs", action="store_true")
    args = parser.parse_args()
    require(args.timeout > 0 and args.memory_mb >= 0, "Invalid resource limit")
    if args.workdir is None:
        work = Path(tempfile.mkdtemp(prefix="floor_52_"))
    else:
        work = args.workdir.resolve()
        work.mkdir(parents=True, exist_ok=False)
    try:
        compiler = shutil.which(args.cxx)
        require(compiler is not None, "C++ compiler not found")
        for label, source in (("a", SOURCE_A), ("b", SOURCE_B)):
            cpp = work/f"construction_{label}.cpp"
            binary = work/f"construction_{label}"
            cpp.write_text(source, encoding="utf-8")
            run_command([compiler, "-std=c++17", "-O2", str(cpp), "-o", str(binary)],
                        work/f"compile_{label}.out", work/f"compile_{label}.err",
                        args.timeout, args.memory_mb)
            directory = work/f"raw_{label}"
            directory.mkdir()
            run_command([str(binary), str(directory)], work/f"run_{label}.jsonl",
                        work/f"run_{label}.err", args.timeout, args.memory_mb)
            print(f"Construction {label.upper()} completed", flush=True)
        a, b = load_stages(work/"run_a.jsonl"), load_stages(work/"run_b.jsonl")
        for stage in range(len(PRIMES)):
            for field in CHECK_FIELDS:
                require(a[stage][field] == b[stage][field],
                        f"Summary mismatch at stage {stage}: {field}")
        for field, value in EXPECTED_FINAL.items():
            require(b[-1][field] == value, f"Final baseline mismatch: {field}")
        files = compare_complete_graphs(work/"raw_a", work/"raw_b")
        reference = check_reference(work/"raw_a")
        report = {
            "success": True,
            "theorem": "For every xi>0 and N, some n>=max(N,1) has gcd(floor(xi*(5/2)^n),40112098026)>1.",
            "parameters": {"a": 5, "b": 2, "K": 4,
                           "primes": [2, 3, 7, 11, 13, 17, 19, 23, 29, 31]},
            "stages": [{k: v for k, v in row.items() if k != "seconds"} for row in b],
            "compared_files": files,
            "compared_bytes": sum(f["bytes"] for f in files),
            "comparison": "Direct equality of every byte of complete canonical input and output graphs at all ten stages; not just hashes or counts.",
            "python_reference_stages": reference,
            "input_vertex_total": sum(row["input_vertices"] for row in b),
            "input_edge_total": sum(row["input_edges"] for row in b),
            "source_sha256": {"A": hashlib.sha256(SOURCE_A.encode()).hexdigest(),
                              "B": hashlib.sha256(SOURCE_B.encode()).hexdigest()},
            "python": sys.version,
            "compiler": subprocess.check_output([compiler, "--version"], text=True).splitlines()[0],
            "lean_formalized": False,
            "provenance": "Separately coded algorithms, not a clean-room or independent-human-review claim.",
        }
        output = work/"verification.json"
        output.write_text(json.dumps(report, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
        if not args.keep_graphs:
            shutil.rmtree(work/"raw_a")
            shutil.rmtree(work/"raw_b")
        print(f"SUCCESS: complete comparison and Python checks passed.\nReport: {output}")
        return 0
    except Exception as exc:
        (work/"failure.json").write_text(json.dumps({"success": False,
            "status": "inconclusive/error", "error": str(exc)}, indent=2)+"\n")
        print(f"INCONCLUSIVE/ERROR: {exc}\nWork directory: {work}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
