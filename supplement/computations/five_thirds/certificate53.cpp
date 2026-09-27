#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include <map>
#include <tuple>
using namespace std;
using I=long long;using Wide=__int128_t;
I D=1; // Fixed denominator K for the original uniform fractional cells.
I fd(Wide a,I b){Wide q=a/b;if(a%b<0)--q;if(q<INT64_MIN||q>INT64_MAX)throw runtime_error("integer_range");return(I)q;}
I cd(Wide a,I b){return -fd(-a,b);}
int mod(I x,int p){return (x%p+p)%p;}
int inv(int x,int p){for(int i=1;i<p;i++)if(i*x%p==1)return i;throw runtime_error("inverse");}
size_t ECAP=10000000,VCAP=32000000;int WCAP=20000;
struct Bounds{I l,u;bool operator==(Bounds const&o)const{return l==o.l&&u==o.u;}};
Bounds intersect(Bounds x,Bounds y){return{max(x.l,y.l),min(x.u,y.u)};}
bool nonempty(Bounds x){return x.l<x.u;}

struct Sequences{
 vector<const string*> entries;
 const string&operator[](size_t i)const{return *entries[i];}
 size_t size()const{return entries.size();}
 void push_back(const string*ptr){entries.push_back(ptr);}
};

struct Pool{
 Sequences seq;unordered_map<string,int> ids;vector<int> reversed;int a,b;
 Pool(int aa,int bb):a(aa),b(bb){}
 int intern(string s){auto it=ids.find(s);if(it!=ids.end())return it->second; if(s.size()>(size_t)WCAP)throw runtime_error("word_cap");int id=seq.size();auto pair=ids.emplace(move(s),id);seq.push_back(&pair.first->first);reversed.push_back(-1);return id;}
 int one(int c){return intern(string(1,char(c+128)));}
 int rev(int w){if(reversed[w]>=0)return reversed[w];string s=seq[w];reverse(s.begin(),s.end());int j=intern(move(s));for(size_t k=0;k<seq[w].size();k++)if(seq[j][k]!=seq[w][seq[w].size()-1-k])throw runtime_error("AUDIT: reversal");reversed[w]=j;reversed[j]=w;return j;}

};
struct Edge{int u,v,w;};
struct Graph{vector<Bounds> bounds;vector<Edge> e;int n()const{return bounds.size();}};
struct LiftData{vector<pair<int,int>> qz;};
#include "audit_basic.hpp"
void checkcap(Graph const&g){if(g.e.size()>ECAP)throw runtime_error("edge_cap");if(g.bounds.size()>VCAP)throw runtime_error("vertex_cap");}
void norm(Graph&g){sort(g.e.begin(),g.e.end(),[](auto&x,auto&y){if(x.u!=y.u)return x.u<y.u;if(x.v!=y.v)return x.v<y.v;return x.w<y.w;});g.e.erase(unique(g.e.begin(),g.e.end(),[](auto&x,auto&y){return x.u==y.u&&x.v==y.v&&x.w==y.w;}),g.e.end());checkcap(g);}
Graph initial(Pool&W,int K){Graph g;int a=W.a,b=W.b;for(int j=0;j<K;j++)g.bounds.push_back({fd((Wide)D*j,K),cd((Wide)D*(j+1),K)});
 for(int c=1-b;c<a;c++)if(mod(c-b+a,2)==0&&gcd(abs(c),a*b)==1){int w=W.one(c);for(int j=0;j<K;j++){int lo=max(0LL,fd((I)a*j-(I)c*K,b)),hi=min((I)K-1,fd((I)a*(j+1)-(I)c*K-1,b));for(int k=lo;k<=hi;k++)g.e.push_back({j,k,w});}}
 norm(g);verify_initial(g,W,K);return g;
}
struct CSR{vector<int> off,ei;CSR(Graph const&g,bool back){off.resize(g.n()+1);ei.resize(g.e.size());for(auto&e:g.e)off[(back?e.v:e.u)+1]++;partial_sum(off.begin(),off.end(),off.begin());vector<int>cur=off;for(int j=0;j<(int)g.e.size();j++){auto&e=g.e[j];ei[cur[back?e.v:e.u]++]=j;}}};
struct Stats{int n=0,m=0,cyclic=0,certified=0,retained=0;};
Graph simplify(Graph const&g,Pool&W,Stats &st){
 st={g.n(),(int)g.e.size(),0,0,0};int n=g.n();CSR adj(g,false),rev(g,true);
 vector<char>seen(n,0);vector<int>order;order.reserve(n);vector<pair<int,int>>stack;
 for(int rt=0;rt<n;rt++)if(!seen[rt]){seen[rt]=1;stack.push_back({rt,adj.off[rt]});while(!stack.empty()){int u=stack.back().first;int &at=stack.back().second;if(at==adj.off[u+1]){order.push_back(u);stack.pop_back();}else{int v=g.e[adj.ei[at++]].v;if(!seen[v]){seen[v]=1;stack.push_back({v,adj.off[v]});}}}}
 vector<int>cid(n,-1),members,starts;members.reserve(n);vector<int>q;
 for(auto it=order.rbegin();it!=order.rend();++it)if(cid[*it]<0){int id=starts.size();starts.push_back(members.size());cid[*it]=id;q={*it};while(!q.empty()){int u=q.back();q.pop_back();members.push_back(u);for(int j=rev.off[u];j<rev.off[u+1];j++){int v=g.e[rev.ei[j]].u;if(cid[v]<0){cid[v]=id;q.push_back(v);}}}}
 int nc=starts.size();starts.push_back(n);vector<int>intern(nc,0);for(auto&e:g.e)if(cid[e.u]==cid[e.v])intern[cid[e.u]]++;
 vector<char>keep(nc,0);vector<I>h(n,-1);vector<int>lab;map<int,pair<I,string>>cert;
 for(int id=0;id<nc;id++)if(intern[id]){
  st.cyclic++;int root=members[starts[id]];h[root]=0;q={root};for(size_t t=0;t<q.size();t++){int u=q[t];for(int j=adj.off[u];j<adj.off[u+1];j++){auto&e=g.e[adj.ei[j]];if(cid[e.v]==id&&h[e.v]<0){h[e.v]=h[u]+W.seq[e.w].size();q.push_back(e.v);}}}
  if(q.size()!=(size_t)(starts[id+1]-starts[id]))throw runtime_error("scc_reach");
  I d=0;for(int u:q)for(int j=adj.off[u];j<adj.off[u+1];j++){auto&e=g.e[adj.ei[j]];if(cid[e.v]==id)d=gcd(d,llabs(h[u]+(I)W.seq[e.w].size()-h[e.v]));}
  if(d<=0||d>200000000)throw runtime_error("phase_limit");lab.assign(d,-1000);bool ok=true;
  for(int u:q){for(int j=adj.off[u];j<adj.off[u+1]&&ok;j++){auto&e=g.e[adj.ei[j]];if(cid[e.v]!=id)continue;I phase=h[u]%d;for(unsigned char ch:W.seq[e.w]){int c=(int)ch-128;if(lab[phase]!=-1000&&lab[phase]!=c){ok=false;break;}lab[phase]=c;if(++phase==d)phase=0;}}if(!ok)break;}
  if(ok){st.certified++;string labels;for(int c:lab)labels+=char(c+128);cert[id]={d,move(labels)};}else{keep[id]=1;st.retained+=q.size();}
 }
 vector<int>outdegree(n,0),sole(n,-1),ids(n,-1);for(int j=0;j<(int)g.e.size();j++){auto&e=g.e[j];if(cid[e.u]==cid[e.v]&&keep[cid[e.u]]){outdegree[e.u]++;sole[e.u]=j;}}
 Graph s;for(int u=0;u<n;u++)if(outdegree[u]>=2){ids[u]=s.n();s.bounds.push_back(g.bounds[u]);}
 for(auto&e:g.e)if(ids[e.u]>=0&&cid[e.u]==cid[e.v]&&keep[cid[e.u]]){
  int v=e.v,w=e.w;if(ids[v]<0){string word=W.seq[w];int steps=0;while(ids[v]<0){if(outdegree[v]!=1)throw runtime_error("functional_retained");auto&t=g.e[sole[v]];word+=W.seq[t.w];v=t.v;if(word.size()>(size_t)WCAP||++steps>n)throw runtime_error("chain_limit");}w=W.intern(move(word));}
  s.e.push_back({ids[e.u],ids[v],w});
 }
 norm(s);verify_reduction(g,s,W,cid,keep,h,cert);return s;
}
void reverse_graph(Graph&g,Pool&W){for(auto&e:g.e){swap(e.u,e.v);e.w=W.rev(e.w);}norm(g);}
Graph both(Graph g,Pool&W){Stats t;for(int rep=0;rep<10&&g.n();rep++){int nn=g.n();reverse_graph(g,W);g=simplify(g,W,t);reverse_graph(g,W);g=simplify(g,W,t);if(g.n()==nn)break;}return g;}



Stats stage_statistics;
Graph reduce(Graph g,Pool&W,int bidir=1){Stats st;g=simplify(g,W,st);stage_statistics=st;if(bidir)g=both(move(g),W);return g;}
Graph lift(Graph const&g,Pool&W,int p){ForwardAudit audit(W.a,W.b,p);int a=W.a,b=W.b;Graph s;I vcount=(I)g.n()*(p-1);if(vcount>INT32_MAX)throw runtime_error("index_cap");vector<LiftData>data(W.seq.size());vector<char>ready(W.seq.size(),0);int ai=inv(a%p,p),bi=inv(b%p,p);
 for(auto&e:g.e){if(!ready[e.w]){auto&seq=W.seq[e.w];vector<char>bad(p,0);bad[0]=1;int root=0,coef=ai,alpha=1,beta=0;for(unsigned char ch:seq){int c=(int)ch-128;root=mod(root-(I)c*coef,p);bad[root]=1;coef=(I)coef*b%p*ai%p;alpha=(I)alpha*a%p*bi%p;beta=(I)mod((I)a*beta+c,p)*bi%p;}
   for(int q=1;q<p;q++)if(!bad[q]){int z=mod((I)alpha*q+beta,p);if(!z)throw runtime_error("zero_lift");data[e.w].qz.push_back({q,z});}insist(audit.evaluate(W.seq[e.w])==data[e.w].qz,"all forward-reachable starting residues");ready[e.w]=1;}
  for(auto qz:data[e.w].qz){s.e.push_back({e.u*(p-1)+qz.first-1,e.v*(p-1)+qz.second-1,e.w});if(s.e.size()>ECAP)throw runtime_error("edge_cap");}
 }
 vector<int>ids(vcount,-1);for(auto&e:s.e){ids[e.u]=0;ids[e.v]=0;}for(int i=0;i<(int)ids.size();i++)if(ids[i]==0){ids[i]=s.n();s.bounds.push_back(g.bounds[i/(p-1)]);if(s.bounds.size()>VCAP)throw runtime_error("vertex_cap");}
 for(auto&e:s.e){e.u=ids[e.u];e.v=ids[e.v];}norm(s);verify_lift_graph(g,s,W,p,data);return s;
}

vector<int>parse(string s){stringstream ss(s);string x;vector<int>v;while(getline(ss,x,','))if(!x.empty())v.push_back(stoi(x));return v;}
void dump(Graph const&g,Pool const&W,string filename){ofstream f(filename);f<<g.n()<<" "<<g.e.size()<<" "<<D<<"\n";for(auto x:g.bounds)f<<x.l<<" "<<x.u<<"\n";for(auto&e:g.e){auto&w=W.seq[e.w];f<<e.u<<" "<<e.v<<" "<<w.size();for(unsigned char c:w)f<<" "<<(int)c-128;f<<"\n";}}
void collect(Graph&g,Pool&W){
 Pool next(W.a,W.b);vector<int>id(W.seq.size(),-1);
 for(auto&e:g.e){if(id[e.w]<0){int nw=next.intern(W.seq[e.w]);id[e.w]=nw;}insist(next.seq[id[e.w]]==W.seq[e.w],"word collection identity");e.w=id[e.w];}
 W=move(next);norm(g);
}
int main(int argc,char**argv){if(argc<5){cerr<<"fast_search a b K primes [edgecap] [prefix]\n";return 1;}
 int a=stoi(argv[1]),b=stoi(argv[2]),K=stoi(argv[3]);if(!(a>b&&b>=2&&a<=127&&gcd(a,b)==1&&K>=1&&K<=65536))return 2;D=K;Pool W(a,b);if(argc>5)ECAP=stoull(argv[5]);string prefix=argc>6?argv[6]:"";int bidir=getenv("BIDIR")?atoi(getenv("BIDIR")):1;int splits=0;
 auto primes=parse(argv[4]);vector<int>ps={0};for(int p:primes){bool prime=p>=2;for(int j=2;j*j<=p;j++)if(p%j==0)prime=false;if(!prime)return 3;if((2*a*b)%p)ps.push_back(p);}auto start=chrono::steady_clock::now();
 cout<<"{\"a\":"<<a<<",\"b\":"<<b<<",\"K\":"<<K<<",\"D\":"<<D<<",\"bidir\":"<<bidir<<",\"splits\":"<<splits<<",\"stages\":[";bool first=true;
 try{Graph g=initial(W,K);int stage=0;for(int p:ps){if(p)g=lift(g,W,p);int ni=g.n(),ei=g.e.size();if(prefix.size())dump(g,W,prefix+"_"+to_string(stage)+"_in.txt");g=reduce(move(g),W,bidir);
  size_t letters=0,maxlen=0;for(auto&e:g.e){letters+=W.seq[e.w].size();maxlen=max(maxlen,W.seq[e.w].size());}cout<<(first?"":",")<<"{\"p\":"<<p<<",\"vin\":"<<ni<<",\"ein\":"<<ei<<",\"cyclic\":"<<stage_statistics.cyclic<<",\"certified\":"<<stage_statistics.certified<<",\"retained\":"<<stage_statistics.retained<<",\"vout\":"<<g.n()<<",\"eout\":"<<g.e.size()<<",\"letters\":"<<letters<<",\"maxlen\":"<<maxlen<<",\"unique_words\":"<<W.seq.size()<<"}";cout.flush();first=false;
  if(prefix.size())dump(g,W,prefix+"_"+to_string(stage)+"_out.txt");stage++;if(!g.n())break;collect(g,W);
 }
 cout<<"],\"status\":\""<<(g.n()?"budget_exhausted":"success")<<"\"";
 }catch(exception const&e){cout<<"],\"status\":\""<<e.what()<<"\"";}
 print_audit_counts();cout<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"}\n";return 0;
}
