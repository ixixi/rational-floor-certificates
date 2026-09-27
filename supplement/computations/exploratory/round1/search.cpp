#include <algorithm>
#include <chrono>
#include <climits>
#include <cmath>
#include <deque>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
struct Edge{int u,v; vector<int>w;};
struct Graph{int n; vector<Edge> e; vector<pair<long long,long long>> bounds;};
long long DEN;
size_t edgecap=400000, lettercap=30000000; int wordcap=12000;
long long floordiv(long long a,long long b){long long q=a/b; if(a%b<0)--q; return q;}
int mod(long long x,int p){return (x%p+p)%p;}
int inv(int b,int p){for(int i=1;i<p;i++)if((long long)i*b%p==1)return i;throw runtime_error("inverse");}
bool eless(const Edge& a,const Edge& b){if(a.u!=b.u)return a.u<b.u;if(a.v!=b.v)return a.v<b.v;return a.w<b.w;}
bool eq(const Edge& a,const Edge& b){return a.u==b.u&&a.v==b.v&&a.w==b.w;}
void normalize(Graph&g){sort(g.e.begin(),g.e.end(),eless);g.e.erase(unique(g.e.begin(),g.e.end(),eq),g.e.end());}
void cap(const Graph&g){if(g.e.size()>edgecap)throw runtime_error("edge_cap");size_t n=0;for(auto&e:g.e){n+=e.w.size();if(e.w.size()>(size_t)wordcap)throw runtime_error("word_cap");}if(n>lettercap)throw runtime_error("letter_cap");}
Graph init(int a,int b,int K, vector<int>&cs){Graph g;g.n=K;for(int j=0;j<K;j++)g.bounds.push_back({DEN/K*j,DEN/K*(j+1)});for(int j=0;j<K;j++)for(int c:cs){int low=max(0LL,floordiv((long long)a*j-(long long)c*K,b));int hi=min((long long)K-1,floordiv((long long)a*(j+1)-(long long)c*K-1,b));for(int k=low;k<=hi;k++)g.e.push_back({j,k,{c}});}normalize(g);cap(g);return g;}
struct Report{int n,e,cyclic,certified,retained,outn,oute,maxlen;size_t letters;};
Graph simplify(Graph const&g,Report&r){r={g.n,(int)g.e.size(),0,0,0,0,0,0,0};
 vector<vector<int>> adj(g.n),rev(g.n);for(int i=0;i<(int)g.e.size();i++){auto&e=g.e[i];adj[e.u].push_back(i);rev[e.v].push_back(i);}
 vector<char>seen(g.n,0);vector<int>order;order.reserve(g.n);
 for(int root=0;root<g.n;root++)if(!seen[root]){vector<pair<int,int>>s;seen[root]=1;s.push_back({root,0});while(!s.empty()){int u=s.back().first;int &i=s.back().second;if(i==(int)adj[u].size()){order.push_back(u);s.pop_back();}else{int v=g.e[adj[u][i++]].v;if(!seen[v]){seen[v]=1;s.push_back({v,0});}}}}
 vector<int>cid(g.n,-1);vector<vector<int>>members;
 for(auto it=order.rbegin();it!=order.rend();++it)if(cid[*it]<0){int id=members.size();members.push_back({});vector<int>s={*it};cid[*it]=id;while(!s.empty()){int u=s.back();s.pop_back();members[id].push_back(u);for(int ei:rev[u]){int v=g.e[ei].u;if(cid[v]<0){cid[v]=id;s.push_back(v);}}}}
 vector<vector<int>>internal(members.size());for(int i=0;i<(int)g.e.size();i++)if(cid[g.e[i].u]==cid[g.e[i].v])internal[cid[g.e[i].u]].push_back(i);
 vector<char>keep(members.size(),0);vector<long long>h(g.n,-1);
 for(int id=0;id<(int)members.size();id++)if(!internal[id].empty()){
  r.cyclic++;int root=members[id][0];h[root]=0;vector<int>q={root};for(size_t i=0;i<q.size();i++){int u=q[i];for(int ei:adj[u]){auto&e=g.e[ei];if(cid[e.v]==id&&h[e.v]<0){h[e.v]=h[u]+e.w.size();q.push_back(e.v);}}}
  if(q.size()!=members[id].size())throw runtime_error("scc_reachability");long long d=0;for(int ei:internal[id]){auto&e=g.e[ei];d=gcd(d,llabs(h[e.u]+(long long)e.w.size()-h[e.v]));}
  if(d<=0)throw runtime_error("period");if(d>50000000)throw runtime_error("phase_cap");
  const int NONE=1000000000;vector<int>lab(d,NONE);bool ok=true;
  for(int ei:internal[id]){auto&e=g.e[ei];for(size_t t=0;t<e.w.size();t++){int s=(h[e.u]+t)%d;int c=e.w[t];if(lab[s]!=NONE&&lab[s]!=c){ok=false;break;}lab[s]=c;}if(!ok)break;}
  if(ok)r.certified++;else{keep[id]=1;r.retained+=members[id].size();}
 }
 // Retain ALL internal edges of all unverified cyclic SCCs.
 vector<vector<int>>out(g.n);for(int i=0;i<(int)g.e.size();i++){auto&e=g.e[i];if(cid[e.u]==cid[e.v]&&keep[cid[e.u]])out[e.u].push_back(i);}
 vector<int>newid(g.n,-1);int nn=0;for(int u=0;u<g.n;u++)if(out[u].size()>=2)newid[u]=nn++;
 // With a full phase test, every retained SCC has a branching vertex.
 for(int id=0;id<(int)members.size();id++)if(keep[id]){bool found=false;for(int u:members[id])if(newid[u]>=0)found=true;if(!found)throw runtime_error("retained_functional_component");}
 Graph ans;ans.n=nn;ans.bounds.resize(nn);for(int u=0;u<g.n;u++)if(newid[u]>=0)ans.bounds[newid[u]]=g.bounds[u];size_t letters=0;
 for(int u=0;u<g.n;u++)if(newid[u]>=0)for(int ei:out[u]){vector<int>w=g.e[ei].w;int v=g.e[ei].v;int steps=0;while(newid[v]<0){if(out[v].size()!=1)throw runtime_error("contraction_outdegree");auto&e=g.e[out[v][0]];w.insert(w.end(),e.w.begin(),e.w.end());v=e.v;if(w.size()>(size_t)wordcap)throw runtime_error("word_cap");if(++steps>g.n)throw runtime_error("contraction_cycle");}letters+=w.size();if(letters>lettercap)throw runtime_error("letter_cap");ans.e.push_back({newid[u],newid[v],move(w)});}
 normalize(ans);cap(ans);r.outn=ans.n;r.oute=ans.e.size();for(auto&e:ans.e){r.maxlen=max(r.maxlen,(int)e.w.size());r.letters+=e.w.size();}return ans;
}
Graph lift(Graph const&g,int a,int b,int p){Graph ans;if((long long)g.n*(p-1)>INT_MAX)throw runtime_error("index_cap");ans.n=g.n*(p-1);int ai=inv(a%p,p),bi=inv(b%p,p);size_t letters=0;
 for(auto&e:g.e){vector<char>forbidden(p,0);forbidden[0]=1;int root=0,coef=ai;int alpha=1,beta=0;
  for(int c:e.w){root=mod(root-(long long)c*coef,p);forbidden[root]=1;coef=(long long)coef*b%p*ai%p;alpha=(long long)alpha*a%p*bi%p;beta=mod((long long)a*beta+c,p)*bi%p;}
  for(int q=1;q<p;q++)if(!forbidden[q]){int z=mod((long long)alpha*q+beta,p);if(!z)throw runtime_error("root_end");ans.e.push_back({e.u*(p-1)+q-1,e.v*(p-1)+z-1,e.w});letters+=e.w.size();if(ans.e.size()>edgecap)throw runtime_error("edge_cap");if(letters>lettercap)throw runtime_error("letter_cap");}
 }
 // Remove isolated vertices and canonically relabel in old index order.
 vector<int>ids(ans.n,-1);for(auto&e:ans.e){ids[e.u]=0;ids[e.v]=0;}int nn=0;for(int&i:ids)if(i==0)i=nn++;for(auto&e:ans.e){e.u=ids[e.u];e.v=ids[e.v];}ans.n=nn;ans.bounds.resize(nn);for(int i=0;i<(int)ids.size();i++)if(ids[i]>=0)ans.bounds[ids[i]]=g.bounds[i/(p-1)];normalize(ans);return ans;
}
vector<int>parse(string s){vector<int>v;stringstream ss(s);string x;while(getline(ss,x,','))if(!x.empty())v.push_back(stoi(x));return v;}
pair<int,int> tighten(Graph &g,int a,int b){
 int rounds=0,deleted=0;
 for(int z=0;z<300;z++){
  vector<pair<long long,long long>> nb(g.n,{DEN,0}),ni(g.n,{DEN,0});vector<Edge>kept;kept.reserve(g.e.size());
  for(auto&e:g.e){long long L=g.bounds[e.v].first,U=g.bounds[e.v].second;
   if(L>=U){deleted++;continue;}
   for(auto it=e.w.rbegin();it!=e.w.rend();++it){int c=*it;
    L=max(0LL,floordiv(b*L+(long long)c*DEN,a));
    U=min(DEN,-floordiv(-(b*U+(long long)c*DEN),a));
    if(L>=U)break;
   }
   L=max(L,g.bounds[e.u].first);U=min(U,g.bounds[e.u].second);
   if(L>=U){deleted++;continue;}
   
   long long X=g.bounds[e.u].first,Y=g.bounds[e.u].second;
   for(int c:e.w){X=max(0LL,floordiv(a*X-(long long)c*DEN,b));Y=min(DEN,-floordiv(-(a*Y-(long long)c*DEN),b));if(X>=Y)break;}
   X=max(X,g.bounds[e.v].first);Y=min(Y,g.bounds[e.v].second);
   if(X>=Y){deleted++;continue;}
   nb[e.u].first=min(nb[e.u].first,L);nb[e.u].second=max(nb[e.u].second,U);
   ni[e.v].first=min(ni[e.v].first,X);ni[e.v].second=max(ni[e.v].second,Y);
   kept.push_back(move(e));
  }
  for(int u=0;u<g.n;u++){nb[u].first=max(nb[u].first,ni[u].first);nb[u].second=min(nb[u].second,ni[u].second);}bool changed=nb!=g.bounds;g.bounds=move(nb);g.e=move(kept);rounds++;
  if(!changed)break;
 }
 return {rounds,deleted};
}
void dump(const Graph&g,string path){ofstream f(path);f<<g.n<<" "<<g.e.size()<<" "<<DEN<<"\n";for(auto q:g.bounds)f<<q.first<<" "<<q.second<<"\n";for(auto&e:g.e){f<<e.u<<" "<<e.v<<" "<<e.w.size();for(int c:e.w)f<<" "<<c;f<<"\n";}}
int main(int argc,char**argv){if(argc<5){cerr<<"Usage: search a b K prime-list [edgecap] [dump-prefix]\n";return 1;}int a=stoi(argv[1]),b=stoi(argv[2]),K=stoi(argv[3]);auto primes=parse(argv[4]);if(argc>=6)edgecap=stoull(argv[5]);string prefix=argc>=7?argv[6]:"";if(!(a>b&&b>=2&&gcd(a,b)==1&&K>0&&a<=200&&K<=65536)){cerr<<"Require coprime 2 <= b < a <= 200 and 1 <= K <= 65536.\n";return 2;}
 set<int> used;for(int p:primes){bool prime=p>=2&&p<=997;for(int d=2;(long long)d*d<=p&&prime;d++)if(p%d==0)prime=false;if(!prime||!used.insert(p).second){cerr<<"Prime list must contain distinct primes <= 997.\n";return 2;}}
 DEN=(long long)K*(1LL<<32);
 vector<int>cs;for(int c=1-b;c<a;c++)if(mod(c-b+a,2)==0&&gcd(abs(c),a*b)==1)cs.push_back(c);
 cout<<"{\"a\":"<<a<<",\"b\":"<<b<<",\"K\":"<<K<<",\"alphabet\":[";for(size_t i=0;i<cs.size();i++)cout<<(i?",":"")<<cs[i];cout<<"],\"stages\":[";bool first=true;auto begin=chrono::steady_clock::now();
 try{Graph g=init(a,b,K,cs);vector<int>ps={0};for(int p:primes)if((2*a*b)%p)ps.push_back(p);bool success=false;int stage=0;for(int p:ps){if(p)g=lift(g,a,b,p);if(!prefix.empty())dump(g,prefix+"_"+to_string(stage)+"_in.txt");Report r;Graph s=simplify(g,r);int rounds=0,deleted=0;
 for(int rep=0;rep<50&&s.n;rep++){
  auto [rr,dd]=tighten(s,a,b);rounds+=rr;deleted+=dd;
  if(!dd)break;
  Report r2;s=simplify(s,r2);
 }
 r.outn=s.n;r.oute=s.e.size();r.maxlen=0;r.letters=0;for(auto&e:s.e){r.maxlen=max(r.maxlen,(int)e.w.size());r.letters+=e.w.size();}
 if(!prefix.empty())dump(s,prefix+"_"+to_string(stage)+"_out.txt");cout<<(first?"":",")<<"{\"p\":"<<p<<",\"vin\":"<<r.n<<",\"ein\":"<<r.e<<",\"cyclic\":"<<r.cyclic<<",\"certified\":"<<r.certified<<",\"retained\":"<<r.retained<<",\"vout\":"<<r.outn<<",\"eout\":"<<r.oute<<",\"maxlen\":"<<r.maxlen<<",\"letters\":"<<r.letters<<",\"bounds_rounds\":"<<rounds<<",\"bounds_deletions\":"<<deleted<<"}";cout.flush();first=false;g=move(s);stage++;if(g.n==0){success=true;break;}}
 cout<<"],\"status\":\""<<(success?"success":"budget_exhausted")<<"\"";
 }catch(const exception&e){cout<<"],\"status\":\""<<e.what()<<"\"";}
 cout<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<"}\n";
}
