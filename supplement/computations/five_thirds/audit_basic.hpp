// A checker for finite certificate operations. The producer supplies proposed
// partitions and contractions; the checker does not assume the SCC algorithm
// is correct. It verifies all-edge rank/phase conditions and recomputes the
// contracted graph by reverse dependency propagation.

#include <array>
#include <map>

struct AuditCounts {
 unsigned long long geometry=0, geometry_empty=0, lift_words=0, lift_edges=0,
 rank_edges=0, phase_letters=0, contracted_edges=0, interval_edges=0,
 interval_vertices=0, initial_edges=0, initial_candidates=0;
} audit_counts;
void insist(bool x,const char*message){if(!x)throw runtime_error(string("AUDIT: ")+message);}
I afloor(Wide n,I d){insist(d>0,"positive denominator");Wide q=n>=0?n/d:-((-n+d-1)/d);insist(q>=INT64_MIN&&q<=INT64_MAX,"audit integer range");return(I)q;}
I aceil(Wide n,I d){return -afloor(-n,d);}

void verify_initial(const Graph&g,const Pool&W,int K){
 vector<tuple<int,int,int>>want,have;insist(g.n()==K,"all initial vertices");
 for(int j=0;j<K;j++){
  insist(g.bounds[j].l<=afloor((Wide)D*j,K),"initial lower cell");
  insist(g.bounds[j].u>=aceil((Wide)D*(j+1),K),"initial upper cell");
  for(int k=0;k<K;k++)for(int c=1-W.b;c<W.a;c++){
   audit_counts.initial_candidates++;
   if(((c-(W.b-W.a))%2)==0&&gcd(abs(c),W.a*W.b)==1 && W.a*j-W.b*(k+1)<c*K&&c*K<W.a*(j+1)-W.b*k)want.emplace_back(j,k,c);
  }
 }
 insist(g.n()==K,"all initial vertices");
 for(auto&e:g.e){insist(W.seq[e.w].size()==1,"initial one-letter edge");have.emplace_back(e.u,e.v,(int)(unsigned char)W.seq[e.w][0]-128);}
 sort(want.begin(),want.end());sort(have.begin(),have.end());insist(want==have,"complete initial edges");audit_counts.initial_edges+=want.size();
}
// Forward reachable-set calculation, deliberately not the producer's forbidden
// starting-root recursion. Byte tables just accelerate a fixed permutation of
// the nonzero residues. All arithmetic is exact.
struct ForwardAudit {
 int a,b,p,bi,r,groups;map<int,vector<array<uint64_t,256>>> tables;
 ForwardAudit(int aa,int bb,int pp):a(aa),b(bb),p(pp),bi(0),groups((pp+7)/8){
  insist(p>=2&&p<=61,"audited prime range");for(int d=2;d*d<=p;d++)insist(p%d!=0,"prime input");for(int x=1;x<p;x++)if(b*x%p==1)bi=x;insist(bi>0&&a%p,"unit coefficients");r=a*bi%p;
 }
 const vector<array<uint64_t,256>>& table(int c){auto it=tables.find(c);if(it!=tables.end())return it->second;vector<array<uint64_t,256>>T(groups);
  for(int j=0;j<groups;j++)for(int mask=0;mask<256;mask++){uint64_t out=0;for(int k=0;k<8;k++)if(mask&(1<<k)){int q=8*j+k;if(q>=p)continue;int z=((a*q+c)*bi%p+p)%p;if(z)out|=uint64_t(1)<<z;}T[j][mask]=out;}
  return tables.emplace(c,move(T)).first->second;
 }
 vector<pair<int,int>> evaluate(const string&w){
  audit_counts.lift_words++;uint64_t alive=(uint64_t(1)<<p)-2;int alpha=1,beta=0;
  for(unsigned char ch:w){int c=(int)ch-128;auto&T=table(c);uint64_t next=0;for(int j=0;j<groups;j++)next|=T[j][(alive>>(8*j))&255];alive=next;
   beta=((a*beta+c)*bi%p+p)%p;alpha=alpha*r%p;if(!alive)return{};
  }
  vector<pair<int,int>>out;for(int q=1;q<p;q++){int z=(alpha*q+beta)%p;if(alive&(uint64_t(1)<<z))out.push_back({q,z});}return out;
 }
};
void verify_lift_graph(const Graph&in,const Graph&out,const Pool&W,int p,const vector<LiftData>&checked){
 size_t nraw=(size_t)in.n()*(p-1);vector<unsigned char>active(nraw,0);
 for(auto&e:in.e)for(auto qz:checked[e.w].qz){active[e.u*(p-1)+qz.first-1]=1;active[e.v*(p-1)+qz.second-1]=1;}
 vector<int>ids(nraw,-1);int nn=0;
 for(size_t j=0;j<nraw;j++)if(active[j]){ids[j]=nn;insist(nn<out.n(),"lift missing vertex");insist(out.bounds[nn]==in.bounds[j/(p-1)],"lift inherited interval");nn++;}
 insist(nn==out.n(),"lift complete vertices");vector<Edge>expected;expected.reserve(out.e.size());
 for(auto&e:in.e)for(auto qz:checked[e.w].qz)expected.push_back({ids[e.u*(p-1)+qz.first-1],ids[e.v*(p-1)+qz.second-1],e.w});
 auto less=[](Edge x,Edge y){return tie(x.u,x.v,x.w)<tie(y.u,y.v,y.w);};auto eq=[](Edge x,Edge y){return tie(x.u,x.v,x.w)==tie(y.u,y.v,y.w);};
 sort(expected.begin(),expected.end(),less);expected.erase(unique(expected.begin(),expected.end(),eq),expected.end());
 insist(expected.size()==out.e.size(),"lift edge count");for(size_t j=0;j<expected.size();j++)insist(eq(expected[j],out.e[j]),"complete lifted edge set");audit_counts.lift_edges+=expected.size();
}
void verify_reduction(const Graph&g,const Graph&out,const Pool&W,const vector<int>&cid,const vector<char>&keep,const vector<I>&h,const map<int,pair<I,string>>&cert){
 insist(cid.size()==g.bounds.size()&&h.size()==g.bounds.size(),"partition coverage");int n=g.n();bool has_retained=false;
 for(int u=0;u<n;u++){insist(cid[u]>=0&&cid[u]<(int)keep.size(),"block id");if(keep[cid[u]])has_retained=true;}
 for(auto&e:g.e){audit_counts.rank_edges++;int s=cid[e.u],t=cid[e.v];if(s!=t){insist(s<t,"strict inter-block rank");continue;}if(keep[s])continue;
  auto it=cert.find(s);insist(it!=cert.end(),"unjustified removed internal edge");I d=it->second.first;auto&label=it->second.second;insist(d>0&&label.size()==(size_t)d,"positive certified period");
  auto&word=W.seq[e.w];insist(h[e.u]>=0&&h[e.v]>=0,"nonnegative phase certificates");insist((h[e.u]+(I)word.size()-h[e.v])%d==0,"all-edge phase advance");
  for(size_t j=0;j<word.size();j++){insist(word[j]==label[(h[e.u]+j)%d],"all-letter phase label");audit_counts.phase_letters++;}
 }
 if(!has_retained){insist(out.n()==0&&out.e.empty(),"empty retained graph");return;}
 vector<int>degree(n,0),single(n,-1),ids(n,-1),destination(n,-1),head(n,-1),next(n,-1);vector<int>queue;
 for(int i=0;i<(int)g.e.size();i++){auto&e=g.e[i];if(cid[e.u]==cid[e.v]&&keep[cid[e.u]]){degree[e.u]++;single[e.u]=i;}}
 int nn=0;for(int u=0;u<n;u++)if(degree[u]>=2){ids[u]=nn;destination[u]=u;queue.push_back(u);insist(nn<out.n()&&out.bounds[nn]==g.bounds[u],"macro vertex and interval");nn++;}
 insist(nn==out.n(),"complete macro vertices");
 for(int u=0;u<n;u++)if(degree[u]==1){int v=g.e[single[u]].v;next[u]=head[v];head[v]=u;}
 for(size_t i=0;i<queue.size();i++){int v=queue[i];for(int u=head[v];u!=-1;u=next[u]){insist(destination[u]==-1,"functional dependency repeated");destination[u]=destination[v];queue.push_back(u);}}
 for(int u=0;u<n;u++)if(degree[u])insist(destination[u]>=0,"unaccounted functional cycle");
 vector<Edge>expected;expected.reserve(out.e.size());
 for(auto&e:g.e)if(ids[e.u]>=0&&cid[e.u]==cid[e.v]&&keep[cid[e.u]]){
  int v=e.v;string text=W.seq[e.w];while(ids[v]<0){auto&t=g.e[single[v]];text+=W.seq[t.w];v=t.v;}
  insist(v==destination[e.v],"macro terminal dependency");auto it=W.ids.find(text);insist(it!=W.ids.end(),"contracted output word missing");expected.push_back({ids[e.u],ids[v],it->second});
 }
 auto less=[](Edge x,Edge y){return tie(x.u,x.v,x.w)<tie(y.u,y.v,y.w);};auto eq=[](Edge x,Edge y){return tie(x.u,x.v,x.w)==tie(y.u,y.v,y.w);};
 sort(expected.begin(),expected.end(),less);expected.erase(unique(expected.begin(),expected.end(),eq),expected.end());insist(expected.size()==out.e.size(),"contracted edge count");
 for(size_t j=0;j<expected.size();j++)insist(eq(expected[j],out.e[j]),"every contracted edge");audit_counts.contracted_edges+=expected.size();
}



void print_audit_counts(){cout<<",\"audit\":{\"geometry\":"<<audit_counts.geometry<<",\"geometry_empty\":"<<audit_counts.geometry_empty<<",\"lift_words\":"<<audit_counts.lift_words<<",\"lift_edges\":"<<audit_counts.lift_edges<<",\"rank_edges\":"<<audit_counts.rank_edges<<",\"phase_letters\":"<<audit_counts.phase_letters<<",\"contracted_edges\":"<<audit_counts.contracted_edges<<",\"interval_edges\":"<<audit_counts.interval_edges<<",\"interval_vertices\":"<<audit_counts.interval_vertices<<",\"initial_edges\":"<<audit_counts.initial_edges<<",\"initial_candidates\":"<<audit_counts.initial_candidates<<"}";}
