// wgb.cpp — Independent implementation B of the word-graph method.
// Written from the mathematical specification in proofs/audit-02-word-method.md
// (sections 2-7, 14) without reading implementation A or the bundled code.
// Standard library only.  Build: g++ -O2 -std=c++17 -o wgb wgb.cpp
//
// Modes:
//   wgb pipeline --a A --b B --K K --carries c1,c2,... --primes p1,p2,... --out DIR [--stop-after k]
//   wgb q75 --a A --b B --M M --K K --carries ... --out DIR
//
// Pipeline: G0_in = initial one-step graph (direct strict inequalities);
//   for k = 0..s: G_k_out = Contract(Remove(G_k_in)); G_{k+1}_in = Lift_{p_{k+1}}(G_k_out).
//   Writes stage<k>_input.txt / stage<k>_output.txt in the normalised WORDGRAPH 2 format
//   and prints one JSON line per stage with the counts.
// Q75: full one-step graph on V(M,K) (gcd(q,M)=1), blocks = SCCs, period/phase, rho/eta.

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>
#include <numeric>
#include <utility>
#include <chrono>

using namespace std;
typedef unsigned long long u64;
typedef long long i64;
typedef unsigned int u32;

static double now_sec() {
    using namespace std::chrono;
    return duration<double>(steady_clock::now().time_since_epoch()).count();
}

[[noreturn]] static void die(const string& msg) {
    fprintf(stderr, "ERROR: %s\n", msg.c_str());
    printf("{\"event\":\"error\",\"message\":\"%s\"}\n", msg.c_str());
    fflush(stdout);
    exit(2);
}

// ---------------------------------------------------------------- graph
struct Graph {
    u64 modulus = 1;          // P = product of used primes (1 initially)
    vector<u64> primes;       // used primes in order
    u32 K = 0;
    vector<u64> vq;           // vertex name q (0 <= q < modulus)
    vector<u32> vcell;        // vertex name cell (0 <= cell < K)
    vector<u32> eu, ev;       // edge endpoints (vertex ids)
    vector<u64> ewoff;        // offset of word in chars
    vector<u32> ewlen;        // word length (>= 1)
    vector<u64> emult;        // multiplicity: number of duplicate triples merged into this edge (reporting only)
    vector<int8_t> chars;     // concatenated words
    size_t nv() const { return vq.size(); }
    size_t ne() const { return eu.size(); }
    const int8_t* word(size_t e) const { return chars.data() + ewoff[e]; }
};

// lexicographic comparison of two words (shorter prefix first)
static int cmp_word(const int8_t* a, u32 la, const int8_t* b, u32 lb) {
    u32 m = la < lb ? la : lb;
    for (u32 i = 0; i < m; ++i) {
        if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
    }
    if (la == lb) return 0;
    return la < lb ? -1 : 1;
}

// Sort vertices by (q,cell), renumber, optionally drop vertices without incident edges,
// sort edges by (u,v,word), remove duplicate triples.  Verifies that vertex names are unique.
static void normalize(Graph& g, bool drop_isolated) {
    size_t n = g.nv();
    vector<u32> perm(n);
    iota(perm.begin(), perm.end(), 0);
    if (drop_isolated) {
        vector<char> used(n, 0);
        for (size_t e = 0; e < g.ne(); ++e) { used[g.eu[e]] = 1; used[g.ev[e]] = 1; }
        vector<u32> keep;
        keep.reserve(n);
        for (u32 i = 0; i < n; ++i) if (used[i]) keep.push_back(i);
        perm.swap(keep);
    }
    sort(perm.begin(), perm.end(), [&](u32 x, u32 y) {
        if (g.vq[x] != g.vq[y]) return g.vq[x] < g.vq[y];
        return g.vcell[x] < g.vcell[y];
    });
    for (size_t i = 1; i < perm.size(); ++i)
        if (g.vq[perm[i]] == g.vq[perm[i - 1]] && g.vcell[perm[i]] == g.vcell[perm[i - 1]])
            die("duplicate vertex name after normalisation");
    vector<u32> newid(n, 0xFFFFFFFFu);
    vector<u64> nq(perm.size());
    vector<u32> nc(perm.size());
    for (u32 i = 0; i < perm.size(); ++i) { newid[perm[i]] = i; nq[i] = g.vq[perm[i]]; nc[i] = g.vcell[perm[i]]; }
    g.vq.swap(nq); g.vcell.swap(nc);
    for (size_t e = 0; e < g.ne(); ++e) {
        g.eu[e] = newid[g.eu[e]]; g.ev[e] = newid[g.ev[e]];
        if (g.eu[e] == 0xFFFFFFFFu || g.ev[e] == 0xFFFFFFFFu) die("edge references dropped vertex");
        if (g.ewlen[e] == 0) die("empty word");
    }
    // sort edges
    size_t m = g.ne();
    vector<u32> ep(m);
    iota(ep.begin(), ep.end(), 0);
    const int8_t* ch = g.chars.data();
    sort(ep.begin(), ep.end(), [&](u32 x, u32 y) {
        if (g.eu[x] != g.eu[y]) return g.eu[x] < g.eu[y];
        if (g.ev[x] != g.ev[y]) return g.ev[x] < g.ev[y];
        return cmp_word(ch + g.ewoff[x], g.ewlen[x], ch + g.ewoff[y], g.ewlen[y]) < 0;
    });
    if (g.emult.size() != m) die("multiplicity vector size mismatch");
    vector<u32> neu, nev; vector<u64> noff; vector<u32> nlen; vector<u64> nmult;
    neu.reserve(m); nev.reserve(m); noff.reserve(m); nlen.reserve(m); nmult.reserve(m);
    for (size_t i = 0; i < m; ++i) {
        u32 e = ep[i];
        if (i > 0) {
            u32 f = ep[i - 1];
            if (g.eu[e] == g.eu[f] && g.ev[e] == g.ev[f] &&
                cmp_word(ch + g.ewoff[e], g.ewlen[e], ch + g.ewoff[f], g.ewlen[f]) == 0) {
                nmult.back() += g.emult[e];   // duplicate triple: merge, keep the count
                continue;
            }
        }
        neu.push_back(g.eu[e]); nev.push_back(g.ev[e]); noff.push_back(g.ewoff[e]); nlen.push_back(g.ewlen[e]); nmult.push_back(g.emult[e]);
    }
    g.eu.swap(neu); g.ev.swap(nev); g.ewoff.swap(noff); g.ewlen.swap(nlen); g.emult.swap(nmult);
}

// ---------------------------------------------------------------- output
struct Out {
    FILE* f = nullptr;
    string buf;
    explicit Out(const string& path) {
        f = fopen(path.c_str(), "wb");
        if (!f) die("cannot open output " + path);
        buf.reserve(1 << 24);
    }
    ~Out() { flush(); fclose(f); }
    void flush() { if (!buf.empty()) { fwrite(buf.data(), 1, buf.size(), f); buf.clear(); } }
    void maybe_flush() { if (buf.size() > (1u << 24) - 4096) flush(); }
    void s(const char* t) { buf.append(t); }
    void s(const string& t) { buf.append(t); }
    void c(char ch) { buf.push_back(ch); }
    void u(u64 x) {
        char tmp[24]; int k = 0;
        if (x == 0) { buf.push_back('0'); return; }
        while (x) { tmp[k++] = char('0' + x % 10); x /= 10; }
        while (k) buf.push_back(tmp[--k]);
    }
    void i(i64 x) { if (x < 0) { buf.push_back('-'); u((u64)(-x)); } else u((u64)x); }
};

static string primes_str(const vector<u64>& ps) {
    string s;
    for (size_t i = 0; i < ps.size(); ++i) { if (i) s += ','; s += to_string(ps[i]); }
    return s;
}

static void write_graph(const Graph& g, const string& path, u64 a, u64 b) {
    Out o(path);
    o.s("WORDGRAPH 2 a="); o.u(a); o.s(" b="); o.u(b); o.s(" K="); o.u(g.K);
    o.s(" modulus="); o.u(g.modulus); o.s(" primes="); o.s(primes_str(g.primes));
    o.s(" vertices="); o.u(g.nv()); o.s(" edges="); o.u(g.ne()); o.c('\n');
    for (size_t i = 0; i < g.nv(); ++i) {
        o.s("V "); o.u(g.vq[i]); o.c(' '); o.u(g.vcell[i]); o.c('\n');
        o.maybe_flush();
    }
    for (size_t e = 0; e < g.ne(); ++e) {
        u32 u = g.eu[e], v = g.ev[e];
        o.s("E "); o.u(g.vq[u]); o.c(' '); o.u(g.vcell[u]); o.c(' '); o.u(g.vq[v]); o.c(' '); o.u(g.vcell[v]);
        const int8_t* w = g.word(e);
        for (u32 i = 0; i < g.ewlen[e]; ++i) { o.c(' '); o.i(w[i]); }
        o.c('\n');
        o.maybe_flush();
    }
}

// ---------------------------------------------------------------- initial graph
static Graph initial_graph(i64 a, i64 b, u32 K, const vector<int>& carries) {
    Graph g;
    g.modulus = 1; g.K = K;
    for (u32 j = 0; j < K; ++j) { g.vq.push_back(0); g.vcell.push_back(j); }
    // direct strict inequalities over all (j, c, k)
    for (u32 j = 0; j < K; ++j)
        for (int c : carries)
            for (u32 k = 0; k < K; ++k) {
                i64 lo = a * (i64)j - b * ((i64)k + 1);
                i64 mid = (i64)c * (i64)K;
                i64 hi = a * ((i64)j + 1) - b * (i64)k;
                if (lo < mid && mid < hi) {
                    g.eu.push_back(j); g.ev.push_back(k);
                    g.ewoff.push_back(g.chars.size()); g.ewlen.push_back(1); g.emult.push_back(1);
                    g.chars.push_back((int8_t)c);
                }
            }
    normalize(g, false);
    return g;
}

// ---------------------------------------------------------------- SCC (iterative Tarjan)
struct SccResult {
    vector<u32> comp;   // component id per vertex; ids are in completion order (sinks first)
    u32 ncomp = 0;
};

static SccResult tarjan(u32 n, const vector<u32>& head, const vector<u32>& to) {
    const u32 UNV = 0xFFFFFFFFu;
    SccResult r;
    r.comp.assign(n, UNV);
    vector<u32> idx(n, UNV), low(n, 0);
    vector<u32> stk; stk.reserve(n);
    vector<char> onst(n, 0);
    vector<pair<u32, u32>> cs;
    u32 counter = 0;
    for (u32 s = 0; s < n; ++s) {
        if (idx[s] != UNV) continue;
        idx[s] = low[s] = counter++; stk.push_back(s); onst[s] = 1;
        cs.push_back({s, head[s]});
        while (!cs.empty()) {
            u32 v = cs.back().first;
            u32 pos = cs.back().second;
            if (pos < head[v + 1]) {
                cs.back().second = pos + 1;
                u32 w = to[pos];
                if (idx[w] == UNV) {
                    idx[w] = low[w] = counter++; stk.push_back(w); onst[w] = 1;
                    cs.push_back({w, head[w]});
                } else if (onst[w]) {
                    if (idx[w] < low[v]) low[v] = idx[w];
                }
            } else {
                if (low[v] == idx[v]) {
                    while (true) {
                        u32 x = stk.back(); stk.pop_back(); onst[x] = 0; r.comp[x] = r.ncomp;
                        if (x == v) break;
                    }
                    r.ncomp++;
                }
                cs.pop_back();
                if (!cs.empty()) { u32 p = cs.back().first; if (low[v] < low[p]) low[p] = low[v]; }
            }
        }
    }
    for (u32 v = 0; v < n; ++v) if (r.comp[v] == UNV) die("tarjan left a vertex unassigned");
    return r;
}

// CSR of edges sorted by source (normalize() guarantees eu sorted).
static void build_csr(const Graph& g, vector<u32>& head) {
    u32 n = (u32)g.nv();
    head.assign(n + 1, 0);
    for (size_t e = 0; e < g.ne(); ++e) head[g.eu[e] + 1]++;
    for (u32 i = 0; i < n; ++i) head[i + 1] += head[i];
    for (size_t e = 1; e < g.ne(); ++e) if (g.eu[e] < g.eu[e - 1]) die("edges not sorted by source");
}

// Independent post-check of the SCC partition (audit-01 §5 sufficient condition):
// (i) inside each block, forward and backward reachability via internal edges only covers the block;
// (ii) every inter-block edge u->v has comp[v] < comp[u] (strict integer rank => condensation acyclic).
static bool verify_scc(const Graph& g, const SccResult& sr, const vector<u32>& head) {
    u32 n = (u32)g.nv();
    // reverse CSR of internal edges
    vector<u32> rhead(n + 1, 0), rto;
    for (size_t e = 0; e < g.ne(); ++e) if (sr.comp[g.eu[e]] == sr.comp[g.ev[e]]) rhead[g.ev[e] + 1]++;
    for (u32 i = 0; i < n; ++i) rhead[i + 1] += rhead[i];
    rto.assign(rhead[n], 0);
    { vector<u32> fill(rhead.begin(), rhead.end() - 1);
      for (size_t e = 0; e < g.ne(); ++e) if (sr.comp[g.eu[e]] == sr.comp[g.ev[e]]) rto[fill[g.ev[e]]++] = g.eu[e]; }
    // block member lists
    vector<u32> chead(sr.ncomp + 1, 0), cmem(n);
    for (u32 v = 0; v < n; ++v) chead[sr.comp[v] + 1]++;
    for (u32 c = 0; c < sr.ncomp; ++c) chead[c + 1] += chead[c];
    { vector<u32> fill(chead.begin(), chead.end() - 1);
      for (u32 v = 0; v < n; ++v) cmem[fill[sr.comp[v]]++] = v; }
    vector<u32> stamp(n, 0xFFFFFFFFu);
    vector<u32> q; q.reserve(n);
    for (u32 c = 0; c < sr.ncomp; ++c) {
        u32 sz = chead[c + 1] - chead[c];
        u32 root = cmem[chead[c]];
        // forward
        q.clear(); q.push_back(root); stamp[root] = 2 * c;
        for (size_t qi = 0; qi < q.size(); ++qi) {
            u32 v = q[qi];
            for (u32 p = head[v]; p < head[v + 1]; ++p) {
                u32 w = g.ev[p];
                if (sr.comp[w] != c) continue;
                if (stamp[w] != 2 * c) { stamp[w] = 2 * c; q.push_back(w); }
            }
        }
        if (q.size() != sz) return false;
        // backward
        q.clear(); q.push_back(root); stamp[root] = 2 * c + 1;
        for (size_t qi = 0; qi < q.size(); ++qi) {
            u32 v = q[qi];
            for (u32 p = rhead[v]; p < rhead[v + 1]; ++p) {
                u32 w = rto[p];
                if (stamp[w] != 2 * c + 1) { stamp[w] = 2 * c + 1; q.push_back(w); }
            }
        }
        if (q.size() != sz) return false;
    }
    for (size_t e = 0; e < g.ne(); ++e) {
        u32 cu = sr.comp[g.eu[e]], cv = sr.comp[g.ev[e]];
        if (cu != cv && !(cv < cu)) return false;
    }
    return true;
}

static u64 gcd64(u64 x, u64 y) { while (y) { u64 t = x % y; x = y; y = t; } return x; }

// ---------------------------------------------------------------- certification (W2)
struct CompInfo {
    vector<u32> chead;      // block -> range in cmem (vertices, ascending ids)
    vector<u32> cmem;
    vector<u32> ehead;      // block -> range in emem (internal edge ids)
    vector<u32> emem;
};

static CompInfo group_components(const Graph& g, const SccResult& sr) {
    CompInfo ci;
    u32 n = (u32)g.nv();
    ci.chead.assign(sr.ncomp + 1, 0); ci.cmem.assign(n, 0);
    for (u32 v = 0; v < n; ++v) ci.chead[sr.comp[v] + 1]++;
    for (u32 c = 0; c < sr.ncomp; ++c) ci.chead[c + 1] += ci.chead[c];
    { vector<u32> fill(ci.chead.begin(), ci.chead.end() - 1);
      for (u32 v = 0; v < n; ++v) ci.cmem[fill[sr.comp[v]]++] = v; }   // ascending ids per block
    ci.ehead.assign(sr.ncomp + 1, 0);
    for (size_t e = 0; e < g.ne(); ++e) if (sr.comp[g.eu[e]] == sr.comp[g.ev[e]]) ci.ehead[sr.comp[g.eu[e]] + 1]++;
    for (u32 c = 0; c < sr.ncomp; ++c) ci.ehead[c + 1] += ci.ehead[c];
    ci.emem.assign(ci.ehead[sr.ncomp], 0);
    { vector<u32> fill(ci.ehead.begin(), ci.ehead.end() - 1);
      for (size_t e = 0; e < g.ne(); ++e) if (sr.comp[g.eu[e]] == sr.comp[g.ev[e]]) ci.emem[fill[sr.comp[g.eu[e]]]++] = (u32)e; }
    return ci;
}

struct CertResult {
    bool cyclic = false;
    bool certified = false;
    u64 d = 0;
    bool all_phases_used = true;
    vector<int8_t> lambda;   // filled only when certified (size d)
    u32 root = 0;
};

// h: scratch array of size n (values valid only for this block); ihead/ito: CSR of internal edges.
static CertResult certify_block(const Graph& g, const CompInfo& ci, u32 c,
                                const vector<u32>& ihead, const vector<u32>& ito, const vector<u32>& ieid,
                                vector<i64>& h, vector<char>& hset, vector<u32>& queue, bool keep_lambda) {
    CertResult r;
    u32 ne_int = ci.ehead[c + 1] - ci.ehead[c];
    if (ne_int == 0) return r;   // acyclic singleton
    r.cyclic = true;
    u32 root = ci.cmem[ci.chead[c]];   // smallest id = lexicographically smallest name
    r.root = root;
    // BFS over internal edges: h(v) = h(u) + |w| at first discovery
    queue.clear(); queue.push_back(root); h[root] = 0; hset[root] = 1;
    for (size_t qi = 0; qi < queue.size(); ++qi) {
        u32 v = queue[qi];
        for (u32 p = ihead[v]; p < ihead[v + 1]; ++p) {
            u32 w = ito[p];
            if (!hset[w]) { hset[w] = 1; h[w] = h[v] + g.ewlen[ieid[p]]; queue.push_back(w); }
        }
    }
    if (queue.size() != ci.chead[c + 1] - ci.chead[c]) die("BFS did not reach whole block (SCC inconsistency)");
    u64 d = 0;
    for (u32 p = ci.ehead[c]; p < ci.ehead[c + 1]; ++p) {
        u32 e = ci.emem[p];
        i64 delta = h[g.eu[e]] + (i64)g.ewlen[e] - h[g.ev[e]];
        u64 ad = delta < 0 ? (u64)(-delta) : (u64)delta;
        d = gcd64(d, ad);
    }
    if (d == 0) die("d = 0 in a cyclic block (impossible by W2-a)");
    r.d = d;
    vector<int8_t> lam(d, (int8_t)127);
    bool ok = true;
    for (u32 p = ci.ehead[c]; p < ci.ehead[c + 1] && ok; ++p) {
        u32 e = ci.emem[p];
        i64 hu = h[g.eu[e]];
        u64 s = (u64)(((hu % (i64)d) + (i64)d) % (i64)d);
        const int8_t* w = g.word(e);
        for (u32 i = 0; i < g.ewlen[e]; ++i) {
            if (lam[s] == 127) lam[s] = w[i];
            else if (lam[s] != w[i]) { ok = false; break; }
            if (++s == d) s = 0;
        }
    }
    if (ok) {
        for (u64 s = 0; s < d; ++s) if (lam[s] == 127) { r.all_phases_used = false; break; }
    }
    if (ok && !r.all_phases_used) die("W2-c violated: an unused phase in a consistently labelled block (implementation error)");
    r.certified = ok;
    if (r.certified && keep_lambda) r.lambda.swap(lam);
    // reset h flags
    for (u32 v : queue) hset[v] = 0;
    return r;
}

// ---------------------------------------------------------------- prune = contract(remove(G))
struct PruneStats {
    u64 scc = 0, cyclic = 0, certified = 0, uncertified = 0, uncertified_vertices = 0;
    u64 anchors = 0, unused_phase_blocks = 0, gprime_edges = 0, out_vertices = 0, out_edges = 0;
    u64 out_max_wlen = 0, out_chars = 0, max_d = 0, out_edges_multiset = 0;
    bool scc_verified = false;
    double t_scc = 0, t_cert = 0, t_contract = 0;
};

static Graph prune(const Graph& g, PruneStats& st) {
    u32 n = (u32)g.nv();
    double t0 = now_sec();
    vector<u32> head; build_csr(g, head);
    SccResult sr = tarjan(n, head, g.ev);
    st.scc = sr.ncomp;
    st.scc_verified = verify_scc(g, sr, head);
    if (!st.scc_verified) die("SCC post-check failed");
    CompInfo ci = group_components(g, sr);
    // CSR of internal edges (targets + edge ids), sources ascending
    vector<u32> ihead(n + 1, 0), ito, ieid;
    for (size_t e = 0; e < g.ne(); ++e) if (sr.comp[g.eu[e]] == sr.comp[g.ev[e]]) ihead[g.eu[e] + 1]++;
    for (u32 i = 0; i < n; ++i) ihead[i + 1] += ihead[i];
    ito.assign(ihead[n], 0); ieid.assign(ihead[n], 0);
    { vector<u32> fill(ihead.begin(), ihead.end() - 1);
      for (size_t e = 0; e < g.ne(); ++e) if (sr.comp[g.eu[e]] == sr.comp[g.ev[e]]) { u32 u = g.eu[e]; ito[fill[u]] = g.ev[e]; ieid[fill[u]] = (u32)e; fill[u]++; } }
    double t1 = now_sec(); st.t_scc = t1 - t0;

    vector<i64> h(n, 0); vector<char> hset(n, 0); vector<u32> queue; queue.reserve(n);
    vector<char> block_uncert(sr.ncomp, 0);
    for (u32 c = 0; c < sr.ncomp; ++c) {
        CertResult cr = certify_block(g, ci, c, ihead, ito, ieid, h, hset, queue, false);
        if (!cr.cyclic) continue;
        st.cyclic++;
        if (cr.d > st.max_d) st.max_d = cr.d;
        if (!cr.all_phases_used) st.unused_phase_blocks++;
        if (cr.certified) st.certified++;
        else { st.uncertified++; st.uncertified_vertices += ci.chead[c + 1] - ci.chead[c]; block_uncert[c] = 1; }
    }
    double t2 = now_sec(); st.t_cert = t2 - t1;

    // G' = internal edges of uncertified blocks (already unique triples after normalize)
    vector<char> edge_in_gp(g.ne(), 0);
    vector<u32> outdeg(n, 0);
    for (size_t e = 0; e < g.ne(); ++e) {
        u32 cu = sr.comp[g.eu[e]];
        if (cu == sr.comp[g.ev[e]] && block_uncert[cu]) { edge_in_gp[e] = 1; outdeg[g.eu[e]]++; st.gprime_edges++; }
    }
    vector<char> macro(n, 0);
    for (u32 v = 0; v < n; ++v) if (outdeg[v] >= 2) macro[v] = 1;
    for (u32 c = 0; c < sr.ncomp; ++c) {
        if (!block_uncert[c]) continue;
        bool has = false;
        for (u32 p = ci.chead[c]; p < ci.chead[c + 1]; ++p) if (macro[ci.cmem[p]]) { has = true; break; }
        if (!has) { macro[ci.cmem[ci.chead[c]]] = 1; st.anchors++; }   // anchor = smallest name
    }
    // G' vertices must all have outdeg >= 1 (W3-a)
    u64 gp_vertices = 0;
    for (u32 c = 0; c < sr.ncomp; ++c) if (block_uncert[c])
        for (u32 p = ci.chead[c]; p < ci.chead[c + 1]; ++p) { gp_vertices++; if (outdeg[ci.cmem[p]] == 0) die("G' vertex with outdegree 0"); }
    // macro edges
    Graph out;
    out.modulus = g.modulus; out.primes = g.primes; out.K = g.K;
    vector<u32> newid(n, 0xFFFFFFFFu);
    for (u32 v = 0; v < n; ++v) if (macro[v]) { newid[v] = (u32)out.vq.size(); out.vq.push_back(g.vq[v]); out.vcell.push_back(g.vcell[v]); }
    // unique out-edge of outdeg-1 vertices within G' : locate by scanning head range
    for (u32 u = 0; u < n; ++u) {
        if (!macro[u]) continue;
        for (u32 p = head[u]; p < head[u + 1]; ++p) {
            if (!edge_in_gp[p]) continue;
            u64 woff = out.chars.size();
            const int8_t* w = g.word(p);
            out.chars.insert(out.chars.end(), w, w + g.ewlen[p]);
            u32 cur = g.ev[p];
            u64 steps = 0;
            while (!macro[cur]) {
                if (outdeg[cur] != 1) die("chain vertex with outdegree != 1");
                u32 q = head[cur];
                while (!edge_in_gp[q]) { ++q; if (q >= head[cur + 1]) die("missing unique out-edge"); }
                const int8_t* w2 = g.word(q);
                out.chars.insert(out.chars.end(), w2, w2 + g.ewlen[q]);
                cur = g.ev[q];
                if (++steps > gp_vertices + 1) die("chain did not terminate (W3-c violated)");
            }
            out.eu.push_back(newid[u]); out.ev.push_back(newid[cur]);
            out.ewoff.push_back(woff); out.ewlen.push_back((u32)(out.chars.size() - woff)); out.emult.push_back(1);
        }
    }
    normalize(out, false);
    st.out_vertices = out.nv(); st.out_edges = out.ne();
    for (size_t e = 0; e < out.ne(); ++e) { if (out.ewlen[e] > st.out_max_wlen) st.out_max_wlen = out.ewlen[e]; st.out_chars += out.ewlen[e]; st.out_edges_multiset += out.emult[e]; }
    st.t_contract = now_sec() - t2;
    return out;
}

// ---------------------------------------------------------------- lift (W4)
static bool is_prime(u64 p) { if (p < 2) return false; for (u64 d = 2; d * d <= p; ++d) if (p % d == 0) return false; return true; }

struct LiftStats { u64 candidates = 0, kept = 0, isolated_dropped = 0, in_vertices = 0, in_edges = 0, in_max_wlen = 0, in_chars = 0, in_edges_multiset = 0; double t = 0; };

static Graph lift(const Graph& g, u64 p, u64 a, u64 b, LiftStats& ls) {
    double t0 = now_sec();
    if (!is_prime(p)) die("p is not prime");
    if (a % p == 0 || b % p == 0) die("p divides ab");
    for (u64 q : g.primes) if (q == p) die("prime already used");
    if (g.modulus % p == 0) die("modulus already divisible by p");
    // b^{-1} mod p by exhaustive search
    u64 binv = 0;
    for (u64 x = 1; x < p; ++x) if ((b % p) * x % p == 1) { binv = x; break; }
    if (binv == 0) die("no inverse of b mod p");
    // P^{-1} mod p for CRT
    u64 Pm = g.modulus % p, Pinv = 0;
    for (u64 x = 1; x < p; ++x) if (Pm * x % p == 1) { Pinv = x; break; }
    if (Pinv == 0) die("no inverse of modulus mod p");
    Graph out;
    out.modulus = g.modulus * p; out.primes = g.primes; out.primes.push_back(p); out.K = g.K;
    out.chars = g.chars;   // words unchanged
    u32 n = (u32)g.nv();
    u64 nprov = (u64)n * (p - 1);
    if (nprov > 0xFFFFFFF0ull) die("too many provisional vertices");
    out.vq.resize(nprov); out.vcell.resize(nprov);
    for (u32 u = 0; u < n; ++u) for (u64 s = 1; s < p; ++s) {
        u64 qu = g.vq[u];
        // q' = qu + P * (((s - qu mod p) mod p) * Pinv mod p); 0 <= q' < P*p; q' == qu (mod P), q' == s (mod p)
        u64 t = ((s + p - qu % p) % p) * Pinv % p;
        u64 qn = qu + g.modulus * t;
        if (qn % g.modulus != qu || qn % p != s || qn >= out.modulus) die("CRT failure");
        out.vq[u * (p - 1) + (s - 1)] = qn; out.vcell[u * (p - 1) + (s - 1)] = g.vcell[u];
    }
    u64 am = a % p;
    for (size_t e = 0; e < g.ne(); ++e) {
        const int8_t* w = g.word(e);
        u32 len = g.ewlen[e];
        for (u64 s = 1; s < p; ++s) {
            ls.candidates++;
            u64 q = s; bool ok = true;
            for (u32 i = 0; i < len; ++i) {
                i64 t = (i64)(am * q) + (i64)w[i];
                i64 tm = ((t % (i64)p) + (i64)p) % (i64)p;
                q = (u64)tm * binv % p;
                if (q == 0) { ok = false; break; }
            }
            if (!ok) continue;
            ls.kept++;
            out.eu.push_back((u32)((u64)g.eu[e] * (p - 1) + (s - 1)));
            out.ev.push_back((u32)((u64)g.ev[e] * (p - 1) + (q - 1)));
            out.ewoff.push_back(g.ewoff[e]); out.ewlen.push_back(len); out.emult.push_back(g.emult[e]);
        }
    }
    u64 before = out.nv();
    normalize(out, true);
    ls.isolated_dropped = before - out.nv();
    ls.in_vertices = out.nv(); ls.in_edges = out.ne();
    for (size_t e = 0; e < out.ne(); ++e) { if (out.ewlen[e] > ls.in_max_wlen) ls.in_max_wlen = out.ewlen[e]; ls.in_chars += out.ewlen[e]; ls.in_edges_multiset += out.emult[e]; }
    ls.t = now_sec() - t0;
    return out;
}

// ---------------------------------------------------------------- CLI helpers
static vector<int> parse_ints(const string& s) {
    vector<int> r; string cur;
    for (char ch : s) { if (ch == ',') { if (!cur.empty()) r.push_back(stoi(cur)); cur.clear(); } else cur += ch; }
    if (!cur.empty()) r.push_back(stoi(cur));
    return r;
}
static vector<u64> parse_u64s(const string& s) {
    vector<u64> r; for (int x : parse_ints(s)) r.push_back((u64)x); return r;
}

static void run_pipeline(int argc, char** argv) {
    i64 a = 0, b = 0; u32 K = 0; vector<int> carries; vector<u64> primes; string outdir; int stop_after = -1;
    for (int i = 2; i < argc; ++i) {
        string k = argv[i]; string v = (i + 1 < argc) ? argv[i + 1] : "";
        if (k == "--a") a = stoll(v); else if (k == "--b") b = stoll(v); else if (k == "--K") K = (u32)stoul(v);
        else if (k == "--carries") carries = parse_ints(v); else if (k == "--primes") primes = parse_u64s(v);
        else if (k == "--out") outdir = v; else if (k == "--stop-after") stop_after = stoi(v);
        else die("unknown option " + k);
        ++i;
    }
    if (!(a > b && b >= 2) || gcd64(a, b) != 1 || K < 1 || carries.empty() || outdir.empty()) die("bad parameters");
    for (int c : carries) if (!(1 - b <= c && c <= a - 1)) die("carry outside [1-b, a-1]");
    { string cs; for (size_t i = 0; i < carries.size(); ++i) { if (i) cs += ','; cs += to_string(carries[i]); }
      printf("{\"event\":\"params\",\"a\":%lld,\"b\":%lld,\"K\":%u,\"carries\":\"%s\",\"primes\":\"%s\"}\n",
             a, b, K, cs.c_str(), primes_str(primes).c_str()); }
    fflush(stdout);
    double tstart = now_sec();
    Graph gin = initial_graph(a, b, K, carries);
    u64 in_max = 0, in_chars = 0;
    for (size_t e = 0; e < gin.ne(); ++e) { if (gin.ewlen[e] > in_max) in_max = gin.ewlen[e]; in_chars += gin.ewlen[e]; }
    LiftStats ls; ls.in_vertices = gin.nv(); ls.in_edges = gin.ne(); ls.in_max_wlen = in_max; ls.in_chars = in_chars; ls.in_edges_multiset = gin.ne();
    for (size_t k = 0; k <= primes.size(); ++k) {
        double ts = now_sec();
        string fin = outdir + "/stage" + to_string(k) + "_input.txt";
        write_graph(gin, fin, a, b);
        PruneStats st;
        Graph gout = prune(gin, st);
        string fout = outdir + "/stage" + to_string(k) + "_output.txt";
        write_graph(gout, fout, a, b);
        double te = now_sec();
        printf("{\"event\":\"stage\",\"stage\":%zu,\"prime\":%llu,\"modulus\":%llu,"
               "\"in_vertices\":%llu,\"in_edges\":%llu,\"in_max_word_length\":%llu,\"in_total_chars\":%llu,"
               "\"lift_candidates\":%llu,\"lift_kept\":%llu,\"lift_isolated_dropped\":%llu,"
               "\"scc\":%llu,\"scc_verified\":%s,\"cyclic\":%llu,\"certified\":%llu,\"uncertified\":%llu,\"uncertified_vertices\":%llu,"
               "\"max_d\":%llu,\"unused_phase_blocks\":%llu,\"anchors\":%llu,\"gprime_edges\":%llu,"
               "\"out_vertices\":%llu,\"out_edges\":%llu,\"out_max_word_length\":%llu,\"out_total_chars\":%llu,"
               "\"in_edges_multiset\":%llu,\"out_edges_multiset\":%llu,"
               "\"t_lift\":%.3f,\"t_scc\":%.3f,\"t_cert\":%.3f,\"t_contract\":%.3f,\"t_stage_total\":%.3f}\n",
               k, k == 0 ? 0ull : primes[k - 1], gin.modulus,
               (u64)ls.in_vertices, (u64)ls.in_edges, ls.in_max_wlen, ls.in_chars,
               ls.candidates, ls.kept, ls.isolated_dropped,
               st.scc, st.scc_verified ? "true" : "false", st.cyclic, st.certified, st.uncertified, st.uncertified_vertices,
               st.max_d, st.unused_phase_blocks, st.anchors, st.gprime_edges,
               st.out_vertices, st.out_edges, st.out_max_wlen, st.out_chars,
               ls.in_edges_multiset, st.out_edges_multiset,
               ls.t, st.t_scc, st.t_cert, st.t_contract, te - ts + ls.t);
        fflush(stdout);
        if ((int)k == stop_after) { printf("{\"event\":\"stopped\",\"after_stage\":%zu}\n", k); break; }
        if (k == primes.size()) {
            printf("{\"event\":\"final\",\"final_output_empty\":%s,\"final_out_vertices\":%llu,\"final_out_edges\":%llu,\"t_total\":%.3f}\n",
                   (gout.nv() == 0 && gout.ne() == 0) ? "true" : "false", st.out_vertices, st.out_edges, now_sec() - tstart);
            break;
        }
        if (gout.nv() == 0) {
            printf("{\"event\":\"final\",\"final_output_empty\":true,\"note\":\"empty before all primes used\",\"t_total\":%.3f}\n", now_sec() - tstart);
            break;
        }
        ls = LiftStats();
        gin = lift(gout, primes[k], (u64)a, (u64)b, ls);
    }
    fflush(stdout);
}

// ---------------------------------------------------------------- Q75 mode
static void run_q75(int argc, char** argv) {
    i64 a = 0, b = 0; u64 M = 0; u32 K = 0; vector<int> carries; string outdir;
    u64 rho_max_allowed = 65, eta_max_allowed = 6, d_max_allowed = 13;
    for (int i = 2; i < argc; ++i) {
        string k = argv[i]; string v = (i + 1 < argc) ? argv[i + 1] : "";
        if (k == "--a") a = stoll(v); else if (k == "--b") b = stoll(v); else if (k == "--M") M = stoull(v);
        else if (k == "--K") K = (u32)stoul(v); else if (k == "--carries") carries = parse_ints(v); else if (k == "--out") outdir = v;
        else if (k == "--rho-max") rho_max_allowed = stoull(v); else if (k == "--eta-max") eta_max_allowed = stoull(v);
        else if (k == "--d-max") d_max_allowed = stoull(v);
        else die("unknown option " + k);
        ++i;
    }
    if (!(a > b && b >= 2) || gcd64(a, b) != 1 || K < 1 || M < 2 || carries.empty() || outdir.empty()) die("bad parameters");
    for (int c : carries) if (!(1 - b <= c && c <= a - 1)) die("carry outside [1-b, a-1]");
    double t0 = now_sec();
    // vertices: all (q,j), gcd(q,M)=1, 0<=j<K, in lexicographic order
    vector<u64> units;
    for (u64 q = 0; q < M; ++q) if (gcd64(q, M) == 1) units.push_back(q);
    Graph g; g.modulus = M; g.K = K;
    for (u64 q : units) for (u32 j = 0; j < K; ++j) { g.vq.push_back(q); g.vcell.push_back(j); }
    // index (q,j) -> id : id = pos(q)*K + j
    vector<i64> qpos(M, -1);
    for (size_t i = 0; i < units.size(); ++i) qpos[units[i]] = (i64)i;
    // E2 by exhaustive search over z (no inverse), E3 by exhaustive search over k
    // zs[ci][qi] = list of z ; ks[ci][j] = list of k
    size_t nc = carries.size();
    vector<vector<vector<u64>>> zs(nc, vector<vector<u64>>(units.size()));
    for (size_t ci = 0; ci < nc; ++ci) for (size_t qi = 0; qi < units.size(); ++qi) {
        i64 q = (i64)units[qi], c = carries[ci];
        for (u64 z = 0; z < M; ++z) {
            i64 t = b * (i64)z - a * q - c;
            if (((t % (i64)M) + (i64)M) % (i64)M == 0 && gcd64(z, M) == 1) zs[ci][qi].push_back(z);
        }
    }
    vector<vector<vector<u32>>> ks(nc, vector<vector<u32>>(K));
    for (size_t ci = 0; ci < nc; ++ci) for (u32 j = 0; j < K; ++j) {
        i64 c = carries[ci];
        for (u32 k = 0; k < K; ++k) {
            i64 lo = a * (i64)j - b * ((i64)k + 1), mid = c * (i64)K, hi = a * ((i64)j + 1) - b * (i64)k;
            if (lo < mid && mid < hi) ks[ci][j].push_back(k);
        }
    }
    for (size_t qi = 0; qi < units.size(); ++qi) for (u32 j = 0; j < K; ++j)
        for (size_t ci = 0; ci < nc; ++ci)
            for (u64 z : zs[ci][qi]) for (u32 k : ks[ci][j]) {
                g.eu.push_back((u32)(qi * K + j)); g.ev.push_back((u32)((u64)qpos[z] * K + k));
                g.ewoff.push_back(g.chars.size()); g.ewlen.push_back(1); g.emult.push_back(1); g.chars.push_back((int8_t)carries[ci]);
            }
    normalize(g, false);
    double t1 = now_sec();
    u32 n = (u32)g.nv();
    vector<u32> head; build_csr(g, head);
    SccResult sr = tarjan(n, head, g.ev);
    bool scc_ok = verify_scc(g, sr, head);
    if (!scc_ok) die("SCC post-check failed");
    CompInfo ci = group_components(g, sr);
    vector<u32> ihead(n + 1, 0), ito, ieid;
    for (size_t e = 0; e < g.ne(); ++e) if (sr.comp[g.eu[e]] == sr.comp[g.ev[e]]) ihead[g.eu[e] + 1]++;
    for (u32 i = 0; i < n; ++i) ihead[i + 1] += ihead[i];
    ito.assign(ihead[n], 0); ieid.assign(ihead[n], 0);
    { vector<u32> fill(ihead.begin(), ihead.end() - 1);
      for (size_t e = 0; e < g.ne(); ++e) if (sr.comp[g.eu[e]] == sr.comp[g.ev[e]]) { u32 u = g.eu[e]; ito[fill[u]] = g.ev[e]; ieid[fill[u]] = (u32)e; fill[u]++; } }
    vector<i64> h(n, 0); vector<char> hset(n, 0); vector<u32> queue; queue.reserve(n);
    vector<CertResult> cr(sr.ncomp);
    u64 cyclic = 0, certified = 0, uncertified = 0, maxd = 0, unused_phase = 0;
    for (u32 c = 0; c < sr.ncomp; ++c) {
        cr[c] = certify_block(g, ci, c, ihead, ito, ieid, h, hset, queue, true);
        if (!cr[c].cyclic) continue;
        cyclic++;
        if (cr[c].d > maxd) maxd = cr[c].d;
        if (!cr[c].all_phases_used) unused_phase++;
        if (cr[c].certified) certified++; else uncertified++;
    }
    // rho / eta over the condensation: predecessors have larger comp ids (Tarjan completion order)
    vector<u64> rho(sr.ncomp, 1), eta(sr.ncomp, 0);
    for (u32 c = 0; c < sr.ncomp; ++c) eta[c] = cr[c].cyclic ? 1 : 0;   // periodic <=> cyclic (all cyclic are certified if uncertified==0)
    for (u32 cc = sr.ncomp; cc-- > 0;) {
        for (u32 p = ci.chead[cc]; p < ci.chead[cc + 1]; ++p) {
            u32 u = ci.cmem[p];
            for (u32 e = head[u]; e < head[u + 1]; ++e) {
                u32 dcomp = sr.comp[g.ev[e]];
                if (dcomp == cc) continue;
                if (rho[cc] + 1 > rho[dcomp]) rho[dcomp] = rho[cc] + 1;
                u64 cand = eta[cc] + (cr[dcomp].cyclic ? 1 : 0);
                if (cand > eta[dcomp]) eta[dcomp] = cand;
            }
        }
    }
    // independent re-check of (Q-rank) and (Q-cyc) on every inter-block edge
    bool rank_ok = true, cyc_ok = true;
    for (size_t e = 0; e < g.ne(); ++e) {
        u32 cu = sr.comp[g.eu[e]], cv = sr.comp[g.ev[e]];
        if (cu == cv) continue;
        if (!(rho[cv] >= rho[cu] + 1)) rank_ok = false;
        if (!(eta[cv] >= eta[cu] + (cr[cv].cyclic ? 1 : 0))) cyc_ok = false;
    }
    u64 rho_max = 0, eta_max = 0;
    for (u32 c = 0; c < sr.ncomp; ++c) { if (rho[c] > rho_max) rho_max = rho[c]; if (eta[c] > eta_max) eta_max = eta[c]; if (eta[c] < (cr[c].cyclic ? 1u : 0u)) cyc_ok = false; }
    bool bounds_ok = rho_max <= rho_max_allowed && eta_max <= eta_max_allowed && maxd <= d_max_allowed && uncertified == 0;
    for (u32 c = 0; c < sr.ncomp; ++c) if (rho[c] < 1) bounds_ok = false;
    double t2 = now_sec();
    // output: block ids renumbered by smallest vertex id (= lexicographic order of smallest vertex)
    vector<u32> order(sr.ncomp);
    iota(order.begin(), order.end(), 0);
    sort(order.begin(), order.end(), [&](u32 x, u32 y) { return ci.cmem[ci.chead[x]] < ci.cmem[ci.chead[y]]; });
    {
        Out o(outdir + "/q75_graph.txt");
        o.s("Q75GRAPH 2 a="); o.i(a); o.s(" b="); o.i(b); o.s(" M="); o.u(M); o.s(" K="); o.u(K);
        o.s(" vertices="); o.u(n); o.s(" edges="); o.u(g.ne()); o.s(" blocks="); o.u(sr.ncomp); o.c('\n');
        for (u32 i = 0; i < n; ++i) { o.s("V "); o.u(g.vq[i]); o.c(' '); o.u(g.vcell[i]); o.c('\n'); o.maybe_flush(); }
        for (size_t e = 0; e < g.ne(); ++e) {
            u32 u = g.eu[e], v = g.ev[e];
            o.s("E "); o.u(g.vq[u]); o.c(' '); o.u(g.vcell[u]); o.c(' '); o.u(g.vq[v]); o.c(' '); o.u(g.vcell[v]); o.c(' '); o.i(g.word(e)[0]); o.c('\n');
            o.maybe_flush();
        }
        for (u32 bi = 0; bi < sr.ncomp; ++bi) {
            u32 c = order[bi];
            o.s("B "); o.u(bi); o.c(' '); o.u(ci.chead[c + 1] - ci.chead[c]); o.c(' '); o.u(ci.ehead[c + 1] - ci.ehead[c]);
            o.c(' '); o.u(cr[c].cyclic ? cr[c].d : 0); o.c(' '); o.u(rho[c]); o.c(' '); o.u(eta[c]);
            o.s(" L");
            if (cr[c].certified) for (u64 s = 0; s < cr[c].d; ++s) { o.c(' '); o.i(cr[c].lambda[s]); }
            o.s(" M");
            for (u32 p = ci.chead[c]; p < ci.chead[c + 1]; ++p) { u32 v = ci.cmem[p]; o.c(' '); o.u(g.vq[v]); o.c(':'); o.u(g.vcell[v]); }
            o.c('\n'); o.maybe_flush();
        }
    }
    printf("{\"event\":\"q75\",\"a\":%lld,\"b\":%lld,\"M\":%llu,\"K\":%u,\"vertices\":%u,\"edges\":%llu,\"blocks\":%u,"
           "\"scc_verified\":%s,\"cyclic\":%llu,\"certified\":%llu,\"uncertified\":%llu,\"max_d\":%llu,\"unused_phase_blocks\":%llu,"
           "\"rho_max\":%llu,\"eta_max\":%llu,\"rank_condition_ok\":%s,\"cyc_condition_ok\":%s,\"bounds_ok\":%s,"
           "\"allowed\":{\"rho_max\":%llu,\"eta_max\":%llu,\"d_max\":%llu},"
           "\"t_enumerate\":%.3f,\"t_analyse\":%.3f,\"t_total\":%.3f}\n",
           a, b, M, K, n, (u64)g.ne(), sr.ncomp, scc_ok ? "true" : "false", cyclic, certified, uncertified, maxd, unused_phase,
           rho_max, eta_max, rank_ok ? "true" : "false", cyc_ok ? "true" : "false", (bounds_ok && rank_ok && cyc_ok) ? "true" : "false",
           rho_max_allowed, eta_max_allowed, d_max_allowed, t1 - t0, t2 - t1, now_sec() - t0);
    fflush(stdout);
}

int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: wgb pipeline|q75 ...\n"); return 1; }
    string mode = argv[1];
    if (mode == "pipeline") run_pipeline(argc, argv);
    else if (mode == "q75") run_q75(argc, argv);
    else die("unknown mode");
    return 0;
}
