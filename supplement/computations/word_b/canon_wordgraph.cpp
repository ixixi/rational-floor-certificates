// canon_wordgraph.cpp — canonical form and SHA-256 of a word-labelled graph dump (B's comparison tool).
// Standard library only.  Build: g++ -O2 -std=c++17 -o canon_wordgraph canon_wordgraph.cpp
//
// Usage: canon_wordgraph FILE [--canonical-out PATH]
//
// Accepted inputs:
//   * WORDGRAPH 2 (written by wgb): header with K and primes, rows `V q cell` and
//     `E qu cu qv cv w...`.  Vertices are renumbered by the key
//     (cell, q mod p_1, ..., q mod p_k), where p_1, ..., p_k are the primes in the order used.
//   * The compact dump written by the 5/3 handoff producer (certificate53): first line
//     `vertices edges D`, then one `lo hi` row per vertex (its cell is [lo/D, hi/D)), then rows
//     `u v length w...` with vertex indices.  This format was read from the handoff's recorded
//     small dumps, not from the producer's source.  Its vertex indices are used as they are.
//
// For both, the canonical text is
//   `CANON1 vertices=N edges=M D=K` (the cell denominator; K for WORDGRAPH 2),
//   one line `V lo hi` per vertex in index order,
//   one line `E u v w...` per distinct triple, sorted by (u, v, word) with the word compared
//   lexicographically (a proper prefix first).
// Two dumps describe the same graph under the respective vertex numbering exactly when their
// canonical texts agree; the tool prints their SHA-256 and summary counts as one JSON line.
// For WORDGRAPH 2 input, the key above reproduces the handoff dumps' vertex order on the
// recorded small instance; this is checked by the comparison, never assumed.

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>
#include <numeric>

using namespace std;
typedef unsigned long long u64;
typedef unsigned int u32;

[[noreturn]] static void die(const string& m) { fprintf(stderr, "ERROR: %s\n", m.c_str()); printf("{\"status\":\"error\",\"message\":\"%s\"}\n", m.c_str()); exit(2); }

// ---------------------------------------------------------------- SHA-256 (FIPS 180-4)
struct Sha256 {
    uint32_t h[8]; unsigned char buf[64]; u64 len = 0; size_t n = 0;
    static uint32_t rotr(uint32_t x, int r) { return (x >> r) | (x << (32 - r)); }
    Sha256() { const uint32_t iv[8] = {0x6a09e667u,0xbb67ae85u,0x3c6ef372u,0xa54ff53au,0x510e527fu,0x9b05688cu,0x1f83d9abu,0x5be0cd19u}; memcpy(h, iv, sizeof h); }
    void block(const unsigned char* p) {
        static const uint32_t k[64] = {
            0x428a2f98u,0x71374491u,0xb5c0fbcfu,0xe9b5dba5u,0x3956c25bu,0x59f111f1u,0x923f82a4u,0xab1c5ed5u,0xd807aa98u,0x12835b01u,0x243185beu,0x550c7dc3u,0x72be5d74u,0x80deb1feu,0x9bdc06a7u,0xc19bf174u,
            0xe49b69c1u,0xefbe4786u,0x0fc19dc6u,0x240ca1ccu,0x2de92c6fu,0x4a7484aau,0x5cb0a9dcu,0x76f988dau,0x983e5152u,0xa831c66du,0xb00327c8u,0xbf597fc7u,0xc6e00bf3u,0xd5a79147u,0x06ca6351u,0x14292967u,
            0x27b70a85u,0x2e1b2138u,0x4d2c6dfcu,0x53380d13u,0x650a7354u,0x766a0abbu,0x81c2c92eu,0x92722c85u,0xa2bfe8a1u,0xa81a664bu,0xc24b8b70u,0xc76c51a3u,0xd192e819u,0xd6990624u,0xf40e3585u,0x106aa070u,
            0x19a4c116u,0x1e376c08u,0x2748774cu,0x34b0bcb5u,0x391c0cb3u,0x4ed8aa4au,0x5b9cca4fu,0x682e6ff3u,0x748f82eeu,0x78a5636fu,0x84c87814u,0x8cc70208u,0x90befffau,0xa4506cebu,0xbef9a3f7u,0xc67178f2u};
        uint32_t w[64];
        for (int i = 0; i < 16; ++i) w[i] = (uint32_t)p[4*i] << 24 | (uint32_t)p[4*i+1] << 16 | (uint32_t)p[4*i+2] << 8 | p[4*i+3];
        for (int i = 16; i < 64; ++i) { uint32_t s0 = rotr(w[i-15],7) ^ rotr(w[i-15],18) ^ (w[i-15] >> 3), s1 = rotr(w[i-2],17) ^ rotr(w[i-2],19) ^ (w[i-2] >> 10); w[i] = w[i-16] + s0 + w[i-7] + s1; }
        uint32_t a=h[0],b=h[1],c=h[2],d=h[3],e=h[4],f=h[5],g=h[6],hh=h[7];
        for (int i = 0; i < 64; ++i) {
            uint32_t S1 = rotr(e,6) ^ rotr(e,11) ^ rotr(e,25), ch = (e & f) ^ (~e & g), t1 = hh + S1 + ch + k[i] + w[i];
            uint32_t S0 = rotr(a,2) ^ rotr(a,13) ^ rotr(a,22), mj = (a & b) ^ (a & c) ^ (b & c), t2 = S0 + mj;
            hh = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
        }
        h[0]+=a; h[1]+=b; h[2]+=c; h[3]+=d; h[4]+=e; h[5]+=f; h[6]+=g; h[7]+=hh;
    }
    void update(const void* data, size_t m) {
        const unsigned char* p = (const unsigned char*)data; len += m;
        while (m) { size_t t = min(m, 64 - n); memcpy(buf + n, p, t); n += t; p += t; m -= t; if (n == 64) { block(buf); n = 0; } }
    }
    string hex() {
        u64 bits = len * 8; unsigned char pad = 0x80; update(&pad, 1);
        unsigned char z = 0; while (n != 56) update(&z, 1);
        unsigned char lb[8]; for (int i = 0; i < 8; ++i) lb[i] = (unsigned char)(bits >> (56 - 8*i)); update(lb, 8);
        char out[65]; for (int i = 0; i < 8; ++i) snprintf(out + 8*i, 9, "%08x", h[i]); return string(out, 64);
    }
};

// ---------------------------------------------------------------- fast reader
struct Reader {
    FILE* f; vector<char> buf; size_t pos = 0, end = 0; bool eof = false;
    explicit Reader(const string& path) : buf(1 << 24) { f = fopen(path.c_str(), "rb"); if (!f) die("cannot open " + path); }
    ~Reader() { if (f) fclose(f); }
    int peek() { if (pos == end) { if (eof) return -1; end = fread(buf.data(), 1, buf.size(), f); pos = 0; if (end == 0) { eof = true; return -1; } } return (unsigned char)buf[pos]; }
    int get() { int c = peek(); if (c >= 0) ++pos; return c; }
    string line() { string s; int c; while ((c = get()) >= 0 && c != '\n') s.push_back((char)c); return s; }
    // parses one integer on the current line; returns false at end of line
    bool num(long long& x) {
        int c = peek();
        while (c == ' ') { get(); c = peek(); }
        if (c == '\n' || c < 0) return false;
        bool neg = false; if (c == '-') { neg = true; get(); c = peek(); }
        if (c < '0' || c > '9') die("malformed number");
        long long v = 0; while (c >= '0' && c <= '9') { v = v * 10 + (c - '0'); get(); c = peek(); }
        x = neg ? -v : v; return true;
    }
    void eol() { int c = peek(); while (c == ' ') { get(); c = peek(); } if (c == '\n') get(); else if (c >= 0) die("trailing data on a line"); }
};

struct G {
    u64 D = 0;
    vector<u32> lo, hi;
    vector<u32> eu, ev; vector<u64> off; vector<u32> len; vector<int8_t> ch;
};

static int cmpw(const int8_t* a, u32 la, const int8_t* b, u32 lb) {
    u32 m = min(la, lb);
    for (u32 i = 0; i < m; ++i) if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;   // signed letters
    if (la == lb) return 0; return la < lb ? -1 : 1;
}

static void read_edge_word(Reader& r, G& g, long long L) {
    g.off.push_back(g.ch.size()); g.len.push_back((u32)L);
    for (long long i = 0; i < L; ++i) { long long c; if (!r.num(c)) die("short word"); if (c < -128 || c > 127) die("letter out of range"); g.ch.push_back((int8_t)c); }
}

static G read_wordgraph(Reader& r, const string& header) {
    G g;
    auto field = [&](const string& key) { size_t p = header.find(" " + key + "="); if (p == string::npos) die("header lacks " + key); p += key.size() + 2; size_t q = header.find(' ', p); return header.substr(p, q == string::npos ? string::npos : q - p); };
    g.D = stoull(field("K"));
    vector<u64> primes; { string ps = field("primes"); string cur; for (char c : ps) { if (c == ',') { primes.push_back(stoull(cur)); cur.clear(); } else cur += c; } if (!cur.empty()) primes.push_back(stoull(cur)); }
    u64 nv = stoull(field("vertices")), ne = stoull(field("edges"));
    vector<u64> vq(nv); vector<u32> vc(nv);
    for (u64 i = 0; i < nv; ++i) {
        if (r.get() != 'V') die("expected V row"); long long q, c; if (!r.num(q) || !r.num(c)) die("bad V row"); r.eol(); vq[i] = (u64)q; vc[i] = (u32)c;
        if (i && !(vq[i-1] < vq[i] || (vq[i-1] == vq[i] && vc[i-1] < vc[i]))) die("V rows not strictly sorted");
    }
    // canonical order: (cell, q mod p_1, ..., q mod p_k)
    vector<u32> perm(nv); iota(perm.begin(), perm.end(), 0);
    sort(perm.begin(), perm.end(), [&](u32 x, u32 y) {
        if (vc[x] != vc[y]) return vc[x] < vc[y];
        for (u64 p : primes) { u64 a = vq[x] % p, b = vq[y] % p; if (a != b) return a < b; }
        return false;
    });
    vector<u32> rank(nv); for (u32 i = 0; i < nv; ++i) rank[perm[i]] = i;
    g.lo.resize(nv); g.hi.resize(nv);
    for (u32 i = 0; i < nv; ++i) { g.lo[i] = vc[perm[i]]; g.hi[i] = vc[perm[i]] + 1; }
    auto vid = [&](long long q, long long c) -> u32 {
        size_t lo = 0, hi = nv;
        while (lo < hi) { size_t m = (lo + hi) / 2; if (vq[m] < (u64)q || (vq[m] == (u64)q && vc[m] < (u32)c)) lo = m + 1; else hi = m; }
        if (lo == nv || vq[lo] != (u64)q || vc[lo] != (u32)c) die("edge endpoint is not a vertex");
        return rank[lo];
    };
    for (u64 e = 0; e < ne; ++e) {
        if (r.get() != 'E') die("expected E row"); long long a, b, c, d; if (!r.num(a) || !r.num(b) || !r.num(c) || !r.num(d)) die("bad E row");
        g.eu.push_back(vid(a, b)); g.ev.push_back(vid(c, d));
        g.off.push_back(g.ch.size()); long long x; u32 L = 0;
        while (r.num(x)) { if (x < -128 || x > 127) die("letter out of range"); g.ch.push_back((int8_t)x); ++L; }
        if (L == 0) die("empty word"); g.len.push_back(L); r.eol();
    }
    if (r.peek() >= 0) die("trailing rows");
    return g;
}

static G read_compact(Reader& r, const string& header) {
    G g;
    long long nv, ne, D;
    if (sscanf(header.c_str(), "%lld %lld %lld", &nv, &ne, &D) != 3) die("bad compact header");
    g.D = (u64)D; g.lo.resize(nv); g.hi.resize(nv);
    for (long long i = 0; i < nv; ++i) { long long a, b; if (!r.num(a) || !r.num(b)) die("bad vertex row"); r.eol(); g.lo[i] = (u32)a; g.hi[i] = (u32)b; }
    for (long long e = 0; e < ne; ++e) {
        long long u, v, L; if (!r.num(u) || !r.num(v) || !r.num(L)) die("bad edge row");
        if (u < 0 || u >= nv || v < 0 || v >= nv || L <= 0) die("bad edge endpoints or length");
        g.eu.push_back((u32)u); g.ev.push_back((u32)v); read_edge_word(r, g, L); r.eol();
    }
    if (r.peek() >= 0) die("trailing rows");
    return g;
}

int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: canon_wordgraph FILE [--canonical-out PATH]\n"); return 1; }
    string path = argv[1], canon_out;
    for (int i = 2; i < argc; ++i) { string k = argv[i]; if (k == "--canonical-out" && i + 1 < argc) canon_out = argv[++i]; else die("unknown option " + k); }
    Reader r(path);
    string header = r.line();
    bool wg = header.rfind("WORDGRAPH 2 ", 0) == 0;
    G g = wg ? read_wordgraph(r, header) : read_compact(r, header);
    u64 nv = g.lo.size(), ne = g.eu.size();
    vector<u32> ep(ne); iota(ep.begin(), ep.end(), 0);
    const int8_t* C = g.ch.data();
    sort(ep.begin(), ep.end(), [&](u32 x, u32 y) {
        if (g.eu[x] != g.eu[y]) return g.eu[x] < g.eu[y];
        if (g.ev[x] != g.ev[y]) return g.ev[x] < g.ev[y];
        return cmpw(C + g.off[x], g.len[x], C + g.off[y], g.len[y]) < 0;
    });
    u64 dup = 0, letters = 0, maxlen = 0;
    for (u64 i = 1; i < ne; ++i) { u32 a = ep[i-1], b = ep[i]; if (g.eu[a] == g.eu[b] && g.ev[a] == g.ev[b] && cmpw(C + g.off[a], g.len[a], C + g.off[b], g.len[b]) == 0) ++dup; }
    Sha256 sh; FILE* co = canon_out.empty() ? nullptr : fopen(canon_out.c_str(), "wb");
    if (!canon_out.empty() && !co) die("cannot open canonical output");
    string buf; buf.reserve(1 << 22);
    auto emit = [&]() { sh.update(buf.data(), buf.size()); if (co) fwrite(buf.data(), 1, buf.size(), co); buf.clear(); };
    auto put_u = [&](u64 x) { char t[24]; int k = 0; if (!x) { buf.push_back('0'); return; } while (x) { t[k++] = char('0' + x % 10); x /= 10; } while (k) buf.push_back(t[--k]); };
    u64 dedup_edges = 0;
    buf += "CANON1 vertices="; put_u(nv); buf += " edges="; put_u(ne - dup); buf += " D="; put_u(g.D); buf.push_back('\n');
    for (u64 i = 0; i < nv; ++i) { buf += "V "; put_u(g.lo[i]); buf.push_back(' '); put_u(g.hi[i]); buf.push_back('\n'); if (buf.size() > (1u << 22)) emit(); }
    for (u64 i = 0; i < ne; ++i) {
        u32 e = ep[i];
        if (i) { u32 f = ep[i-1]; if (g.eu[e] == g.eu[f] && g.ev[e] == g.ev[f] && cmpw(C + g.off[e], g.len[e], C + g.off[f], g.len[f]) == 0) continue; }
        ++dedup_edges; letters += g.len[e]; if (g.len[e] > maxlen) maxlen = g.len[e];
        buf += "E "; put_u(g.eu[e]); buf.push_back(' '); put_u(g.ev[e]);
        for (u32 j = 0; j < g.len[e]; ++j) { int c = C[g.off[e] + j]; buf.push_back(' '); if (c < 0) { buf.push_back('-'); c = -c; } put_u((u64)c); }
        buf.push_back('\n'); if (buf.size() > (1u << 22)) emit();
    }
    emit(); if (co) fclose(co);
    printf("{\"status\":\"ok\",\"format\":\"%s\",\"vertices\":%llu,\"edges\":%llu,\"duplicate_rows\":%llu,\"letters\":%llu,\"max_word_length\":%llu,\"D\":%llu,\"sha256\":\"%s\"}\n",
           wg ? "WORDGRAPH2" : "compact", nv, dedup_edges, dup, letters, maxlen, g.D, sh.hex().c_str());
    return 0;
}
