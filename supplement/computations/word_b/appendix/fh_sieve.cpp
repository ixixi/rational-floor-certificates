// fh_sieve.cpp — 有限高さ篩（独立検算B・附録担当）。整数演算のみ（__int128）。
// usage: fh_sieve a b N out_prefix
// 出力: out_prefix.counts.json, out_prefix.candidates.txt（"seed c_0 ... c_{N-1}" 行）
// 数学的条件は proofs/audit-04-appendices.md §3.3.2–3.3.3、audit-03 §3.1（アルファベット）、§3.15（区間更新）。
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <string>
#include <algorithm>
#include <numeric>

typedef __int128 i128;
typedef unsigned __int128 u128;

static std::string i128str(i128 v) {
    if (v == 0) return "0";
    bool neg = v < 0;
    u128 u = neg ? (u128)(-v) : (u128)v;
    std::string s;
    while (u) { s += char('0' + (int)(u % 10)); u /= 10; }
    if (neg) s += '-';
    std::reverse(s.begin(), s.end());
    return s;
}

static u128 mulmod(u128 x, u128 y, u128 m) {  // 倍加法。x,y < m < 2^126 で溢れない
    x %= m; y %= m;
    u128 r = 0;
    while (y) {
        if (y & 1) { r += x; if (r >= m) r -= m; }
        x += x; if (x >= m) x -= m;
        y >>= 1;
    }
    return r;
}

static i128 egcd(i128 a, i128 b, i128 &x, i128 &y) {
    if (b == 0) { x = 1; y = 0; return a; }
    i128 x1, y1;
    i128 g = egcd(b, a % b, x1, y1);
    x = y1; y = x1 - (a / b) * y1;
    return g;
}

static u128 invmod(u128 a, u128 m) {
    i128 x, y;
    i128 g = egcd((i128)(a % m), (i128)m, x, y);
    if (g != 1) { fprintf(stderr, "invmod: not invertible\n"); exit(3); }
    i128 r = x % (i128)m; if (r < 0) r += (i128)m;
    return (u128)r;
}

static long long gcdll(long long a, long long b) { while (b) { long long t = a % b; a = b; b = t; } return a < 0 ? -a : a; }

static int a, b, N;
static std::vector<int> alph, rp;
static std::vector<long long> A, rejI, rejR;
static std::vector<std::vector<int>> bpow, ainvp;   // [prime][depth]
static std::vector<u128> bpowN, apow_mod;            // b^j, a^j mod b^j
static u128 bN, invaN;
static long long leaves = 0, cntSmall = 0, cntEven = 0, cntRoots = 0, cntCand = 0, seedFail = 0;
static u128 maxSeed = 0;
static FILE *fc;
static int word[64];
static i128 Cj[64], Lv[64], Uv[64], Bv[64];
static int Rj[16][64];
static uint64_t maskv[16][64];

static long long powmod_ll(long long x, long long e, long long m) { long long r = 1 % m; x %= m; if (x < 0) x += m; while (e) { if (e & 1) r = r * x % m; x = x * x % m; e >>= 1; } return r; }

static void dfs(int j) {
    A[j]++;
    if (j == N) {
        leaves++;
        i128 cn = Cj[N] % (i128)bN; if (cn < 0) cn += (i128)bN;
        u128 s = mulmod((bN - (u128)cn) % bN, invaN, bN);   // FH-seed
        bool ok = true;
        for (int jj = 1; jj <= N; jj++) {                      // a^jj s + C_jj ≡ 0 (mod b^jj)
            u128 m = bpowN[jj];
            u128 t = mulmod(apow_mod[jj], s % m, m);
            i128 cj = Cj[jj] % (i128)m; if (cj < 0) cj += (i128)m;
            t = (t + (u128)cj) % m;
            if (t != 0) { ok = false; break; }
        }
        if (!ok) seedFail++;
        if (s > maxSeed) maxSeed = s;
        if (s <= (u128)std::max(a, N + 1)) cntSmall++;
        else if ((s & 1) == 0) cntEven++;
        else {
            bool rej = false;
            for (size_t i = 0; i < rp.size(); i++) {
                int p = rp[i]; int sm = (int)(s % (u128)p);
                if (maskv[i][N] & (1ULL << sm)) { rej = true; break; }
            }
            if (rej) cntRoots++;
            else {
                cntCand++;
                fprintf(fc, "%s", i128str((i128)s).c_str());
                for (int k = 0; k < N; k++) fprintf(fc, " %d", word[k]);
                fprintf(fc, "\n");
            }
        }
        return;
    }
    for (int c : alph) {
        i128 B2 = (i128)b * Bv[j];
        i128 L2 = (i128)a * Lv[j] - (i128)c * Bv[j]; if (L2 < 0) L2 = 0;
        i128 U2 = (i128)a * Uv[j] - (i128)c * Bv[j]; if (U2 > B2) U2 = B2;
        if (L2 >= U2) { rejI[j + 1]++; continue; }
        bool cover = false;
        for (size_t i = 0; i < rp.size(); i++) {
            int p = rp[i];
            long long cm = ((long long)c % p + p) % p;
            long long r = ((long long)Rj[i][j] - cm * bpow[i][j] % p * ainvp[i][j]) % p;
            if (r < 0) r += p;
            Rj[i][j + 1] = (int)r;
            maskv[i][j + 1] = maskv[i][j] | (1ULL << r);
            if (__builtin_popcountll(maskv[i][j + 1]) == p) cover = true;
        }
        if (cover) { rejR[j + 1]++; continue; }
        word[j] = c;
        Cj[j + 1] = (i128)a * Cj[j] + (i128)bpowN[j] * (i128)c;
        Lv[j + 1] = L2; Uv[j + 1] = U2; Bv[j + 1] = B2;
        dfs(j + 1);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: fh_sieve a b N out_prefix\n"); return 2; }
    a = atoi(argv[1]); b = atoi(argv[2]); N = atoi(argv[3]);
    std::string prefix = argv[4];
    if (!(a > b && b >= 2 && gcdll(a, b) == 1) || N < 1 || N > 60) { fprintf(stderr, "bad parameters\n"); return 2; }
    // アルファベット 𝒞(a,b)
    for (int c = 1 - b; c <= a - 1; c++)
        if (((c - (b - a)) % 2) == 0 && gcdll(c < 0 ? -c : c, (long long)a * b) == 1) alph.push_back(c);
    // 根集合の素数: 奇素数 p <= N+1, p ∤ ab
    for (int p = 3; p <= N + 1; p += 2) {
        bool pr = true; for (int d = 3; d * d <= p; d += 2) if (p % d == 0) { pr = false; break; }
        if (pr && ((long long)a * b) % p != 0) rp.push_back(p);
    }
    if (rp.size() > 16) { fprintf(stderr, "too many root primes\n"); return 2; }
    A.assign(N + 1, 0); rejI.assign(N + 2, 0); rejR.assign(N + 2, 0);
    bpow.assign(rp.size(), std::vector<int>(N + 1)); ainvp.assign(rp.size(), std::vector<int>(N + 1));
    for (size_t i = 0; i < rp.size(); i++) {
        int p = rp[i];
        long long ainv = powmod_ll(a, p - 2, p);
        for (int j = 0; j <= N; j++) { bpow[i][j] = (int)powmod_ll(b, j, p); ainvp[i][j] = (int)powmod_ll(ainv, j + 1, p); }
        Rj[i][0] = 0; maskv[i][0] = 1ULL;  // R_0 = 0
    }
    bpowN.assign(N + 1, 1); for (int j = 1; j <= N; j++) bpowN[j] = bpowN[j - 1] * (u128)b;
    bN = bpowN[N];
    apow_mod.assign(N + 1, 0);
    for (int j = 1; j <= N; j++) { u128 m = bpowN[j]; u128 r = 1 % m; for (int k = 0; k < j; k++) r = mulmod(r, (u128)a % m, m); apow_mod[j] = r; }
    invaN = invmod(apow_mod[N], bN);
    Cj[0] = 0; Lv[0] = 0; Uv[0] = 1; Bv[0] = 1;
    fc = fopen((prefix + ".candidates.txt").c_str(), "w");
    if (!fc) { fprintf(stderr, "cannot open output\n"); return 2; }
    dfs(0);
    fclose(fc);
    FILE *fo = fopen((prefix + ".counts.json").c_str(), "w");
    fprintf(fo, "{\n \"a\": %d, \"b\": %d, \"N\": %d,\n \"alphabet\": [", a, b, N);
    for (size_t i = 0; i < alph.size(); i++) fprintf(fo, "%s%d", i ? ", " : "", alph[i]);
    fprintf(fo, "],\n \"root_primes\": [");
    for (size_t i = 0; i < rp.size(); i++) fprintf(fo, "%s%d", i ? ", " : "", rp[i]);
    fprintf(fo, "],\n \"A\": [");
    for (int j = 0; j <= N; j++) fprintf(fo, "%s%lld", j ? ", " : "", A[j]);
    fprintf(fo, "],\n \"rejected_interval_by_depth\": [");
    for (int j = 0; j <= N; j++) fprintf(fo, "%s%lld", j ? ", " : "", rejI[j]);
    fprintf(fo, "],\n \"rejected_roots_by_depth\": [");
    for (int j = 0; j <= N; j++) fprintf(fo, "%s%lld", j ? ", " : "", rejR[j]);
    fprintf(fo, "],\n \"leaves\": {\"total\": %lld, \"small\": %lld, \"even\": %lld, \"roots\": %lld, \"candidates\": %lld},\n", leaves, cntSmall, cntEven, cntRoots, cntCand);
    fprintf(fo, " \"seed_consistency_failures\": %lld,\n \"max_seed\": \"%s\",\n \"b_pow_N\": \"%s\",\n \"small_threshold\": %d\n}\n", seedFail, i128str((i128)maxSeed).c_str(), i128str((i128)bN).c_str(), std::max(a, N + 1));
    fclose(fo);
    return 0;
}
