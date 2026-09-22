"""共通の数学ルーチン（独立検算B・附録担当）。

すべて整数と fractions.Fraction の厳密演算。浮動小数点・乱数・確率的素数判定は使わない。
定義は proofs/audit-01.md §2–§4 と proofs/audit-03-scope-obstructions.md §2–§3 に従う。
"""
from fractions import Fraction
from math import gcd
import itertools


# ---------------------------------------------------------------- 整数論の基本

def egcd(x, y):
    """拡張 Euclid: (g, s, t) with s*x + t*y = g = gcd(x, y) >= 0."""
    old_r, r = x, y
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        qt = old_r // r
        old_r, r = r, old_r - qt * r
        old_s, s = s, old_s - qt * s
        old_t, t = t, old_t - qt * t
    if old_r < 0:
        old_r, old_s, old_t = -old_r, -old_s, -old_t
    return old_r, old_s, old_t


def modinv(x, m):
    """x の法 m の逆元（0 <= 結果 < m）。可逆でなければ ValueError。"""
    if m == 1:
        return 0
    g, s, _ = egcd(x % m, m)
    if g != 1:
        raise ValueError("not invertible: %d mod %d" % (x, m))
    return s % m


def crt(pairs):
    """pairs = [(r_i, m_i)]（m_i は互いに素）。0 <= x < prod m_i を返す。"""
    x, m = 0, 1
    for r, mi in pairs:
        if gcd(m, mi) != 1:
            raise ValueError("moduli not coprime")
        # x + m*t ≡ r (mod mi)
        t = ((r - x) * modinv(m % mi, mi)) % mi if mi > 1 else 0
        x = x + m * t
        m *= mi
        x %= m
    return x


def trial_factor(n):
    """試し割りによる素因数分解 {p: e}。n >= 1。"""
    assert n >= 1
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def is_prime(n):
    """試し割り（決定的）。"""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def primes_upto(n):
    """Eratosthenes の篩。"""
    if n < 2:
        return []
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def rad(n):
    r = 1
    for p in trial_factor(n):
        r *= p
    return r


def is_squarefree(n):
    return all(e == 1 for e in trial_factor(n).values())


def phi(n):
    r = n
    for p in trial_factor(n):
        r = r // p * (p - 1)
    return r


# ---------------------------------------------------------------- 基本記法

def check_base(a, b):
    return a > b >= 2 and gcd(a, b) == 1


def sigma(a, b):
    """Σ = {1-b, ..., a-1}."""
    return list(range(1 - b, a))


def carry_alphabet(a, b):
    """𝒞(a,b) = {c : 1-b <= c <= a-1, c ≡ b-a (mod 2), gcd(c, ab) = 1}."""
    return [c for c in range(1 - b, a) if (c - (b - a)) % 2 == 0 and gcd(abs(c), a * b) == 1]


def e1(a, b, e):
    return 1 - b <= e <= a - 1


def e3(a, b, K, j, k, e):
    """aj - b(k+1) < eK < a(j+1) - bk（符号付き整数、厳密不等号）。"""
    return a * j - b * (k + 1) < e * K < a * (j + 1) - b * k


def floor_frac(x):
    """Fraction/int の床（負も正しく）。"""
    x = Fraction(x)
    return x.numerator // x.denominator


def frac_part(x):
    x = Fraction(x)
    return x - floor_frac(x)


def solve_linear(bcoef, t, M):
    """b*z ≡ t (mod M) の全解 z（0 <= z < M）。b の逆元を仮定しない。"""
    if M == 1:
        return [0]
    g = gcd(bcoef % M, M) if bcoef % M != 0 else M
    if t % g != 0:
        return []
    bp, Mp, tp = (bcoef % M) // g, M // g, (t % M) // g
    # 注意: t % M を g で割る: t ≡ t%M (mod M) で g | M なので g | t ⟺ g | t%M
    if Mp == 1:
        z0 = 0
    else:
        z0 = (tp * modinv(bp, Mp)) % Mp
    return [z0 + l * Mp for l in range(g)]


def units(M):
    if M == 1:
        return [0]
    return [q for q in range(M) if gcd(q, M) == 1]


def edges_G(a, b, M, K, alphabet=None):
    """一段階完全グラフ G(M,K) の全辺 (q,j,z,k,e)。頂点は V(M,K)。"""
    alph = sigma(a, b) if alphabet is None else alphabet
    us = units(M)
    uset = set(us)
    edges = []
    for q in us:
        for e in alph:
            zs = [z for z in solve_linear(b, a * q + e, M) if z in uset]
            if not zs:
                continue
            for j in range(K):
                for k in range(K):
                    if e3(a, b, K, j, k, e):
                        for z in zs:
                            edges.append((q, j, z, k, e))
    return edges


def edges_Gprime(a, b, R, K):
    """G'(R,K)（audit-03 §3.5）: q ∈ (Z/R)^×（R=1 なら q=0）、e ∈ 𝒞(a,b)、bz ≡ aq+e (R)、E3。"""
    return edges_G(a, b, R, K, alphabet=carry_alphabet(a, b))


# ---------------------------------------------------------------- 非周期二進列

def aperiodic_bits(n):
    """1,0,1,0,0,1,0,0,0,1,...（零の連の長さが 1 ずつ増える）の先頭 n 項。"""
    out = []
    run = 1
    while len(out) < n:
        out.append(1)
        out.extend([0] * run)
        run += 1
    return out[:n]


def has_period(seq, P):
    """有限列 seq が周期 P（全 n で seq[n+P]=seq[n]）を持つか。"""
    return all(seq[i] == seq[i + P] for i in range(len(seq) - P))


# ---------------------------------------------------------------- OB-R の証人と区間

def obr_witness(a, b, R, m):
    """B-1: OB-R の証人条件。dict を返す。"""
    res = {"a": a, "b": b, "R": R, "m": m}
    checks = {}
    checks["a>b>=2"] = a > b >= 2
    checks["gcd(a,b)=1"] = gcd(a, b) == 1
    checks["R>=1"] = R >= 1
    checks["gcd(R,2ab)=1"] = gcd(R, 2 * a * b) == 1
    checks["m>=1"] = m >= 1
    h = 2 * R * m
    d = a - b
    c = d - h
    checks["h=2Rm<=a-1"] = h <= a - 1
    checks["gcd(c,ab)=1"] = gcd(abs(c), a * b) == 1
    res.update({"h": h, "d": d, "c": c})
    accepted = all(checks.values())
    derived = {}
    if accepted:
        derived["1-b<=c"] = 1 - b <= c
        derived["c<d"] = c < d
        derived["d<=a-1"] = d <= a - 1
        derived["c=d mod 2"] = (c - d) % 2 == 0
        derived["c=d mod R"] = (c - d) % R == 0
        derived["gcd(d,ab)=1"] = gcd(d, a * b) == 1
        calph = carry_alphabet(a, b)
        derived["c in C(a,b)"] = c in calph
        derived["d in C(a,b)"] = d in calph
    res["checks"] = checks
    res["accepted"] = accepted
    res["derived"] = derived
    res["derived_all"] = all(derived.values()) if accepted else None
    return res


def psi(a, b, c, x):
    """逆向き写像 ψ_c(x) = (b x + c)/a。"""
    return (b * Fraction(x) + c) / a


def phi_closed(a, b, h, L, x):
    """Φ_L の閉形式 1 + (b/a)^{L+1}(x-1) - (h/a)(b/a)^L。"""
    r = Fraction(b, a)
    return 1 + r ** (L + 1) * (Fraction(x) - 1) - Fraction(h, a) * r ** L


def phi_iter(a, b, c, d, L, x):
    """Φ_L = ψ_d^L ∘ ψ_c を一文字ずつ反復。(最終値, 途中値リスト[ψ_c 直後, 各 ψ_d 後]) を返す。"""
    vals = []
    y = psi(a, b, c, x)
    vals.append(y)
    for _ in range(L):
        y = psi(a, b, d, y)
        vals.append(y)
    return y, vals


def x_fixed(a, b, h, L):
    """x_L = 1 - h b^L / (a^{L+1} - b^{L+1})."""
    return 1 - Fraction(h * b ** L, a ** (L + 1) - b ** (L + 1))


def minimal_L(a, b, h, c, Lmax):
    """max(0,-c/b) < x_L を満たす最小 L >= 0 を整数比較で探索。None なら上限到達。
    (b-τ)(a^{L+1}-b^{L+1}) > h b^{L+1}, τ = max(0,-c)。"""
    tau = max(0, -c)
    aL1, bL1 = a, b
    for L in range(Lmax + 1):
        if (b - tau) * (aL1 - bL1) > h * bL1:
            return L
        aL1 *= a
        bL1 *= b
    return None


def interval_certificate(a, b, h, c, Lmax=5000, full=True):
    """B-2: 不変区間の証明書。dict（合否と数値）を返す。"""
    d = c + h
    t = max(Fraction(0), Fraction(-c, b))
    L = minimal_L(a, b, h, c, Lmax)
    out = {"a": a, "b": b, "h": h, "c": c, "d": d, "threshold": str(t), "Lmax": Lmax}
    if L is None:
        out["status"] = "inconclusive"
        out["L"] = None
        return out
    xL, xL1 = x_fixed(a, b, h, L), x_fixed(a, b, h, L + 1)
    ch = {}
    ch["t<x_L"] = t < xL
    ch["x_L<x_{L+1}"] = xL < xL1
    ch["x_{L+1}<1"] = xL1 < 1
    ch["minimality"] = (x_fixed(a, b, h, L - 1) <= t) if L >= 1 else True
    # 閉形式と反復の一致、不動点
    fL_iter, valsL = phi_iter(a, b, c, d, L, xL)
    fL1_iter, valsL1 = phi_iter(a, b, c, d, L + 1, xL1)
    ch["Phi_L(x_L)=x_L (iter)"] = fL_iter == xL
    ch["Phi_{L+1}(x_{L+1})=x_{L+1} (iter)"] = fL1_iter == xL1
    ch["Phi_L closed=iter at x_L"] = phi_closed(a, b, h, L, xL) == fL_iter
    ch["Phi_{L+1} closed=iter at x_{L+1}"] = phi_closed(a, b, h, L + 1, xL1) == fL1_iter
    mid = (xL + xL1) / 2
    ch["closed=iter at mid (L)"] = phi_closed(a, b, h, L, mid) == phi_iter(a, b, c, d, L, mid)[0]
    ch["closed=iter at mid (L+1)"] = phi_closed(a, b, h, L + 1, mid) == phi_iter(a, b, c, d, L + 1, mid)[0]
    # 両端点の像が I 内
    imgs = {
        "Phi_L(x_L)": fL_iter,
        "Phi_L(x_{L+1})": phi_iter(a, b, c, d, L, xL1)[0],
        "Phi_{L+1}(x_L)": phi_iter(a, b, c, d, L + 1, xL)[0],
        "Phi_{L+1}(x_{L+1})": fL1_iter,
    }
    ch["endpoint images in I"] = all(xL <= v <= xL1 for v in imgs.values())
    # 全途中値が (0,1)
    inter_ok = True
    for x0 in (xL, xL1):
        for LL in (L, L + 1):
            _, vals = phi_iter(a, b, c, d, LL, x0)
            if not all(0 < v < 1 for v in vals):
                inter_ok = False
    ch["intermediate values in (0,1)"] = inter_ok
    out.update({
        "L": L, "x_L": str(xL), "x_{L+1}": str(xL1),
        "U": [d] * L + [c], "V": [d] * (L + 1) + [c],
        "checks": ch, "all_pass": all(ch.values()), "status": "success",
    })
    return out


# ---------------------------------------------------------------- Jacobsthal

def unit_mask(N, primes):
    """[0, 2N) の各整数が N と互いに素かのビット列（N の素因数の倍数を除く）。"""
    n2 = 2 * N
    m = bytearray([1]) * n2
    for p in primes:
        m[0::p] = bytearray(len(m[0::p]))
    return m


def jacobsthal_def(N, primes):
    """定義どおり: 全窓（開始点 0..N-1）に単元が含まれる最小の窓長 J。"""
    m = unit_mask(N, primes)
    pre = [0] * (2 * N + 1)
    for i in range(2 * N):
        pre[i + 1] = pre[i] + m[i]
    J = 1
    while True:
        ok = True
        for s in range(N):
            if pre[s + J] - pre[s] == 0:
                ok = False
                break
        if ok:
            return J
        J += 1
        if J > N + 1:
            raise RuntimeError("no J found")


def jacobsthal_gap(N, primes):
    """単元の最大間隔（巡回差を含む）。"""
    m = unit_mask(N, primes)
    us = [i for i in range(N) if m[i]]
    g = 0
    for i in range(len(us) - 1):
        g = max(g, us[i + 1] - us[i])
    g = max(g, us[0] + N - us[-1])
    return g


def window_unit_counts(N, primes, H):
    """長さ H の全窓（開始点 0..N-1）の単元数のリスト。H <= N を想定（H > N なら 2N まで拡張）。"""
    if H > N:
        # 窓が 2N を超えないよう、N の周期性で拡張する
        reps = (H // N) + 2
        base = unit_mask(N, primes)[:N]
        m = bytes(base) * reps
    else:
        m = unit_mask(N, primes)
    pre = [0] * (len(m) + 1)
    for i in range(len(m)):
        pre[i + 1] = pre[i] + m[i]
    return [pre[s + H] - pre[s] for s in range(N)]


# ---------------------------------------------------------------- 有限歩道の言語

def language(edges, K, n, vertices=None):
    """長さ <= n の歩道の (セル列, 出力語) の集合。edges は (q,j,z,k,e)。
    長さ 0（単独頂点）も含める（全セルが頂点にあるので (j,) が入る）。"""
    adj = {}
    verts = set()
    for (q, j, z, k, e) in edges:
        adj.setdefault((q, j), []).append((z, k, e))
        verts.add((q, j))
        verts.add((z, k))
    if vertices is not None:
        verts |= set(vertices)
    lang = set()
    # 状態: (cellseq, word) -> 到達可能な終点頂点の集合
    cur = {}
    for v in verts:
        cur.setdefault(((v[1],), ()), set()).add(v)
    for key in cur:
        lang.add(key)
    for _ in range(n):
        nxt = {}
        for (cells, word), ends in cur.items():
            for v in ends:
                for (z, k, e) in adj.get(v, ()):
                    key = (cells + (k,), word + (e,))
                    nxt.setdefault(key, set()).add((z, k))
        cur = nxt
        for key in cur:
            lang.add(key)
    return lang
