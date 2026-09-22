#!/usr/bin/env python3
"""B-R1: REC-FIN（audit-04 §3.1.2）。全二進語（長さ<=8）、m∈{2,3}、L∈{0,1,2}、全コピー塔、全置換対、全初期状態で
(COPY)、(REC-copy) 全部分集合、H_k=G_{S_k}、帰還 G_n(x)=x、接頭語帰還を検査。非置換写像での反例も探す。
写像はタプル、compose(f,g)=f∘g（g を先に適用）。"""
import itertools
import json


def compose(f, g):
    return tuple(f[g[x]] for x in range(len(g)))


def G_prefix(w, n, maps, m):
    G = tuple(range(m))
    for i in range(n):
        G = compose(maps[w[i]], G)   # G_{i+1} = f_{w_i} ∘ G_i
    return G


def copy_ok(w, ts, L):
    """(COPY): w[t_k : t_k+S_{k-1}+L] = w[0 : S_{k-1}+L] for all k, and |w| >= S_m + L."""
    S = 0
    for t in ts:
        if len(w) < t + S + L or w[t:t + S + L] != w[0:S + L]:
            return False
        S += t
    return len(w) >= S + L


def check_tower(w, ts, L, maps, m):
    """REC-FIN の結論と補助等式。失敗があれば理由文字列、なければ None。"""
    S = [0]
    for t in ts:
        S.append(S[-1] + t)
    G = {n: G_prefix(w, n, maps, m) for n in range(len(w) + 1)}
    idx = list(range(len(ts)))
    for h in range(0, len(ts) + 1):
        for sub in itertools.combinations(idx, h):
            n = sum(ts[i] for i in sub)
            comp = tuple(range(m))          # G_{t_{i_1}} ∘ G_{t_{i_2}} ∘ ... ∘ G_{t_{i_h}}
            for i in sub:
                comp = compose(comp, G[ts[i]])
            if comp != G[n]:
                return "REC-copy fails for subset %s" % (sub,)
            if w[n:n + L] != w[0:L]:
                return "prefix return fails for subset %s" % (sub,)
    H = [tuple(range(m))]
    for k, t in enumerate(ts):
        H.append(compose(H[-1], G[t]))    # H_k = H_{k-1} ∘ G_{t_k}
        if H[-1] != G[S[k + 1]]:
            return "H_k != G_{S_k} at k=%d" % (k + 1,)
    for x in range(m):
        found = False
        for i in range(len(ts) + 1):
            for j in range(i + 1, len(ts) + 1):
                n = sum(ts[i:j])
                if G[n][x] == x and w[n:n + L] == w[0:L]:
                    found = True
        if not found:
            return "no return for x=%d" % x
    return None


def main():
    perms = {m: list(itertools.permutations(range(m))) for m in (2, 3)}
    stats = {"towers": 0, "checks": 0}
    fails = []
    for m in (2, 3):
        for n in range(1, 9):
            for w in itertools.product((0, 1), repeat=n):
                for L in (0, 1, 2):
                    for ts in itertools.product(range(1, n + 1), repeat=m):
                        if sum(ts) + L > n or not copy_ok(w, ts, L):
                            continue
                        stats["towers"] += 1
                        for f0 in perms[m]:
                            for f1 in perms[m]:
                                stats["checks"] += 1
                                r = check_tower(w, ts, L, {0: f0, 1: f1}, m)
                                if r is not None:
                                    fails.append({"m": m, "w": w, "ts": ts, "L": L, "f0": f0, "f1": f1, "reason": r})
    counter = None
    for m in (2, 3):
        allmaps = list(itertools.product(range(m), repeat=m))
        for n in range(1, 7):
            for w in itertools.product((0, 1), repeat=n):
                for ts in itertools.product(range(1, n + 1), repeat=m):
                    if sum(ts) > n or not copy_ok(w, ts, 0):
                        continue
                    for f0 in allmaps:
                        for f1 in allmaps:
                            if len(set(f0)) == m and len(set(f1)) == m:
                                continue
                            r = check_tower(w, ts, 0, {0: f0, 1: f1}, m)
                            if r is not None and r.startswith("no return"):
                                counter = {"m": m, "w": w, "ts": ts, "f0": f0, "f1": f1, "reason": r}
                                break
                        if counter:
                            break
                    if counter:
                        break
                if counter:
                    break
            if counter:
                break
        if counter:
            break
    all_ok = not fails and counter is not None
    out = {"check": "B-R1 REC-FIN", "n_copy_towers": stats["towers"], "n_checks": stats["checks"], "n_failures": len(fails), "failures": fails[:10],
           "non_permutation_counterexample": counter, "all_pass": all_ok, "status": "success",
           "summary": "%d copy towers x permutation pairs = %d checks, failures=%d; non-permutation counterexample found=%s" % (stats["towers"], stats["checks"], len(fails), counter is not None)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
