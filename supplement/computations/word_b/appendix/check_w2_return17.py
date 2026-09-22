#!/usr/bin/env python3
"""B-W2: RETURN-17（研究メモ §13.3、audit-04 §3.5.4）。法 17 の辺表、自己ループ、非巡回性、順位表、(111,109) との比較。"""
import json
from math import gcd
from obmath import modinv
from check_w1_return_words import U97, V97, forward_res

MEMO_EDGES = {(4, "U", 16), (4, "V", 16), (5, "U", 1), (6, "V", 4), (8, "V", 9), (9, "U", 9), (10, "V", 14), (11, "U", 13), (11, "V", 8), (14, "U", 2), (15, "U", 4), (16, "V", 12)}
RANK = {1: 0, 2: 0, 3: 0, 4: 2, 5: 1, 6: 3, 7: 0, 8: 1, 9: 0, 10: 2, 11: 2, 12: 0, 13: 0, 14: 1, 15: 3, 16: 1}


def edges_mod(a, b, p):
    E = set()
    for q in range(1, p):
        for name, w in (("U", U97), ("V", V97)):
            seq = forward_res(a, b, w, q, p)
            if all(v != 0 for v in seq):
                E.add((q, name, seq[-1]))
    return E


def acyclic(E, p):
    adj = {}
    for (u, _, v) in E:
        if u != v:
            adj.setdefault(u, set()).add(v)
    color = {}

    def dfs(u):
        color[u] = 1
        for v in adj.get(u, ()):
            if color.get(v) == 1:
                return False
            if color.get(v) is None and not dfs(v):
                return False
        color[u] = 2
        return True
    return all(dfs(u) for u in range(1, p) if color.get(u) is None)


def main():
    p = 17
    E = edges_mod(9, 7, p)
    ch = {}
    ch["12 edges match memo"] = E == MEMO_EDGES and len(E) == 12
    loops = {e for e in E if e[0] == e[2]}
    ch["only self-loop is 9-U->9"] = loops == {(9, "U", 9)}
    ch["acyclic without self-loops (DFS)"] = acyclic(E, p)
    ch["rank strictly decreases on all non-loop edges"] = all(RANK[v] < RANK[u] for (u, _, v) in E if u != v)
    E2 = edges_mod(111, 109, p)
    ch["(111,109) edge table identical"] = E2 == E
    seq = forward_res(111, 109, U97, 713, 715)
    ch["(111,109): U from 713 mod 715 does not return / hits non-unit"] = seq[-1] != 713 or any(gcd(v, 715) != 1 for v in seq)
    all_ok = all(ch.values())
    out = {"check": "B-W2 RETURN-17", "edges": sorted(E), "self_loops": sorted(loops), "edges_111_109": sorted(E2), "U_711_109_from_713_mod_715": seq,
           "checks": ch, "all_pass": all_ok, "status": "success",
           "summary": "mod 17: %d edges (memo match=%s), self-loop only 9-U->9=%s, acyclic=%s, rank decrease=%s; (111,109) same table=%s, U not a return word mod 715=%s" % (
               len(E), ch["12 edges match memo"], ch["only self-loop is 9-U->9"], ch["acyclic without self-loops (DFS)"], ch["rank strictly decreases on all non-loop edges"],
               ch["(111,109) edge table identical"], ch["(111,109): U from 713 mod 715 does not return / hits non-unit"])}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
