#!/usr/bin/env python3
"""Post-checks of the Q75GRAPH 2 dump against the definitions of the waiting-time certificate.

Same-provenance self-check by implementation A (not independent B). Reads only
the text dump and checks:
  Q1 vertex set == all legal states {(q,j): 0<=q<M, gcd(q,M)=1, 0<=j<K}.
  Q2 edge set == literal enumeration: for every legal (q,j), carry c, every
     solution z of b*z = a*q + c (mod M) handled without assuming b invertible
     (g = gcd(b,M) and all g lifts), unit z only, and every k with the strict
     inequalities a*j - b*(k+1) < c*K < a*(j+1) - b*k (literal loop over k).
  Q3 blocks partition the vertex set; blocks == strongly connected components
     (iterative Tarjan recomputed here); ids follow the smallest-vertex order.
  Q4 periods and phases: for every cyclic block the period recomputed from a
     BFS potential equals the dumped period; phase(v) := (potential of v) mod
     period with phase 0 at the smallest vertex; every internal edge u->v has
     phase(v) == phase(u)+1 and carry == labels[phase(u)]; every label used;
     acyclic blocks have period 0 and no labels.
  Q5 ranks: for every inter-block edge C->D, rho(D) >= rho(C)+1 and
     eta(D) >= eta(C) + [D cyclic]; rho >= 1; eta >= [C cyclic]; and rho, eta
     equal the canonical longest-path values recomputed here.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from math import gcd
from pathlib import Path

from postcheck_wordgraph import tarjan
from wg_format import read_q75


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dumps", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    header, vertices, edges, blocks = read_q75(args.dumps / "q75.txt")
    a, b, M, K = header["a"], header["b"], header["M"], header["K"]
    carries = [c for c in range(1 - b, a) if (c - (b - a)) % 2 == 0 and gcd(c, a * b) == 1]
    rep: dict = dict(kind="same-provenance postcheck by implementation A (not independent B)", a=a, b=b, M=M, K=K, carries=carries)
    rep["header_counts_ok"] = (header["vertices"] == len(vertices) and header["edges"] == len(edges) and header["blocks"] == len(blocks))
    legal = [(q, j) for q in range(M) if gcd(q, M) == 1 for j in range(K)]
    rep["Q1_vertices_equal_all_legal_states"] = (vertices == legal)
    rep["legal_state_count"] = len(legal)
    g = gcd(b, M)
    Mg = M // g
    inv_bg = pow(b // g, -1, Mg) if Mg > 1 else 0
    cellsets = {}
    for j in range(K):
        for c in carries:
            cellsets[j, c] = [k for k in range(K) if a * j - b * (k + 1) < c * K < a * (j + 1) - b * k]
    lit = set()
    for q in range(M):
        if gcd(q, M) != 1:
            continue
        for c in carries:
            t = a * q + c
            if t % g:
                continue
            z0 = (t // g) * inv_bg % Mg if Mg > 1 else 0
            for l in range(g):
                z = z0 + l * Mg
                if gcd(z, M) != 1:
                    continue
                for j in range(K):
                    for k in cellsets[j, c]:
                        lit.add((q, j, z, k, c))
    eset = set(edges)
    rep["Q2_edges_equal_literal_enumeration"] = (lit == eset and len(eset) == len(edges) and edges == sorted(edges))
    rep["Q2_literal_edge_count"] = len(lit)
    rep["Q2_gcd_b_M"] = g
    owner = {}
    for i, blk in enumerate(blocks):
        for v in blk["members"]:
            if v in owner:
                raise RuntimeError("vertex in two blocks")
            owner[v] = i
        if blk["members"] != sorted(blk["members"]) or len(blk["members"]) != blk["size"]:
            raise RuntimeError("block member list malformed")
    ids_ok = all(blk["id"] == i for i, blk in enumerate(blocks)) and all(blocks[i]["members"][0] < blocks[i + 1]["members"][0] for i in range(len(blocks) - 1))
    rep["Q3_blocks_partition_vertices"] = (set(owner) == set(vertices) and len(owner) == len(vertices)) and ids_ok
    idx = {v: i for i, v in enumerate(vertices)}
    adj = [[] for _ in vertices]
    for q, j, z, k, c in edges:
        adj[idx[(q, j)]].append((idx[(z, k)], (c,)))
    comp, ncomp = tarjan(len(vertices), adj)
    scc_sets = defaultdict(set)
    for i, v in enumerate(vertices):
        scc_sets[comp[i]].add(v)
    rep["Q3_blocks_equal_sccs"] = ({frozenset(s) for s in scc_sets.values()} == {frozenset(b_["members"]) for b_ in blocks})
    rep["blocks"] = len(blocks)
    # Q4: recompute period and phases from a BFS potential (root = smallest vertex)
    internal = defaultdict(list)
    for q, j, z, k, c in edges:
        u, v = (q, j), (z, k)
        if owner[u] == owner[v]:
            internal[owner[u]].append((u, v, c))
    q4 = True
    period_equal = True
    for i, blk in enumerate(blocks):
        ies = internal.get(i, [])
        if len(ies) != blk["internal"]:
            q4 = False
        if not ies:
            if blk["period"] != 0 or blk["labels"]:
                q4 = False
            continue
        out = defaultdict(list)
        for u, v, c in ies:
            out[u].append(v)
        root = blk["members"][0]
        h = {root: 0}
        queue = [root]
        for u in queue:
            for v in out[u]:
                if v not in h:
                    h[v] = h[u] + 1
                    queue.append(v)
        if set(h) != set(blk["members"]):
            q4 = False
            continue
        d = 0
        for u, v, c in ies:
            d = gcd(d, abs(h[u] + 1 - h[v]))
        if d != blk["period"]:
            period_equal = False
        if d < 1 or len(blk["labels"]) != blk["period"]:
            q4 = False
            continue
        used = set()
        for u, v, c in ies:
            ph = h[u] % d
            if (h[v] - h[u] - 1) % d != 0 or blk["labels"][ph] != c:
                q4 = False
            used.add(ph)
        if used != set(range(d)):
            q4 = False
    rep["Q4_phase_labels_consistent"] = q4
    rep["Q4_period_equals_recomputed_gcd"] = period_equal
    q5 = True
    dag = defaultdict(list)
    indeg = [0] * len(blocks)
    for q, j, z, k, c in edges:
        cu, cv = owner[(q, j)], owner[(z, k)]
        if cu != cv:
            bu, bv = blocks[cu], blocks[cv]
            if not (bv["rho"] >= bu["rho"] + 1 and bv["eta"] >= bu["eta"] + (1 if bv["internal"] > 0 else 0)):
                q5 = False
            dag[cu].append(cv)
            indeg[cv] += 1
    for blk in blocks:
        if not (blk["rho"] >= 1 and blk["eta"] >= (1 if blk["internal"] > 0 else 0)):
            q5 = False
    rep["Q5_rank_inequalities"] = q5
    rho = [1] * len(blocks)
    eta = [1 if blk["internal"] > 0 else 0 for blk in blocks]
    ready = [i for i in range(len(blocks)) if indeg[i] == 0]
    done = 0
    while ready:
        ccur = ready.pop()
        done += 1
        for dnext in dag[ccur]:
            rho[dnext] = max(rho[dnext], rho[ccur] + 1)
            eta[dnext] = max(eta[dnext], eta[ccur] + (1 if blocks[dnext]["internal"] > 0 else 0))
            indeg[dnext] -= 1
            if indeg[dnext] == 0:
                ready.append(dnext)
    rep["Q5_condensation_acyclic"] = (done == len(blocks))
    rep["Q5_rho_eta_equal_canonical_longest_path"] = all(rho[i] == blk["rho"] and eta[i] == blk["eta"] for i, blk in enumerate(blocks))
    rep["max_rho"] = max(rho)
    rep["max_eta"] = max(eta)
    rep["max_period"] = max(blk["period"] for blk in blocks)
    rep["cyclic_blocks"] = sum(1 for blk in blocks if blk["internal"] > 0)
    rep["edges"] = len(edges)
    rep["all_passed"] = rep["header_counts_ok"] and all(v for k, v in rep.items() if k.startswith("Q"))
    args.out.write_text(json.dumps(rep, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in rep.items() if k.startswith("Q") or k in ("all_passed", "max_rho", "max_eta", "max_period")}))
    if not rep["all_passed"]:
        sys.exit(1)


if __name__ == "__main__":
    main()
