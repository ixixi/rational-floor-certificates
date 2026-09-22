#!/usr/bin/env python3
"""Post-checks of implementation A's WORDGRAPH 2 dumps against the mathematical definitions.

This is a same-provenance self-check written by implementation A's author.
It is NOT the independent verification B and shares nothing with B. It reads
only the normalized text dumps (never the C++ internals) and recomputes, from
the definitions in the research memo (F3, W2-W4), what each stage should be:

  P1  stage 0 input  == literal one-step graph: all (j, k, c) with the strict
      inequalities a*j - b*(k+1) < c*K < a*(j+1) - b*k, vertices = all cells.
  P2  stage s input  == lift of the stage s-1 output by prime p_s: for every
      distinct edge and every start residue r in 1..p-1 the residue is followed
      letter by letter, z <- (a*z + c) * b^{-1} mod p, and the edge survives
      only if every intermediate residue (including the last) is nonzero;
      vertex names are combined by CRT; states without edges are dropped.
  P3  stage s output == prune of the stage s input: strongly connected blocks
      (iterative Tarjan), cyclic blocks, potential h from the smallest vertex,
      d = gcd of |h(u)+|w|-h(v)| over internal edges, per-letter phase labels,
      retained (uncertified) blocks, anchors = vertices of retained out-degree
      >= 2 (else the smallest vertex of the block), chain compression.
  C   the counts (vertices, edges, cyclic, certified, retained vertices,
      compressed vertices/edges) recomputed here versus the C++ summary line.

Usage: python3 postcheck_wordgraph.py --case five-halves --dumps DIR --summary run_a.jsonl --out report.json
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import defaultdict
from math import gcd
from pathlib import Path

from wg_format import check_wordgraph_order, read_wordgraph

CASES = {
    "five-halves": dict(a=5, b=2, K=4, carries=[-1, 1, 3], primes=[3, 7, 11, 13, 17, 19, 23, 29, 31]),
    "cross-75": dict(a=7, b=5, K=2048, carries=[-4, -2, 2, 4, 6], primes=[3, 11, 13]),
}
sys.setrecursionlimit(10000)


def literal_initial(a: int, b: int, K: int, carries: list[int]):
    vertices = [(0, j) for j in range(K)]
    edges = set()
    for j in range(K):
        aj, aj1 = a * j, a * (j + 1)
        for c in carries:
            cK = c * K
            for k in range(K):
                if aj - b * (k + 1) < cK < aj1 - b * k:
                    edges.add((0, j, 0, k, (c,)))
    return vertices, edges


def lift(a: int, b: int, prev_edges, modulus_old: int, p: int):
    inv_b = pow(b, -1, p)
    inv_m = pow(modulus_old % p, -1, p)
    cache: dict[tuple[int, ...], list[int | None]] = {}

    def follow(word):
        table = cache.get(word)
        if table is None:
            table = [None] * p
            for r in range(1, p):
                z = r
                for c in word:
                    z = (a * z + c) * inv_b % p
                    if z == 0:
                        break
                else:
                    table[r] = z
            cache[word] = table
        return table

    def combine(q: int, r: int) -> int:
        return q + modulus_old * ((r - q) * inv_m % p)

    edges = set()
    for q, j, z, k, word in prev_edges:
        table = follow(word)
        for r in range(1, p):
            t = table[r]
            if t is not None:
                edges.add((combine(q, r), j, combine(z, t), k, word))
    vertices = sorted({(q, j) for q, j, *_ in edges} | {(z, k) for _, _, z, k, _ in edges})
    return vertices, edges, len(cache)


def tarjan(n: int, adj):
    index = [-1] * n
    low = [0] * n
    onstack = bytearray(n)
    comp = [-1] * n
    it = [0] * n
    stack: list[int] = []
    ncomp = 0
    counter = 0
    for root in range(n):
        if index[root] != -1:
            continue
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        onstack[root] = 1
        call = [root]
        while call:
            u = call[-1]
            au = adj[u]
            if it[u] < len(au):
                v = au[it[u]][0]
                it[u] += 1
                if index[v] == -1:
                    index[v] = low[v] = counter
                    counter += 1
                    stack.append(v)
                    onstack[v] = 1
                    call.append(v)
                elif onstack[v] and index[v] < low[u]:
                    low[u] = index[v]
            else:
                call.pop()
                if low[u] == index[u]:
                    while True:
                        v = stack.pop()
                        onstack[v] = 0
                        comp[v] = ncomp
                        if v == u:
                            break
                    ncomp += 1
                if call and low[u] < low[call[-1]]:
                    low[call[-1]] = low[u]
    if stack or any(c < 0 for c in comp):
        raise RuntimeError("Tarjan bookkeeping failure")
    return comp, ncomp


def prune(vertices, edges):
    """Recompute cyclic/certified/retained blocks and the compressed graph from a dump."""
    n = len(vertices)
    idx = {v: i for i, v in enumerate(vertices)}
    adj = [[] for _ in range(n)]
    for q, j, z, k, word in edges:
        adj[idx[(q, j)]].append((idx[(z, k)], word))
    comp, ncomp = tarjan(n, adj)
    iadj = [[(v, w) for v, w in adj[u] if comp[v] == comp[u]] for u in range(n)]
    members = defaultdict(list)
    for u in range(n):
        members[comp[u]].append(u)
    internal_edges = [0] * ncomp
    for u in range(n):
        internal_edges[comp[u]] += len(iadj[u])
    h = [-1] * n
    stats = dict(blocks=ncomp, cyclic=0, certified=0, retained_blocks=0, retained_vertices=0,
                 max_d_certified=0, retained_block_sizes=[])
    retained_comps = set()
    for c in range(ncomp):
        if internal_edges[c] == 0:
            continue
        stats["cyclic"] += 1
        mem = members[c]
        root = min(mem)  # vertices are sorted, so the smallest index is the smallest (q, j)
        h[root] = 0
        queue = [root]
        for u in queue:
            for v, w in iadj[u]:
                if h[v] < 0:
                    h[v] = h[u] + len(w)
                    queue.append(v)
        if len(queue) != len(mem):
            raise RuntimeError("block not reachable from its root")
        d = 0
        for u in mem:
            for v, w in iadj[u]:
                d = gcd(d, abs(h[u] + len(w) - h[v]))
        if d <= 0:
            raise RuntimeError("cyclic block with d = 0")
        labels = {}
        ok = True
        for u in mem:
            if not ok:
                break
            hu = h[u]
            for v, w in iadj[u]:
                for i, letter in enumerate(w):
                    ph = (hu + i) % d
                    prev = labels.setdefault(ph, letter)
                    if prev != letter:
                        ok = False
                        break
                if not ok:
                    break
        if ok:
            stats["certified"] += 1
            stats["max_d_certified"] = max(stats["max_d_certified"], d)
        else:
            stats["retained_blocks"] += 1
            stats["retained_vertices"] += len(mem)
            stats["retained_block_sizes"].append(len(mem))
            retained_comps.add(c)
    stats["retained_block_sizes"].sort()
    anchors = set()
    has_anchor = set()
    for c in retained_comps:
        for u in members[c]:
            if len(iadj[u]) >= 2:
                anchors.add(u)
                has_anchor.add(c)
    fallback = 0
    for c in retained_comps - has_anchor:
        anchors.add(min(members[c]))
        fallback += 1
    compressed = set()
    raw_count = 0
    max_word = 0
    for u in sorted(anchors):
        for v, w in iadj[u]:
            word = list(w)
            steps = 0
            while v not in anchors:
                if len(iadj[v]) != 1:
                    raise RuntimeError("chain vertex without unique continuation")
                v, w2 = iadj[v][0]
                word.extend(w2)
                steps += 1
                if steps > n:
                    raise RuntimeError("chain does not reach an anchor")
            raw_count += 1
            max_word = max(max_word, len(word))
            compressed.add((*vertices[u], *vertices[v], tuple(word)))
    stats.update(compressed_vertices=len(anchors), compressed_edges_distinct=len(compressed),
                 compressed_edges_with_multiplicity=raw_count, fallback_anchors=fallback,
                 max_compressed_word=max_word)
    out_vertices = sorted(vertices[u] for u in anchors)
    return stats, out_vertices, compressed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=sorted(CASES), required=True)
    parser.add_argument("--dumps", type=Path, required=True)
    parser.add_argument("--summary", type=Path, help="C++ summary JSON lines (run_a.jsonl)")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    case = CASES[args.case]
    a, b, K, carries, primes = case["a"], case["b"], case["K"], case["carries"], case["primes"]
    summary = []
    if args.summary:
        summary = [json.loads(l) for l in args.summary.read_text().splitlines() if l.strip() and '"stage"' in l]
    report = dict(case=args.case, kind="same-provenance postcheck by implementation A (not independent B)",
                  stages=[], all_passed=True)
    prev_out = None
    stage = 0
    while (args.dumps / f"stage-{stage:02d}-input.txt").exists():
        t0 = time.monotonic()
        hin, vin, ein = read_wordgraph(args.dumps / f"stage-{stage:02d}-input.txt")
        hout, vout, eout = read_wordgraph(args.dumps / f"stage-{stage:02d}-output.txt")
        check_wordgraph_order(hin, vin, ein)
        check_wordgraph_order(hout, vout, eout)
        rec: dict = dict(stage=stage, input_vertices=len(vin), input_edges_distinct=len(ein),
                         output_vertices=len(vout), output_edges_distinct=len(eout))
        modulus = 1
        for p in primes[:stage]:
            modulus *= p
        rec["header_ok"] = (hin["modulus"] == modulus == hout["modulus"] and hin["K"] == K == hout["K"]
                            and hin["primes"] == primes[:stage] == hout["primes"])
        ein_set = set(ein)
        if stage == 0:
            v_lit, e_lit = literal_initial(a, b, K, carries)
            rec["P1_initial_vertices_equal"] = (v_lit == vin)
            rec["P1_initial_edges_equal"] = (e_lit == ein_set)
            rec["P1_literal_edge_count"] = len(e_lit)
            passed = rec["P1_initial_vertices_equal"] and rec["P1_initial_edges_equal"]
        else:
            p = primes[stage - 1]
            v_lift, e_lift, nwords = lift(a, b, prev_out, modulus // p, p)
            rec["P2_prime"] = p
            rec["P2_lift_vertices_equal"] = (v_lift == vin)
            rec["P2_lift_edges_equal"] = (e_lift == ein_set)
            rec["P2_lift_edge_count"] = len(e_lift)
            rec["P2_missing_in_dump"] = len(e_lift - ein_set)
            rec["P2_extra_in_dump"] = len(ein_set - e_lift)
            rec["P2_distinct_words_simulated"] = nwords
            passed = rec["P2_lift_vertices_equal"] and rec["P2_lift_edges_equal"]
        stats, v_cmp, e_cmp = prune(vin, ein)
        rec["P3"] = stats
        rec["P3_output_vertices_equal"] = (v_cmp == vout)
        rec["P3_output_edges_equal"] = (e_cmp == set(eout))
        rec["P3_missing_in_dump"] = len(e_cmp - set(eout))
        rec["P3_extra_in_dump"] = len(set(eout) - e_cmp)
        passed = passed and rec["P3_output_vertices_equal"] and rec["P3_output_edges_equal"] and rec["header_ok"]
        if stage < len(summary):
            s = summary[stage]
            cmp = dict(input_vertices=(s["input_vertices"], len(vin)),
                       input_edges_with_multiplicity_vs_distinct=(s["input_edges"], len(ein)),
                       cyclic=(s["cyclic"], stats["cyclic"]), certified=(s["certified"], stats["certified"]),
                       retained=(s["retained"], stats["retained_vertices"]),
                       macro_vertices=(s["macro_vertices"], stats["compressed_vertices"]),
                       macro_edges_with_multiplicity=(s["macro_edges"], stats["compressed_edges_with_multiplicity"]),
                       macro_edges_distinct=(None, stats["compressed_edges_distinct"]),
                       max_word=(s["max_word"], stats["max_compressed_word"]))
            rec["C_summary_vs_recomputed"] = cmp
            rec["C_counts_equal"] = all(x == y for k, (x, y) in cmp.items()
                                        if k not in ("input_edges_with_multiplicity_vs_distinct", "macro_edges_distinct"))
            passed = passed and rec["C_counts_equal"]
        rec["passed"] = passed
        rec["seconds"] = round(time.monotonic() - t0, 3)
        report["all_passed"] = report["all_passed"] and passed
        report["stages"].append(rec)
        print(json.dumps({k: rec[k] for k in ("stage", "passed", "seconds")}), flush=True)
        prev_out = eout
        stage += 1
    report["stages_checked"] = stage
    report["final_output_empty"] = bool(report["stages"]) and report["stages"][-1]["output_vertices"] == 0
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("all_passed:", report["all_passed"], "final_output_empty:", report["final_output_empty"])
    if not report["all_passed"]:
        sys.exit(1)


if __name__ == "__main__":
    main()
