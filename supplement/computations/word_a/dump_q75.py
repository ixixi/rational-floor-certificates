#!/usr/bin/env python3
"""Dump the supplied Q75 arrays (7/5, M=429, K=2048) into one Q75GRAPH 2 text file.

Usage:
    python3 dump_q75.py --prefix DIR/graphA --out OUT_DIR [--manifest m.json]

The supplied construction writes three sorted int32 arrays:
  <prefix>_edges.bin       records (source key, target key, carry)
  <prefix>_vertices.bin    records (key, block root key, h, d)
  <prefix>_components.bin  records (root key, size, internal edges, d, certified, rho, eta)
with key = q*K + j. This dumper renames keys to (q, j), rebuilds the block
partition as a family of vertex sets, derives the phase-label sequence of every
cyclic block from the internal edges (phase 0 at the block's smallest vertex;
the supplied h values are used only to derive phases, they are not written)
and checks that the derived labels are consistent (one carry per phase). It
performs no SCC computation itself; the recomputation of blocks, phases and
the longest-path ranks is in postcheck_q75.py. It also writes an excerpt file
with the cyclic blocks only.
"""
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from math import gcd
from pathlib import Path

from wg_format import Q75_MAGIC, read_int32_records, sha256_file, write_q75

A, B, M, K = 7, 5, 429, 2048
CARRIES = [-4, -2, 2, 4, 6]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--manifest", type=Path)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    sources = {s: Path(f"{args.prefix}_{s}.bin") for s in ("edges", "vertices", "components")}
    edges_raw = read_int32_records(sources["edges"], 3)
    verts_raw = read_int32_records(sources["vertices"], 4)
    comps_raw = read_int32_records(sources["components"], 7)

    def name(key: int) -> tuple[int, int]:
        q, j = divmod(key, K)
        if not (0 <= q < M and gcd(q, M) == 1 and 0 <= j < K):
            raise ValueError(f"illegal key {key}")
        return q, j

    vertices = sorted(name(v[0]) for v in verts_raw)
    if len(set(vertices)) != len(vertices):
        raise ValueError("duplicate vertex")
    edges = sorted((*name(s), *name(t), c) for s, t, c in edges_raw)
    if len(set(edges)) != len(edges):
        raise ValueError("duplicate edge record")
    if any(c not in CARRIES for *_, c in edges):
        raise ValueError("carry outside the alphabet")
    members: dict[int, list[tuple[int, int]]] = defaultdict(list)
    hvalue: dict[tuple[int, int], int] = {}
    dvalue: dict[int, int] = {}
    for key, root, h, d in verts_raw:
        members[root].append(name(key))
        hvalue[name(key)] = h
        if dvalue.setdefault(root, d) != d:
            raise ValueError("inconsistent d inside a block")
    comp = {}
    for root, size, internal, d, cert, rho, eta in comps_raw:
        if root in comp:
            raise ValueError("duplicate block record")
        comp[root] = dict(size=size, internal=internal, d=d, certified=cert, rho=rho, eta=eta)
    if set(comp) != set(members):
        raise ValueError("block records and vertex records disagree")
    owner = {}
    for root, vs in members.items():
        vs.sort()
        if name(root) != vs[0]:
            raise ValueError("block root is not its smallest vertex")
        if len(vs) != comp[root]["size"] or dvalue[root] != comp[root]["d"]:
            raise ValueError("block size or d mismatch")
        if hvalue[vs[0]] != 0:
            raise ValueError("supplied h is not 0 at the smallest vertex")
        for v in vs:
            owner[v] = root
    internal_count = defaultdict(int)
    labels: dict[int, dict[int, int]] = defaultdict(dict)
    for q, j, z, k, c in edges:
        u, v = (q, j), (z, k)
        r = owner[u]
        if owner[v] != r:
            continue
        internal_count[r] += 1
        d = comp[r]["d"]
        if d <= 0:
            raise ValueError("internal edge in a block with d=0")
        if (hvalue[u] + 1 - hvalue[v]) % d:
            raise ValueError("h is not a phase potential modulo d")
        if labels[r].setdefault(hvalue[u] % d, c) != c:
            raise ValueError(f"block {name(r)} is not phase-consistent although the arrays claim certified={comp[r]['certified']}")
    blocks = []
    cyclic = certified = 0
    for root in members:
        info = comp[root]
        if internal_count[root] != info["internal"]:
            raise ValueError("internal edge count mismatch")
        is_cyclic = info["internal"] > 0
        if info["certified"] != int(is_cyclic):
            raise ValueError("arrays report an uncertified cyclic block; the dump refuses to hide it")
        if is_cyclic:
            cyclic += 1
            certified += 1
            if sorted(labels[root]) != list(range(info["d"])):
                raise ValueError("a phase has no label")
            lab = [labels[root][p] for p in range(info["d"])]
        else:
            if info["d"] != 0:
                raise ValueError("acyclic block with d != 0")
            lab = []
        blocks.append(dict(members=members[root], internal=info["internal"], period=info["d"],
                           rho=info["rho"], eta=info["eta"], labels=lab))
    blocks.sort(key=lambda blk: blk["members"][0])
    main_file = args.out / "q75.txt"
    write_q75(main_file, a=A, b=B, M=M, K=K, vertices=vertices, edges=edges, blocks=blocks)
    excerpt = args.out / "q75-cyclic-blocks-excerpt.txt"
    with excerpt.open("w", encoding="utf-8", newline="\n") as f:
        f.write(f"{Q75_MAGIC} a={A} b={B} M={M} K={K} vertices={len(vertices)} edges={len(edges)} blocks={len(blocks)}\n")
        with main_file.open("r", encoding="utf-8") as g:
            for line in g:
                if line.startswith("B ") and int(line.split()[3]) > 0:
                    f.write(line)
    max_rho = max(c["rho"] for c in comp.values())
    max_eta = max(c["eta"] for c in comp.values())
    max_d = max(c["d"] for c in comp.values())
    summary = dict(format="Q75GRAPH 2", a=A, b=B, M=M, K=K, carries=CARRIES, vertices=len(vertices), edges=len(edges),
                   blocks=len(blocks), cyclic_blocks=cyclic, certified_blocks=certified, max_rho=max_rho, max_eta=max_eta, max_d=max_d,
                   sources={s: dict(path=str(sources[s]), bytes=sources[s].stat().st_size, sha256=sha256_file(sources[s])) for s in sources},
                   outputs={"q75": dict(path=str(main_file), bytes=main_file.stat().st_size, sha256=sha256_file(main_file)),
                            "cyclic_blocks_excerpt": dict(path=str(excerpt), bytes=excerpt.stat().st_size, sha256=sha256_file(excerpt),
                                                          note="excerpt: header plus the B lines with internal_edges > 0 only")})
    if args.manifest:
        args.manifest.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: summary[k] for k in ("vertices", "edges", "blocks", "cyclic_blocks", "certified_blocks", "max_rho", "max_eta", "max_d")}))


if __name__ == "__main__":
    main()
