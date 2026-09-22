#!/usr/bin/env python3
"""Dump the supplied WORDGR01 stage files of one run into WORDGRAPH 2 text files.

Usage:
    python3 dump_wordgraph.py --case five-halves --binaries RAW_DIR --out OUT_DIR [--manifest m.json]
    python3 dump_wordgraph.py --case cross-75    --binaries RAW_DIR --out OUT_DIR [--manifest m.json]

RAW_DIR holds ``<stage>_input.bin`` / ``<stage>_output.bin`` as written by the
supplied C++ construction. The dump renames vertices to intrinsic ``(q, cell)``,
sorts, removes identical duplicate edges (their raw count is recorded in the
JSON manifest only) and writes ``stage-<ss>-<input|output>.txt`` per stage.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

from wg_format import normalize_wordgraph, read_wordgr01, sha256_file, write_wordgraph

CASES = {
    "five-halves": dict(a=5, b=2, K=4, carries=[-1, 1, 3], primes=[3, 7, 11, 13, 17, 19, 23, 29, 31]),
    "cross-75": dict(a=7, b=5, K=2048, carries=[-4, -2, 2, 4, 6], primes=[3, 11, 13]),
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=sorted(CASES), required=True)
    parser.add_argument("--binaries", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, help="JSON manifest of the produced files")
    args = parser.parse_args()
    case = CASES[args.case]
    args.out.mkdir(parents=True, exist_ok=True)
    manifest = []
    stage = 0
    while (args.binaries / f"{stage}_input.bin").exists():
        primes = case["primes"][:stage]
        expected_modulus = 1
        for p in primes:
            expected_modulus *= p
        for kind in ("input", "output"):
            source = args.binaries / f"{stage}_{kind}.bin"
            modulus, K, graph = read_wordgr01(source)
            if K != case["K"] or modulus != expected_modulus:
                raise ValueError(f"{source}: K/modulus {K}/{modulus} differ from the case definition")
            vertices, edges, raw = normalize_wordgraph(K, graph)
            letters = sorted({c for *_, w in edges for c in w})
            if any(c not in case["carries"] for c in letters):
                raise ValueError(f"{source}: letter outside the carry set: {letters}")
            outdeg = Counter((q, j) for q, j, *_ in edges)
            target = args.out / f"stage-{stage:02d}-{kind}.txt"
            write_wordgraph(target, a=case["a"], b=case["b"], K=K, modulus=modulus, primes=primes,
                            vertices=vertices, edges=edges)
            manifest.append(dict(stage=stage, kind=kind, primes=primes, modulus=modulus,
                                 vertices=len(vertices), edges=len(edges), edges_with_multiplicity=raw,
                                 max_word=max((len(w) for *_, w in edges), default=0),
                                 out_degree_one_vertices=sum(1 for v in vertices if outdeg.get(v, 0) == 1),
                                 out_degree_zero_vertices=sum(1 for v in vertices if outdeg.get(v, 0) == 0),
                                 source=source.name, source_sha256=sha256_file(source), source_bytes=source.stat().st_size,
                                 path=str(target), bytes=target.stat().st_size, sha256=sha256_file(target)))
            print(json.dumps({k: manifest[-1][k] for k in ("stage", "kind", "vertices", "edges", "edges_with_multiplicity")}), flush=True)
        stage += 1
    if args.manifest:
        args.manifest.write_text(json.dumps(dict(format="WORDGRAPH 2", case=args.case, files=manifest), indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
