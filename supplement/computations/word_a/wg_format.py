#!/usr/bin/env python3
"""Normalized text formats for implementation A of the word-labelled method.

This module converts the supplied binary graph files (``WORDGR01`` word graphs
and the Q75 ``int32`` arrays) into the machine-readable text formats specified
in ``computations/word-schema.md`` (``WORDGRAPH 2`` and
``Q75GRAPH 2``). It contains no edge enumeration, lifting, SCC, certification
or compression logic: it only renames, sorts, deduplicates and serializes what
the C++ programs wrote, and checks a few structural invariants of those files.

Vertex names are intrinsic: ``(q, cell)`` where ``q`` is the least
non-negative residue modulo the product of the primes lifted so far
(CRT-combined) and ``cell`` is the fractional cell. Edges are
``(q_u, cell_u, q_v, cell_v, word)`` with the word written as a sequence of
signed integer carries. All lists are sorted lexicographically; identical
parallel edges appear once.
"""
from __future__ import annotations

import hashlib
import struct
from pathlib import Path
from typing import Iterable

WORDGRAPH_MAGIC = "WORDGRAPH 2"
Q75_MAGIC = "Q75GRAPH 2"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------- WORDGR01 --

def read_wordgr01(path: Path) -> tuple[int, int, dict[int, list[tuple[int, tuple[int, ...]]]]]:
    """Parse a supplied ``WORDGR01`` file.

    Layout (little endian): magic ``WORDGR01`` (8 bytes), modulus (u64),
    K (u32), vertex count (u64); then for each vertex: tag (u64), out-degree
    (u32); then for each edge: target tag (u64), word length (u32), word bytes
    (each byte is carry+128). Multiplicities are preserved in the returned
    lists; the file's own vertex order and edge order are kept as read.
    """
    data = Path(path).read_bytes()
    if data[:8] != b"WORDGR01":
        raise ValueError(f"{path}: bad magic")
    modulus, K, n = struct.unpack_from("<QIQ", data, 8)
    off = 28
    graph: dict[int, list[tuple[int, tuple[int, ...]]]] = {}
    for _ in range(n):
        tag, deg = struct.unpack_from("<QI", data, off)
        off += 12
        if tag in graph:
            raise ValueError(f"{path}: duplicate vertex tag {tag}")
        edges = []
        for _ in range(deg):
            target, length = struct.unpack_from("<QI", data, off)
            off += 12
            if length == 0:
                raise ValueError(f"{path}: empty word")
            word = tuple(byte - 128 for byte in data[off:off + length])
            off += length
            edges.append((target, word))
        graph[tag] = edges
    if off != len(data):
        raise ValueError(f"{path}: trailing bytes ({len(data) - off})")
    for tag, edges in graph.items():
        for target, _ in edges:
            if target not in graph:
                raise ValueError(f"{path}: edge target {target} is not a vertex")
    return modulus, K, graph


def normalize_wordgraph(K: int, graph: dict[int, list[tuple[int, tuple[int, ...]]]]):
    """Return sorted intrinsic vertices, sorted distinct edges and the raw edge count."""
    vertices = sorted(divmod(tag, K) for tag in graph)
    raw = 0
    edge_set: set[tuple[int, int, int, int, tuple[int, ...]]] = set()
    for tag, edges in graph.items():
        q, j = divmod(tag, K)
        for target, word in edges:
            z, k = divmod(target, K)
            edge_set.add((q, j, z, k, word))
            raw += 1
    return vertices, sorted(edge_set), raw


# ------------------------------------------------------------ WORDGRAPH 2 --

def write_wordgraph(path: Path, *, a: int, b: int, K: int, modulus: int, primes: Iterable[int], vertices, edges) -> None:
    """Write a ``WORDGRAPH 2`` file (one graph per file, UTF-8, LF).

    Header: ``WORDGRAPH 2 a=<a> b=<b> K=<K> modulus=<P> primes=<p1,p2,...> vertices=<n> edges=<m>``
    then ``V <q> <cell>`` lines (sorted) and ``E <q_u> <cell_u> <q_v> <cell_v> <c_0> ... <c_{l-1}>``
    lines (sorted by (q_u, cell_u, q_v, cell_v, word); words compared element-wise, shorter first).
    """
    primes = list(primes)
    vertices = sorted(vertices)
    edges = sorted(set(edges))
    header = (f"{WORDGRAPH_MAGIC} a={a} b={b} K={K} modulus={modulus} primes={','.join(map(str, primes))} "
              f"vertices={len(vertices)} edges={len(edges)}")
    with Path(path).open("w", encoding="utf-8", newline="\n") as f:
        f.write(header + "\n")
        for q, j in vertices:
            f.write(f"V {q} {j}\n")
        for q, j, z, k, word in edges:
            f.write("E " + " ".join(map(str, (q, j, z, k, *word))) + "\n")


def parse_header(line: str, magic: str) -> dict[str, object]:
    if not line.startswith(magic + " "):
        raise ValueError(f"bad header: {line!r}")
    header: dict[str, object] = {}
    for token in line[len(magic) + 1:].split():
        key, _, value = token.partition("=")
        if key == "primes":
            header[key] = [int(x) for x in value.split(",") if x]
        else:
            header[key] = int(value)
    return header


def read_wordgraph(path: Path):
    """Read a ``WORDGRAPH 2`` file. Returns (header dict, vertices list, edges list) in file order."""
    vertices: list[tuple[int, int]] = []
    edges: list[tuple[int, int, int, int, tuple[int, ...]]] = []
    with Path(path).open("r", encoding="utf-8") as f:
        header = parse_header(f.readline().rstrip("\n"), WORDGRAPH_MAGIC)
        for line in f:
            parts = line.split()
            if not parts:
                continue
            if parts[0] == "V":
                vertices.append((int(parts[1]), int(parts[2])))
            elif parts[0] == "E":
                nums = list(map(int, parts[1:]))
                edges.append((nums[0], nums[1], nums[2], nums[3], tuple(nums[4:])))
            else:
                raise ValueError(f"{path}: unexpected line {line!r}")
    return header, vertices, edges


def check_wordgraph_order(header, vertices, edges) -> None:
    if vertices != sorted(vertices) or len(set(vertices)) != len(vertices):
        raise ValueError("vertex list is not sorted and distinct")
    if edges != sorted(edges) or len(set(edges)) != len(edges):
        raise ValueError("edge list is not sorted and distinct")
    if header.get("vertices") != len(vertices) or header.get("edges") != len(edges):
        raise ValueError("header counts disagree with the lists")
    modulus = 1
    for p in header.get("primes", []):
        modulus *= p
    if header.get("modulus") != modulus:
        raise ValueError("modulus is not the product of the primes")
    vset = set(vertices)
    for q, j, z, k, word in edges:
        if (q, j) not in vset or (z, k) not in vset:
            raise ValueError("edge endpoint outside the vertex list")
        if not word:
            raise ValueError("empty word")
    for q, j in vertices:
        if not (0 <= q < header["modulus"] and 0 <= j < header["K"]):
            raise ValueError("vertex outside the name ranges")


# -------------------------------------------------------------- Q75GRAPH 2 --

def read_int32_records(path: Path, width: int) -> list[tuple[int, ...]]:
    data = Path(path).read_bytes()
    if len(data) % (4 * width):
        raise ValueError(f"{path}: size is not a multiple of {4 * width}")
    return list(struct.iter_unpack("<" + "i" * width, data))


def write_q75(path: Path, *, a: int, b: int, M: int, K: int, vertices, edges, blocks) -> None:
    """Write a ``Q75GRAPH 2`` file.

    Header: ``Q75GRAPH 2 a=7 b=5 M=429 K=2048 vertices=<n> edges=<m> blocks=<k>``;
    ``V <q> <j>`` lines (sorted); ``E <q_u> <j_u> <q_v> <j_v> <c>`` lines (sorted);
    ``B <id> <size> <internal_edges> <period> <rho> <eta> L <labels...> M <q:j> ...`` lines,
    ids assigned from 0 in the lexicographic order of each block's smallest vertex, members
    sorted; the label list has ``period`` entries and is omitted when the period is 0.
    ``blocks`` is a list of dicts with keys members (sorted list of (q, j)), internal,
    period, rho, eta, labels (list; empty for period 0).
    """
    vertices = sorted(vertices)
    edges = sorted(set(edges))
    blocks = sorted(blocks, key=lambda blk: blk["members"][0])
    with Path(path).open("w", encoding="utf-8", newline="\n") as f:
        f.write(f"{Q75_MAGIC} a={a} b={b} M={M} K={K} vertices={len(vertices)} edges={len(edges)} blocks={len(blocks)}\n")
        for q, j in vertices:
            f.write(f"V {q} {j}\n")
        for q, j, z, k, c in edges:
            f.write(f"E {q} {j} {z} {k} {c}\n")
        for i, blk in enumerate(blocks):
            labels = " ".join(map(str, blk["labels"]))
            members = " ".join(f"{q}:{j}" for q, j in blk["members"])
            f.write(f"B {i} {len(blk['members'])} {blk['internal']} {blk['period']} {blk['rho']} {blk['eta']} L"
                    + (" " + labels if labels else "") + " M " + members + "\n")


def read_q75(path: Path):
    """Read a ``Q75GRAPH 2`` file. Returns (header, vertices, edges, blocks) in file order."""
    vertices, edges, blocks = [], [], []
    with Path(path).open("r", encoding="utf-8") as f:
        header = parse_header(f.readline().rstrip("\n"), Q75_MAGIC)
        for line in f:
            parts = line.split()
            if not parts:
                continue
            if parts[0] == "V":
                vertices.append((int(parts[1]), int(parts[2])))
            elif parts[0] == "E":
                edges.append(tuple(map(int, parts[1:6])))
            elif parts[0] == "B":
                bid, size, internal, period, rho, eta = map(int, parts[1:7])
                if parts[7] != "L":
                    raise ValueError(f"{path}: malformed block line {line!r}")
                m_index = parts.index("M")
                labels = [int(x) for x in parts[8:m_index]]
                members = [tuple(map(int, t.split(":"))) for t in parts[m_index + 1:]]
                blocks.append(dict(id=bid, size=size, internal=internal, period=period, rho=rho, eta=eta,
                                   labels=labels, members=members))
            else:
                raise ValueError(f"{path}: unexpected line {line!r}")
    return header, vertices, edges, blocks
