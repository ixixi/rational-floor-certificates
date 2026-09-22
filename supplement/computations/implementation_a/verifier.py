#!/usr/bin/env python3
"""Integer verifier A, derived from the supplied verify_floor_7_5.py.

Original SHA-256: 2c337379168f1479d54401892ebdb77f13fb07d9510d43589e2814fd9d5119c8.
build_graph and components retain the original closed-form enumeration and
iterative Kosaraju method. The partition checker is strengthened; canonical
component records, stage control and a rank/phase certificate are added.
This module has no dependency on expected tables or implementation B.
"""
from __future__ import annotations

from collections import Counter, deque
from heapq import heapify, heappop, heappush
from math import gcd
from typing import Callable

State = tuple[int, int]
Edge = tuple[int, int]
Graph = tuple[list[State], list[list[Edge]], list[list[int]]]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def integer(value: object) -> bool:
    return type(value) is int


def validate_parameters(parameters: dict) -> None:
    keys = {"a", "b", "M", "K0", "f", "max_stages"}
    require(set(parameters) == keys, "Incorrect parameter keys")
    require(all(integer(v) for v in parameters.values()), "Parameters must be integers")
    a, b = parameters["a"], parameters["b"]
    require(a > b >= 2 and gcd(a, b) == 1, "Invalid rational base")
    require(parameters["M"] >= 2 and parameters["K0"] >= 1, "Invalid finite parameters")
    require(parameters["f"] >= 2 and parameters["max_stages"] >= 1, "Invalid run parameters")


def build_graph(a: int, b: int, modulus: int, cells: int,
                allowed: set[State] | None = None) -> Graph:
    """All E1--E3 edges, including all unit solutions when b is a nonunit."""
    require(all(integer(x) for x in (a, b, modulus, cells)), "Noninteger graph parameter")
    require(a > b >= 2 and gcd(a, b) == 1, "Invalid rational base")
    require(modulus >= 2 and cells >= 1, "Invalid finite parameters")
    units = [q for q in range(modulus) if gcd(q, modulus) == 1]
    if allowed is None:
        states = [(q, j) for q in units for j in range(cells)]
    else:
        require(isinstance(allowed, set), "allowed must be a set of state tuples")
        require(all(isinstance(v, tuple) and len(v) == 2
                    and all(integer(x) for x in v) for v in allowed), "Malformed state")
        states = sorted(allowed)
    require(all(0 <= q < modulus and gcd(q, modulus) == 1 and 0 <= j < cells
                for q, j in states), "Invalid state")
    index = {v: i for i, v in enumerate(states)}
    destinations: dict[int, list[int]] = {}
    for z in units:
        destinations.setdefault(b * z % modulus, []).append(z)
    adj: list[list[Edge]] = [[] for _ in states]
    rev: list[list[int]] = [[] for _ in states]
    for u, (q, j) in enumerate(states):
        for carry in range(1 - b, a):
            zs = destinations.get((a * q + carry) % modulus, ())
            if not zs:
                continue
            lo = max(0, (a * j - carry * cells) // b)
            hi = min(cells - 1, (a * (j + 1) - carry * cells - 1) // b)
            for k in range(lo, hi + 1):
                require(a*j - b*(k+1) < carry*cells < a*(j+1) - b*k,
                        "Incorrect interval edge")
                for z in zs:
                    v = index.get((z, k))
                    if v is not None:
                        adj[u].append((v, carry))
                        rev[v].append(u)
    return states, adj, rev


def components(adj: list[list[Edge]], rev: list[list[int]]) -> tuple[list[list[int]], list[int]]:
    """Original iterative Kosaraju, with no recursive calls."""
    count = len(adj)
    seen = bytearray(count)
    order: list[int] = []
    for root in range(count):
        if seen[root]:
            continue
        seen[root] = 1
        stack = [(root, iter(adj[root]))]
        while stack:
            u, edges = stack[-1]
            edge = next(edges, None)
            if edge is None:
                order.append(u)
                stack.pop()
            else:
                v = edge[0]
                if not seen[v]:
                    seen[v] = 1
                    stack.append((v, iter(adj[v])))
    groups: list[list[int]] = []
    owner = [-1] * count
    for root in reversed(order):
        if owner[root] != -1:
            continue
        number = len(groups)
        group: list[int] = []
        owner[root] = number
        stack = [root]
        while stack:
            u = stack.pop()
            group.append(u)
            for v in rev[u]:
                if owner[v] == -1:
                    owner[v] = number
                    stack.append(v)
        groups.append(group)
    return groups, owner


def check_adjacency(adj: list[list[Edge]], rev: list[list[int]]) -> None:
    count = len(adj)
    require(len(rev) == count, "Wrong reverse adjacency length")
    reconstructed: list[list[int]] = [[] for _ in adj]
    for u, edges in enumerate(adj):
        require(len(set(edges)) == len(edges), "Duplicate labelled edge")
        for edge in edges:
            require(len(edge) == 2 and all(integer(x) for x in edge), "Malformed edge")
            v, _ = edge
            require(0 <= v < count, "Edge endpoint out of range")
            reconstructed[v].append(u)
    for v, incoming in enumerate(rev):
        require(all(integer(u) and 0 <= u < count for u in incoming),
                "Reverse endpoint out of range")
        require(Counter(incoming) == Counter(reconstructed[v]), "Inconsistent reverse adjacency")


def check_partition(adj: list[list[Edge]], rev: list[list[int]],
                    groups: list[list[int]], owner: list[int]) -> list[int]:
    """Check a full SCC partition and return strictly decreasing block ranks."""
    check_adjacency(adj, rev)
    count = len(adj)
    require(len(owner) == count, "Wrong owner length")
    require(all(group for group in groups), "Empty component")
    flattened = [u for group in groups for u in group]
    require(all(integer(u) and 0 <= u < count for u in flattened),
            "Component vertex out of range")
    require(sorted(flattened) == list(range(count)), "Partition is not a disjoint cover")
    require(all(integer(c) and 0 <= c < len(groups) for c in owner), "Owner out of range")
    for c, group in enumerate(groups):
        require(all(owner[u] == c for u in group), "Incorrect owner membership")

    quotient = [set() for _ in groups]
    indegree = [0] * len(groups)
    for c, group in enumerate(groups):
        members = set(group)
        for backwards in (False, True):
            visited = {group[0]}
            todo = [group[0]]
            while todo:
                u = todo.pop()
                neighbors = rev[u] if backwards else (v for v, _ in adj[u])
                for v in neighbors:
                    if owner[v] == c and v not in visited:
                        visited.add(v)
                        todo.append(v)
            require(visited == members, "Component is not strongly connected")
        for u in group:
            for v, _ in adj[u]:
                d = owner[v]
                if d != c and d not in quotient[c]:
                    quotient[c].add(d)
                    indegree[d] += 1
    todo = [c for c, degree in enumerate(indegree) if degree == 0]
    heapify(todo)
    topological: list[int] = []
    while todo:
        c = heappop(todo)
        topological.append(c)
        for d in sorted(quotient[c]):
            indegree[d] -= 1
            if indegree[d] == 0:
                heappush(todo, d)
    require(len(topological) == len(groups), "Component quotient has a cycle")
    ranks = [0] * len(groups)
    for i, c in enumerate(topological):
        ranks[c] = len(groups) - 1 - i
    require(all(ranks[d] < ranks[c] for c, successors in enumerate(quotient)
                for d in successors), "Invalid decreasing rank")
    return ranks


def canonical_word(labels: list[int]) -> list[int]:
    require(bool(labels), "Empty periodic word")
    length = len(labels)
    primitive = next(labels[:p] for p in range(1, length + 1)
                     if length % p == 0 and all(labels[i] == labels[i % p]
                                                for i in range(length)))
    return min(primitive[i:] + primitive[:i] for i in range(len(primitive)))


def edge_record(states: list[State], u: int, v: int, label: int) -> list[int]:
    return [*states[u], *states[v], label]


def certify_component(states: list[State], adj: list[list[Edge]],
                      group: list[int], owner: list[int], number: int) -> dict:
    group = sorted(group, key=states.__getitem__)
    root = group[0]
    distance = {root: 0}
    todo = deque([root])
    while todo:
        u = todo.popleft()
        for v, _ in adj[u]:
            if owner[v] == number and v not in distance:
                distance[v] = distance[u] + 1
                todo.append(v)
    require(set(distance) == set(group), "Incomplete internal BFS")
    internal = [(u, v, label) for u in group for v, label in adj[u] if owner[v] == number]
    period = 0
    for u, v, _ in internal:
        period = gcd(period, abs(distance[u] + 1 - distance[v]))
    result = {
        "vertices": [list(states[u]) for u in group],
        "internal_edge_count": len(internal),
        "cyclic": bool(internal), "certified": False,
        "h": [distance[u] for u in group], "d": period,
        "phase_labels": None, "word": None, "collision": None,
    }
    if not internal:
        require(len(group) == 1 and period == 0, "Invalid edgeless SCC")
        return result
    require(period > 0, "Cyclic component has zero period")
    first: dict[int, tuple[int, int, int]] = {}
    for u, v, label in internal:
        phase = distance[u] % period
        require(distance[v] % period == (phase + 1) % period, "Invalid edge phase")
        if phase not in first:
            first[phase] = (u, v, label)
        elif first[phase][2] != label and result["collision"] is None:
            result["collision"] = [edge_record(states, *first[phase]),
                                   edge_record(states, u, v, label)]
    require(len(first) == period, "Missing phase")
    if result["collision"] is None:
        result["certified"] = True
        result["phase_labels"] = [first[phase][2] for phase in range(period)]
        result["word"] = canonical_word(result["phase_labels"])
    return result


def refine(retained: list[list[int]], factor: int) -> list[list[int]]:
    require(integer(factor) and factor >= 2, "Invalid refinement factor")
    result = sorted([q, factor*j+r] for q, j in retained for r in range(factor))
    require(len({tuple(v) for v in result}) == len(result), "Duplicate refined cell")
    require({(q, j // factor) for q, j in result} == {tuple(v) for v in retained},
            "Refinement parent mismatch")
    require(len(result) == factor * len(retained), "Incomplete refinement")
    return result


def analyze_stage(graph: Graph, cells: int, factor: int) -> tuple[dict, dict]:
    states, adj, rev = graph
    require(len(states) == len(adj), "Wrong state count")
    require(states == sorted(set(states)), "States must be sorted and unique")
    check_adjacency(adj, rev)
    groups, owner = components(adj, rev)
    # Validate the actual algorithm output before canonicalizing or rebuilding owner.
    check_partition(adj, rev, groups, owner)
    groups = sorted((sorted(group) for group in groups), key=lambda group: states[group[0]])
    owner = [-1] * len(states)
    for number, group in enumerate(groups):
        for u in group:
            owner[u] = number
    ranks = check_partition(adj, rev, groups, owner)
    records = [certify_component(states, adj, group, owner, number)
               for number, group in enumerate(groups)]
    retained = sorted(v for comp in records if comp["cyclic"] and not comp["certified"]
                      for v in comp["vertices"])
    edges = sorted(edge_record(states, u, v, label)
                   for u, outgoing in enumerate(adj) for v, label in outgoing)
    refined = refine(retained, factor)
    stage = {"K": cells, "vertices": [list(v) for v in states], "edges": edges,
             "components": records, "retained": retained, "refined_vertices": refined}
    phase = [0] * len(states)
    blocks = []
    for c, (group, record) in enumerate(zip(groups, records)):
        kind = ("periodic" if record["certified"] else
                "retained" if record["cyclic"] else "edgeless")
        blocks.append({"kind": kind, "rank": ranks[c],
                       "d": record["d"] if record["certified"] else 0,
                       "phase_labels": record["phase_labels"] if record["certified"] else []})
        if record["certified"]:
            for u, h in zip(group, record["h"]):
                phase[u] = h % record["d"]
    certificate = {"K": cells, "vertices": stage["vertices"], "edges": edges,
                   "owner": owner, "phase": phase, "blocks": blocks,
                   "retained": retained, "refined_vertices": refined}
    check_block_certificate(certificate, factor)
    return stage, certificate


def check_block_certificate(certificate: dict, factor: int) -> None:
    """A-side export check; not a replacement for Lean or independent B."""
    vertices = certificate["vertices"]
    index = {tuple(v): i for i, v in enumerate(vertices)}
    require(len(index) == len(vertices), "Duplicate certificate vertex")
    owner, phase, blocks = certificate["owner"], certificate["phase"], certificate["blocks"]
    require(len(owner) == len(phase) == len(vertices), "Certificate vector size")
    require(all(integer(c) and 0 <= c < len(blocks) for c in owner), "Invalid block owner")
    require(set(owner) == set(range(len(blocks))), "Unused block")
    for block in blocks:
        require(integer(block["rank"]) and block["rank"] >= 0, "Negative block rank")
        require(block["kind"] in ("retained", "edgeless", "periodic"), "Invalid block kind")
        if block["kind"] == "periodic":
            require(integer(block["d"]) and block["d"] > 0, "Invalid block period")
            require(len(block["phase_labels"]) == block["d"]
                    and all(integer(e) for e in block["phase_labels"]), "Invalid block labels")
    for u, c in enumerate(owner):
        require(integer(phase[u]), "Noninteger phase")
        if blocks[c]["kind"] == "periodic":
            require(0 <= phase[u] < blocks[c]["d"], "Phase out of range")
    for q, j, z, k, e in certificate["edges"]:
        require((q, j) in index and (z, k) in index, "Certificate endpoint missing")
        u, v = index[(q, j)], index[(z, k)]
        c, d = owner[u], owner[v]
        if c != d:
            require(blocks[d]["rank"] < blocks[c]["rank"], "Block rank does not decrease")
        else:
            block = blocks[c]
            require(block["kind"] != "edgeless", "Internal edge in edgeless block")
            if block["kind"] == "periodic":
                require(phase[v] == (phase[u] + 1) % block["d"], "Block phase mismatch")
                require(e == block["phase_labels"][phase[u]], "Block label mismatch")
    retained = sorted(vertices[u] for u, c in enumerate(owner) if blocks[c]["kind"] == "retained")
    require(certificate["retained"] == retained, "Retained block coverage mismatch")
    require(certificate["refined_vertices"] == refine(retained, factor), "Certificate refinement mismatch")


def run(parameters: dict, on_stage: Callable[[dict, dict], None] | None = None) -> tuple[dict, dict]:
    validate_parameters(parameters)
    science = {"schema_version": 1, "parameters": dict(parameters),
               "termination": "inconclusive", "stages": []}
    certificate = {"schema_version": 1, "kind": "block-rank-phase",
                   "parameters": dict(parameters), "termination": "inconclusive", "stages": []}
    allowed = None
    for stage_index in range(parameters["max_stages"]):
        cells = parameters["K0"] * parameters["f"] ** stage_index
        graph = build_graph(parameters["a"], parameters["b"], parameters["M"], cells, allowed)
        if science["stages"]:
            require([list(v) for v in graph[0]] == science["stages"][-1]["refined_vertices"],
                    "Next stage does not contain exactly all child cells")
        stage, proof = analyze_stage(graph, cells, parameters["f"])
        science["stages"].append(stage)
        certificate["stages"].append(proof)
        if on_stage is not None:
            on_stage(stage, proof)
        if not stage["retained"]:
            science["termination"] = certificate["termination"] = "success"
            break
        allowed = {tuple(v) for v in stage["refined_vertices"]}
    return science, certificate
