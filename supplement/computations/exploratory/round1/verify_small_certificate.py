#!/usr/bin/env python3
"""Literal reference computation for the small 7/5 interval certificate.

Standard library only. Uses direct initial inequalities, forward prime iteration,
Tarjan SCCs, and Fraction-based outward-rounded interval images. It does not
import the C++ implementation. With --compare, compares every stage vertex,
interval endpoint, edge, and carry letter with the C++ dumps.

This is an executable finite verification, not a Lean/kernel formalization.
"""
from __future__ import annotations
import argparse
import json
import math
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

Word = tuple[int, ...]
Edge = tuple[int, int, Word]
Interval = tuple[int, int]

@dataclass(frozen=True)
class Graph:
    bounds: tuple[Interval, ...]
    edges: tuple[Edge, ...]

    @property
    def n(self) -> int:
        return len(self.bounds)


def make_graph(bounds, edges) -> Graph:
    return Graph(tuple(bounds), tuple(sorted(set(edges))))


def initial(a: int, b: int, cells: int, denominator: int, alphabet: Word) -> Graph:
    bounds = [(j*denominator//cells, (j+1)*denominator//cells) for j in range(cells)]
    edges = [(j, k, (c,)) for j in range(cells) for k in range(cells)
             for c in alphabet if a*j-b*(k+1) < c*cells < a*(j+1)-b*k]
    return make_graph(bounds, edges)


def components(g: Graph) -> list[list[int]]:
    """Tarjan's algorithm; intended for this small independently checked case."""
    adj = [[] for _ in range(g.n)]
    for u, v, _ in g.edges:
        adj[u].append(v)
    counter = 0
    stack: list[int] = []
    on_stack: set[int] = set()
    index: dict[int, int] = {}
    low: dict[int, int] = {}
    result: list[list[int]] = []

    def visit(u: int) -> None:
        nonlocal counter
        index[u] = low[u] = counter
        counter += 1
        stack.append(u)
        on_stack.add(u)
        for v in adj[u]:
            if v not in index:
                visit(v)
                low[u] = min(low[u], low[v])
            elif v in on_stack:
                low[u] = min(low[u], index[v])
        if low[u] == index[u]:
            comp = []
            while True:
                v = stack.pop()
                on_stack.remove(v)
                comp.append(v)
                if u == v:
                    break
            result.append(sorted(comp))

    for u in range(g.n):
        if u not in index:
            visit(u)
    return result


def phase_test(vertices: list[int], edges: list[Edge]):
    if not edges:
        return None
    adj = {u: [] for u in vertices}
    for edge in edges:
        adj[edge[0]].append(edge)
    h = {min(vertices): 0}
    queue = deque(h)
    while queue:
        u = queue.popleft()
        for _, v, word in adj[u]:
            if v not in h:
                h[v] = h[u]+len(word)
                queue.append(v)
    assert len(h) == len(vertices)
    d = math.gcd(*(h[u]+len(word)-h[v] for u, v, word in edges))
    assert d > 0
    labels: dict[int, int] = {}
    for u, v, word in edges:
        assert (h[u]+len(word)-h[v]) % d == 0
        for i, c in enumerate(word):
            phase = (h[u]+i) % d
            if phase in labels and labels[phase] != c:
                return dict(certified=False, period=d)
            labels[phase] = c
    assert len(labels) == d
    return dict(certified=True, period=d, phase_word=[labels[i] for i in range(d)])


def simplify(g: Graph):
    comps = components(g)
    comp_id = {u: i for i, comp in enumerate(comps) for u in comp}
    internal = [[] for _ in comps]
    for edge in g.edges:
        u, v, _ = edge
        if comp_id[u] == comp_id[v]:
            internal[comp_id[u]].append(edge)
    kept: list[Edge] = []
    report = []
    for comp, edges in zip(comps, internal):
        phase = phase_test(comp, edges)
        if phase is None:
            continue
        report.append(dict(vertices=comp, **phase))
        if not phase['certified']:
            kept.extend(edges)
    out = [[] for _ in range(g.n)]
    for edge in kept:
        out[edge[0]].append(edge)
    anchors = [u for u in range(g.n) if len(out[u]) >= 2]
    ids = {u: i for i, u in enumerate(anchors)}
    new_edges = []
    for u in anchors:
        for _, v, word in out[u]:
            letters = list(word)
            visited = set()
            while v not in ids:
                assert v not in visited and len(out[v]) == 1
                visited.add(v)
                _, v, following = out[v][0]
                letters.extend(following)
            new_edges.append((ids[u], ids[v], tuple(letters)))
    return make_graph([g.bounds[u] for u in anchors], new_edges), report


def prime_lift(g: Graph, a: int, b: int, p: int) -> Graph:
    assert p >= 2 and all(p % d for d in range(2, math.isqrt(p)+1))
    assert a % p and b % p
    b_inverse = pow(b, -1, p)
    edges = []
    for u, v, word in g.edges:
        for q in range(1, p):
            z = q
            for c in word:
                z = ((a*z+c)*b_inverse) % p
                if z == 0:
                    break
            else:
                edges.append((u*(p-1)+q-1, v*(p-1)+z-1, word))
    active = sorted({u for u, _, _ in edges} | {v for _, v, _ in edges})
    ids = {u: i for i, u in enumerate(active)}
    bounds = [g.bounds[u//(p-1)] for u in active]
    return make_graph(bounds, [(ids[u], ids[v], word) for u, v, word in edges])


def rounded_image(interval: Interval, word: Word, a: int, b: int,
                  denominator: int, backward: bool) -> Interval:
    """Use rational endpoints, then round outwards at every letter."""
    lower, upper = interval
    if lower >= upper:
        return lower, upper
    for c in reversed(word) if backward else word:
        left, right = Fraction(lower, denominator), Fraction(upper, denominator)
        if backward:
            left, right = (b*left+c)/a, (b*right+c)/a
        else:
            left, right = (a*left-c)/b, (a*right-c)/b
        lower = max(0, math.floor(left*denominator))
        upper = min(denominator, math.ceil(right*denominator))
        if lower >= upper:
            break
    return lower, upper


def intersect(x: Interval, y: Interval) -> Interval:
    return max(x[0], y[0]), min(x[1], y[1])


def tighten(g: Graph, a: int, b: int, denominator: int):
    deleted = 0
    for iteration in range(300):
        departure = [[] for _ in range(g.n)]
        arrival = [[] for _ in range(g.n)]
        edges = []
        for u, v, word in g.edges:
            if g.bounds[v][0] >= g.bounds[v][1]:
                deleted += 1
                continue
            pre = intersect(rounded_image(g.bounds[v], word, a, b, denominator, True), g.bounds[u])
            image = intersect(rounded_image(g.bounds[u], word, a, b, denominator, False), g.bounds[v])
            if pre[0] >= pre[1] or image[0] >= image[1]:
                deleted += 1
                continue
            departure[u].append(pre)
            arrival[v].append(image)
            edges.append((u, v, word))
        def hull(intervals: list[Interval]) -> Interval:
            return (min(x[0] for x in intervals), max(x[1] for x in intervals)) if intervals else (denominator, 0)
        bounds = tuple(intersect(hull(departure[u]), hull(arrival[u])) for u in range(g.n))
        stable = bounds == g.bounds
        g = make_graph(bounds, edges)
        if stable:
            return g, iteration+1, deleted
    return g, 300, deleted


def read_dump(path: Path):
    with path.open() as f:
        n, m, denominator = map(int, f.readline().split())
        bounds = [tuple(map(int, f.readline().split())) for _ in range(n)]
        edges = []
        for _ in range(m):
            u, v, length, *word = map(int, f.readline().split())
            assert length == len(word)
            edges.append((u, v, tuple(word)))
        assert not f.read().strip()
    g = make_graph(bounds, edges)
    assert g.n == n and len(g.edges) == m
    return denominator, g


def run(compare: Path | None = None):
    a, b, cells = 7, 5, 4
    denominator = cells*2**32
    alphabet = (-4, -2, 2, 4, 6)
    g = initial(a, b, cells, denominator, alphabet)
    reports = []
    compared_vertices = compared_edges = compared_letters = 0
    for stage, prime in enumerate((0, 3, 11, 13)):
        if prime:
            g = prime_lift(g, a, b, prime)
        original = g
        reduced, phase_report = simplify(g)
        rounds = deletions = 0
        for _ in range(50):
            if not reduced.n:
                break
            reduced, rr, dd = tighten(reduced, a, b, denominator)
            rounds += rr
            deletions += dd
            if not dd:
                break
            reduced, _ = simplify(reduced)
        if compare:
            for kind, graph in (('in', original), ('out', reduced)):
                d_cpp, g_cpp = read_dump(compare / f'cpp_{stage}_{kind}.txt')
                assert d_cpp == denominator
                assert graph.bounds == g_cpp.bounds, (stage, kind, 'bounds')
                assert graph.edges == g_cpp.edges, (stage, kind, 'edges')
                compared_vertices += graph.n
                compared_edges += len(graph.edges)
                compared_letters += sum(len(w) for _, _, w in graph.edges)
        reports.append(dict(prime=prime, input_vertices=original.n, input_edges=len(original.edges),
                            output_vertices=reduced.n, output_edges=len(reduced.edges),
                            interval_rounds=rounds, interval_deletions=deletions,
                            cyclic_components=phase_report))
        g = reduced
    assert g.n == 0 and not g.edges
    return dict(status='verified_empty', a=a, b=b, initial_cells=cells, denominator=denominator,
                primes=[2, 3, 5, 11, 13], stages=reports,
                comparison=dict(stage_graphs=8 if compare else 0, vertices=compared_vertices,
                                edges=compared_edges, letters=compared_letters),
                formalization='Not Lean-verified; exact executable finite computation.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compare', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run(args.compare)
    text = json.dumps(result, indent=2)
    if args.output:
        args.output.write_text(text+'\n', encoding='utf-8')
    print(text)
