#!/usr/bin/env python3
"""An exact inverse search: all bases certified by G(M=30, K=1).

Result: the only reduced base a>b>=2 passing the all-edge phase criterion
at these fixed parameters is 4/3. This is NOT a classification with arbitrary
K or arbitrary prime sets, and the arithmetic theorem for 4/3 is already
known. The paper's Theorem 39 excludes all a>=2*rad(30)=60, so the finite
search below exhausts the domain for these parameters.

No dependencies, floating-point arithmetic, or trajectory samples are used.
This is a small reproducible computational check, not a Lean formalization.
"""
from collections import deque
from math import gcd
import json

MODULUS = 30
UNITS = tuple(q for q in range(MODULUS) if gcd(q, MODULUS) == 1)


def exact_edges(a: int, b: int) -> list[tuple[int, int, int]]:
    """Literal (E1)-(E3) enumeration. K=1 makes (E3) equal -b<c<a."""
    return [(u, c, v)
            for u, q in enumerate(UNITS)
            for v, z in enumerate(UNITS)
            for c in range(1 - b, a)
            if (b * z - a * q - c) % MODULUS == 0]


def phase_check(a: int, b: int) -> tuple[bool, list[dict]]:
    edges = exact_edges(a, b)
    n = len(UNITS)
    # Transitive closure, rather than a Tarjan/Kosaraju SCC traversal.
    reach = [[i == j for j in range(n)] for i in range(n)]
    adjacency = [[] for _ in range(n)]
    for u, c, v in edges:
        reach[u][v] = True
        adjacency[u].append(v)
    for k in range(n):
        for i in range(n):
            if reach[i][k]:
                for j in range(n):
                    reach[i][j] = reach[i][j] or reach[k][j]

    unseen = set(range(n))
    reports = []
    all_pass = True
    while unseen:
        root = min(unseen)
        component = {v for v in unseen if reach[root][v] and reach[v][root]}
        unseen -= component
        internal = [(u, c, v) for u, c, v in edges
                    if u in component and v in component]
        if not internal:
            continue
        h = {root: 0}
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v in adjacency[u]:
                if v in component and v not in h:
                    h[v] = h[u] + 1
                    queue.append(v)
        if set(h) != component:
            raise RuntimeError('Reachability partition failed its own check')
        d = 0
        for u, c, v in internal:
            d = gcd(d, abs(h[u] + 1 - h[v]))
        if d <= 0:
            raise RuntimeError('Nonpositive period for a cyclic component')
        labels = [set() for _ in range(d)]
        for u, c, v in internal:
            labels[h[u] % d].add(c)
        passes = all(len(values) == 1 for values in labels)
        all_pass = all_pass and passes
        reports.append({'residues': sorted(UNITS[v] for v in component),
                        'period': d,
                        'phase_labels': [sorted(values) for values in labels],
                        'passes': passes})
    return all_pass, reports


def main() -> None:
    successes = []
    tested = 0
    for a in range(3, 60):
        for b in range(2, a):
            if gcd(a, b) != 1:
                continue
            tested += 1
            passes, reports = phase_check(a, b)
            if passes:
                successes.append({'a': a, 'b': b,
                                  'vertices': len(UNITS),
                                  'edges': len(exact_edges(a, b)),
                                  'cyclic_components': reports})
    print(json.dumps({'M': MODULUS, 'K': 1, 'numerator_bound_exclusive': 60,
                      'tested_reduced_bases': tested, 'successes': successes,
                      'scope': 'Exact finite-parameter phase-test classification; '
                               'not arithmetic impossibility for rejected bases'},
                     indent=2))


if __name__ == '__main__':
    main()
