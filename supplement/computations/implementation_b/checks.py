"""Small literal exhaustive oracles independent of B's search optimizations."""

import json
from fractions import Fraction
from itertools import product
from math import gcd

from core import (adjacency, all_vertices, certify, edges_direct,
                  primitive_rotation, tarjan, verify_partition)


def literal_edges(a, b, M, K, vertices):
    return sorted((q, j, z, k, e)
                  for q, j in vertices for z, k in vertices
                  for e in range(1 - b, a)
                  if (b * z - a * q - e) % M == 0
                  and a * j - b * (k + 1) < e * K < a * (j + 1) - b * k)


def reachability_partition(graph):
    closure = []
    for root in range(len(graph)):
        found = {root}
        frontier = [root]
        while frontier:
            vertex = frontier.pop()
            for target in graph[vertex]:
                if target not in found:
                    found.add(target)
                    frontier.append(target)
        closure.append(found)
    unseen = set(range(len(graph)))
    groups = []
    while unseen:
        root = min(unseen)
        group = sorted(v for v in unseen if v in closure[root] and root in closure[v])
        groups.append(group)
        unseen.difference_update(group)
    return groups


def main():
    counts = {'edge_cases': 0, 'graphs': 0, 'malformed_partitions_rejected': 0,
              'refinement_checks': 0, 'floor_ceiling_checks': 0}
    observed = {'nonunit_b': False, 'negative_e': False,
                'strict_boundary': False, 'self_loop': False,
                'parallel_labels': False}
    for a, b in ((3, 2), (4, 3), (5, 2), (5, 3), (5, 4), (7, 5)):
        for M in range(2, 13):
            for K in range(1, 6):
                full = all_vertices(M, K)
                for vertices in (full, full[::2], [v for v in full if sum(v) % 3]):
                    actual = edges_direct(a, b, M, K, vertices)
                    expected = literal_edges(a, b, M, K, vertices)
                    assert actual == expected, (a, b, M, K, vertices)
                    counts['edge_cases'] += 1
                    observed['nonunit_b'] |= gcd(b, M) > 1 and bool(actual)
                    observed['negative_e'] |= any(edge[4] < 0 for edge in actual)
                    observed['self_loop'] |= any(edge[:2] == edge[2:4] for edge in actual)
                    observed['parallel_labels'] |= len({edge[:4] for edge in actual}) < len(actual)
                    for q, j in vertices:
                        for z, k in vertices:
                            for e in range(1 - b, a):
                                if (b*z-a*q-e) % M == 0 and e*K in (
                                        a*j-b*(k+1), a*(j+1)-b*k):
                                    assert (q, j, z, k, e) not in actual
                                    observed['strict_boundary'] = True
    assert all(observed.values()), observed
    for n in range(4):
        pairs = list(product(range(n), repeat=2))
        for mask in range(1 << len(pairs)):
            graph = [[] for _ in range(n)]
            for bit, (u, v) in enumerate(pairs):
                if mask & (1 << bit):
                    graph[u].append(v)
            got = tarjan(graph)
            assert got == reachability_partition(graph)
            verify_partition(graph, got)
            counts['graphs'] += 1
    for graph, groups in (([[1], [0]], [[0, 0]]),
                          ([[1], [0]], [[0], [1]]),
                          ([[], []], [[0, 1]]),
                          ([[], []], [[0]])):
        try:
            verify_partition(graph, groups)
        except AssertionError:
            counts['malformed_partitions_rejected'] += 1
        else:
            raise AssertionError(('invalid partition accepted', graph, groups))
    vertices = [(1, 0), (1, 1), (1, 2), (1, 3)]
    edges = [(1, 0, 1, 1, -2), (1, 1, 1, 2, 3),
             (1, 2, 1, 3, -2), (1, 3, 1, 0, 3)]
    component = certify(vertices, edges)
    assert component['d'] == 4 and component['word'] == [-2, 3]
    assert component['h'] == [0, 1, 2, 3] and component['certified']
    collision = certify(vertices, edges + [(1, 0, 1, 1, 7)])
    assert not collision['certified'] and collision['collision']
    assert certify([(2, 3)], [(2, 3, 2, 3, -1)])['word'] == [-1]
    assert not certify([(2, 3)], [])['cyclic']
    assert primitive_rotation([3, -1, 3, -1]) == [-1, 3]
    for numerator in range(-20, 21):
        for denominator in range(1, 8):
            floor = numerator // denominator
            ceiling = -((-numerator) // denominator)
            assert floor*denominator <= numerator < (floor+1)*denominator
            assert (ceiling-1)*denominator < numerator <= ceiling*denominator
            counts['floor_ceiling_checks'] += 1
    for K in range(1, 10):
        for f in range(2, 6):
            for den in range(1, 20):
                for num in range(den):
                    theta = Fraction(num, den)
                    coarse = (K * theta).__floor__()
                    fine = (f * K * theta).__floor__()
                    assert fine // f == coarse
                    assert fine in range(f * coarse, f * coarse + f)
                    counts['refinement_checks'] += 1
    print(json.dumps({'status': 'PASS', 'counts': counts,
                      'observed_edge_features': observed}, sort_keys=True))


if __name__ == '__main__':
    main()
