"""Independent, integer-only E1--E3 graph computation (implementation B)."""

from collections import defaultdict, deque
from math import gcd


def validate_parameters(a, b, M, K0, f, max_stages):
    assert all(type(x) is int for x in (a, b, M, K0, f, max_stages))
    assert a > b >= 2 and gcd(a, b) == 1
    assert M >= 2 and K0 >= 1 and f >= 2 and max_stages >= 1


def all_vertices(M, K):
    return [(q, j) for q in range(M) if gcd(q, M) == 1 for j in range(K)]


def edges_direct(a, b, M, K, vertices):
    """E2 buckets; E3 literally tested for every j,e,k before vertex filtering."""
    allowed = set(vertices)
    assert len(allowed) == len(vertices)
    assert all(0 <= q < M and gcd(q, M) == 1 and 0 <= j < K
               for q, j in vertices)
    buckets = defaultdict(list)
    for z in range(M):
        if gcd(z, M) == 1:
            buckets[(b * z) % M].append(z)
    local = {}
    for j in sorted({j for _, j in vertices}):
        for e in range(1 - b, a):
            eK = e * K
            aj = a * j
            next_aj = a * (j + 1)
            local[j, e] = [k for k in range(K)
                           if aj - b * (k + 1) < eK < next_aj - b * k]
    edges = []
    for q, j in vertices:
        for e in range(1 - b, a):
            for z in buckets.get((a * q + e) % M, ()):
                for k in local[j, e]:
                    if (z, k) in allowed:
                        edges.append((q, j, z, k, e))
    edges.sort()
    assert len(set(edges)) == len(edges)
    return edges


def adjacency(vertices, edges):
    number = {v: i for i, v in enumerate(vertices)}
    outgoing = [[] for _ in vertices]
    for q, j, z, k, _ in edges:
        outgoing[number[q, j]].append(number[z, k])
    return outgoing


def tarjan(outgoing):
    """Explicit DFS frames implement Tarjan's lowlink stack algorithm."""
    count = len(outgoing)
    seen = [-1] * count
    low = [0] * count
    active = [False] * count
    pending = []
    groups = []
    next_index = 0
    for root in range(count):
        if seen[root] >= 0:
            continue
        seen[root] = low[root] = next_index
        next_index += 1
        active[root] = True
        pending.append(root)
        frames = [[root, 0]]
        while frames:
            vertex, offset = frames[-1]
            if offset < len(outgoing[vertex]):
                target = outgoing[vertex][offset]
                frames[-1][1] += 1
                if seen[target] < 0:
                    seen[target] = low[target] = next_index
                    next_index += 1
                    pending.append(target)
                    active[target] = True
                    frames.append([target, 0])
                elif active[target]:
                    low[vertex] = min(low[vertex], seen[target])
            else:
                frames.pop()
                if low[vertex] == seen[vertex]:
                    group = []
                    while True:
                        member = pending.pop()
                        active[member] = False
                        group.append(member)
                        if member == vertex:
                            break
                    groups.append(sorted(group))
                if frames:
                    parent = frames[-1][0]
                    low[parent] = min(low[parent], low[vertex])
    return sorted(groups, key=lambda group: group[0])


def verify_partition(outgoing, groups):
    """Exact coverage + two directions of connectivity + acyclic quotient."""
    n = len(outgoing)
    owner = [-1] * n
    for group_id, group in enumerate(groups):
        assert group
        for v in group:
            assert 0 <= v < n and owner[v] == -1
            owner[v] = group_id
    assert all(x >= 0 for x in owner)
    reverse = [[] for _ in outgoing]
    quotient = [set() for _ in groups]
    for u, targets in enumerate(outgoing):
        for v in targets:
            reverse[v].append(u)
            if owner[u] != owner[v]:
                quotient[owner[u]].add(owner[v])
    for group_id, group in enumerate(groups):
        for graph in (outgoing, reverse):
            visited = {group[0]}
            queue = [group[0]]
            while queue:
                u = queue.pop()
                for v in graph[u]:
                    if owner[v] == group_id and v not in visited:
                        visited.add(v)
                        queue.append(v)
            assert len(visited) == len(group)
    indegree = [0] * len(groups)
    for successors in quotient:
        for v in successors:
            indegree[v] += 1
    queue = deque(i for i, x in enumerate(indegree) if x == 0)
    removed = 0
    while queue:
        u = queue.popleft()
        removed += 1
        for v in quotient[u]:
            indegree[v] -= 1
            if indegree[v] == 0:
                queue.append(v)
    assert removed == len(groups)


def primitive_rotation(sequence):
    length = len(sequence)
    assert length > 0
    period = next(p for p in range(1, length + 1)
                  if length % p == 0 and
                  all(sequence[i] == sequence[i % p] for i in range(length)))
    primitive = sequence[:period]
    return min(primitive[i:] + primitive[:i] for i in range(period))


def certify(group, internal_edges):
    """All-edge phase label sets; no cycle sampling or tree-edge shortcut."""
    group = sorted(group)
    graph = {v: [] for v in group}
    for q, j, z, k, _ in internal_edges:
        graph[q, j].append((z, k))
    distance = {group[0]: 0}
    queue = deque([group[0]])
    while queue:
        u = queue.popleft()
        for v in graph[u]:
            if v not in distance:
                distance[v] = distance[u] + 1
                queue.append(v)
    assert len(distance) == len(group)
    cyclic = bool(internal_edges)
    d = 0
    for q, j, z, k, _ in internal_edges:
        d = gcd(d, abs(distance[q, j] + 1 - distance[z, k]))
    phase_labels = word = collision = None
    certified = False
    if cyclic:
        assert d > 0
        phases = [dict() for _ in range(d)]
        for edge in internal_edges:
            q, j, z, k, label = edge
            phase = distance[q, j] % d
            assert distance[z, k] % d == (phase + 1) % d
            phases[phase][label] = edge
        assert all(phases)
        certified = all(len(values) == 1 for values in phases)
        if certified:
            phase_labels = [next(iter(values)) for values in phases]
            word = primitive_rotation(phase_labels)
        else:
            conflicting = next(values for values in phases if len(values) > 1)
            labels = sorted(conflicting)
            collision = [conflicting[labels[0]], conflicting[labels[-1]]]
    else:
        assert len(group) == 1 and d == 0
    return {'vertices': group, 'internal_edge_count': len(internal_edges),
            'cyclic': cyclic, 'certified': certified,
            'h': [distance[v] for v in group], 'd': d,
            'phase_labels': phase_labels, 'word': word, 'collision': collision}


def stage(a, b, M, K, f, vertices):
    vertices = sorted(vertices)
    edges = edges_direct(a, b, M, K, vertices)
    graph = adjacency(vertices, edges)
    groups = tarjan(graph)
    verify_partition(graph, groups)
    owner = {}
    for group_id, group in enumerate(groups):
        for index in group:
            owner[vertices[index]] = group_id
    internal = [[] for _ in groups]
    for edge in edges:
        q, j, z, k, _ = edge
        if owner[q, j] == owner[z, k]:
            internal[owner[q, j]].append(edge)
    components = [certify([vertices[i] for i in group], internal[group_id])
                  for group_id, group in enumerate(groups)]
    retained = sorted(v for component in components
                      if component['cyclic'] and not component['certified']
                      for v in component['vertices'])
    refined = [(q, f * j + i) for q, j in retained for i in range(f)]
    return {'K': K, 'vertices': vertices, 'edges': edges,
            'components': components, 'retained': retained,
            'refined_vertices': refined}


def calculate(parameters, checkpoint=None):
    validate_parameters(**parameters)
    a, b, M, K, f, max_stages = (parameters[x]
                                for x in ('a', 'b', 'M', 'K0', 'f', 'max_stages'))
    vertices = all_vertices(M, K)
    result = {'schema_version': 1, 'parameters': parameters,
              'termination': 'inconclusive', 'stages': []}
    for index in range(max_stages):
        current = stage(a, b, M, K, f, vertices)
        result['stages'].append(current)
        if checkpoint:
            checkpoint(index, current)
        if not current['retained']:
            result['termination'] = 'success'
            break
        vertices = current['refined_vertices']
        K *= f
    return result
