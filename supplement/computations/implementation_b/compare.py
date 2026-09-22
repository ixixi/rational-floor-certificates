"""Elementwise comparison of frozen independent outputs; A code is never read."""

import argparse
import gzip
import json
from pathlib import Path
import sys

from core import (adjacency, all_vertices, certify, validate_parameters,
                  verify_partition)
from run import CASES, HERE, ROOT, sha, write_json

TOP_KEYS = {'schema_version', 'parameters', 'termination', 'stages'}
STAGE_KEYS = {'K', 'vertices', 'edges', 'components', 'retained', 'refined_vertices'}
COMPONENT_KEYS = {'vertices', 'internal_edge_count', 'cyclic', 'certified',
                  'h', 'd', 'phase_labels', 'word', 'collision'}


def load(path):
    if str(path).endswith('.gz'):
        with gzip.open(path, 'rt') as stream:
            return json.load(stream)
    return json.loads(Path(path).read_text())


def require(condition, context):
    if not condition:
        raise ValueError(context)


def normalized(values, width, context):
    require(all(isinstance(v, list) and len(v) == width and
                all(type(x) is int for x in v) for v in values), context + ': shape')
    tuples = [tuple(v) for v in values]
    require(tuples == sorted(set(tuples)), context + ': sorting/uniqueness')
    return tuples


def check_document(document):
    require(TOP_KEYS <= document.keys(), 'missing document fields')
    require(document['schema_version'] == 1, 'schema')
    p = document['parameters']
    validate_parameters(**p)
    a, b, M, K, f, limit = (p[x] for x in ('a', 'b', 'M', 'K0', 'f', 'max_stages'))
    require(0 < len(document['stages']) <= limit, 'stage count')
    expected_vertices = all_vertices(M, K)
    extras = {'document': sorted(set(document) - TOP_KEYS), 'stages': [], 'components': []}
    counts = []
    for index, stage in enumerate(document['stages']):
        context = f'stage {index}'
        require(STAGE_KEYS <= stage.keys(), context + ': missing fields')
        extras['stages'].append(sorted(set(stage) - STAGE_KEYS))
        require(stage['K'] == K, context + ': K')
        vertices = normalized(stage['vertices'], 2, context + ': vertices')
        edges = normalized(stage['edges'], 5, context + ': edges')
        require(vertices == expected_vertices, context + ': initial/refinement coverage')
        allowed = set(vertices)
        for q, j, z, k, e in edges:
            require((q, j) in allowed and (z, k) in allowed,
                    context + ': edge endpoints')
            require(1-b <= e <= a-1 and (b*z-a*q-e) % M == 0 and
                    a*j-b*(k+1) < e*K < a*(j+1)-b*k,
                    context + ': illegal edge')
        components = stage['components']
        groups = []
        number = {v: i for i, v in enumerate(vertices)}
        owner = {}
        component_extras = set()
        for group_id, component in enumerate(components):
            require(COMPONENT_KEYS <= component.keys(), context + ': component fields')
            component_extras.update(set(component) - COMPONENT_KEYS)
            group = normalized(component['vertices'], 2, context + ': component vertices')
            require(bool(group), context + ': empty component')
            groups.append([number[v] for v in group])
            for v in group:
                require(v not in owner, context + ': overlapping component')
                owner[v] = group_id
        require([g[0] for g in groups] == sorted(g[0] for g in groups),
                context + ': component ordering')
        verify_partition(adjacency(vertices, edges), groups)
        extras['components'].append(sorted(component_extras))
        internal = [[] for _ in groups]
        for edge in edges:
            if owner[edge[:2]] == owner[edge[2:4]]:
                internal[owner[edge[:2]]].append(edge)
        retained = []
        witnesses = 0
        for group_id, component in enumerate(components):
            recalculated = certify([vertices[i] for i in groups[group_id]], internal[group_id])
            # JSON-normalize B tuples before exact scalar/array comparison.
            recalculated = json.loads(json.dumps(recalculated))
            for key in COMPONENT_KEYS - {'collision'}:
                require(component[key] == recalculated[key],
                        context + f': invalid component {group_id} {key}')
            collision = component['collision']
            if component['cyclic'] and not component['certified']:
                require(isinstance(collision, list) and len(collision) == 2,
                        context + ': absent collision')
                require(all(isinstance(edge, list) and len(edge) == 5 and
                            all(type(x) is int for x in edge) for edge in collision),
                        context + ': collision shape')
                x, y = map(tuple, collision)
                internal_set = set(internal[group_id])
                require(x in internal_set and y in internal_set,
                        context + ': collision is not internal edge')
                distance = dict(zip(map(tuple, component['vertices']), component['h']))
                require(x[4] != y[4] and distance[x[:2]] % component['d'] ==
                        distance[y[:2]] % component['d'], context + ': invalid collision')
                witnesses += 1
                retained.extend(map(tuple, component['vertices']))
            else:
                require(collision is None, context + ': unexpected collision')
        retained.sort()
        require(normalized(stage['retained'], 2, context + ': retained') == retained,
                context + ': wrong retained union')
        expected_vertices = [(q, f*j+i) for q, j in retained for i in range(f)]
        require(normalized(stage['refined_vertices'], 2, context + ': refined') ==
                expected_vertices, context + ': wrong refinement')
        require(index == len(document['stages']) - 1 or retained,
                context + ': continued after success')
        counts.append({'stage': index, 'K': K, 'vertices': len(vertices),
                       'edges': len(edges), 'components': len(components),
                       'internal_edges': sum(map(len, internal)),
                       'h_entries': sum(len(c['h']) for c in components),
                       'collision_witnesses_checked': witnesses,
                       'retained': len(retained), 'refined_vertices': len(expected_vertices)})
        K *= f
    require(document['termination'] == ('success' if not expected_vertices else 'inconclusive'),
            'incorrect termination flag')
    return {'counts': counts, 'additional_fields': extras}


def compare_documents(a, b):
    checked_a = check_document(a)
    checked_b = check_document(b)
    for key in TOP_KEYS - {'stages'}:
        require(a[key] == b[key], 'different ' + key)
    require(len(a['stages']) == len(b['stages']), 'different number of stages')
    different_valid_witnesses = 0
    for index, (x, y) in enumerate(zip(a['stages'], b['stages'])):
        for key in STAGE_KEYS - {'components'}:
            # Full arrays, not hashes or counts, are compared here.
            require(x[key] == y[key], f'stage {index}: different {key}')
        by_vertices_a = {tuple(map(tuple, c['vertices'])): c for c in x['components']}
        by_vertices_b = {tuple(map(tuple, c['vertices'])): c for c in y['components']}
        require(by_vertices_a.keys() == by_vertices_b.keys(), f'stage {index}: SCC partition')
        for vertices, ca in by_vertices_a.items():
            cb = by_vertices_b[vertices]
            for key in COMPONENT_KEYS - {'collision'}:
                require(ca[key] == cb[key], f'stage {index}: component {vertices[0]} {key}')
            if ca['collision'] != cb['collision']:
                different_valid_witnesses += 1
    return {'status': 'PASS', 'elementwise_comparison': True,
            'checked_fields': {'document': sorted(TOP_KEYS - {'stages'}),
                               'stage': sorted(STAGE_KEYS),
                               'component': sorted(COMPONENT_KEYS - {'collision'})},
            'collision_policy': 'Every witness individually validated; selection may differ.',
            'different_valid_collision_selections': different_valid_witnesses,
            'A_validation': checked_a, 'B_validation': checked_b,
            'additional_field_policy': 'Only schema 1 fields are compared; extra fields are listed, not scientific inputs to B.'}






