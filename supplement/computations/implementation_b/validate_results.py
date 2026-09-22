"""Expected-table comparison and rejection tests for corrupted certificates."""

import argparse
import copy
import csv
import json
from pathlib import Path
import sys

from compare import check_document, compare_documents, load
from run import CASES, HERE, ROOT, summarize, write_json


def table_checks(documents):
    expected = ROOT / 'evidence/expected'
    with (expected / 'main-stages.csv').open() as stream:
        wanted_main = [{k: int(v) for k, v in row.items()} for row in csv.DictReader(stream)]
    actual_main = []
    for stage in summarize(documents['main'])['stages']:
        actual_main.append({key: stage[{'remaining_vertices': 'retained_vertices'}.get(key, key)]
                            for key in wanted_main[0]})
    assert actual_main == wanted_main
    expected_groups = []
    with (expected / 'periodic-components.csv').open() as stream:
        for row in csv.DictReader(stream):
            expected_groups.append({'K': int(row['K']), 'd': int(row['d']),
                                    'component_count': int(row['component_count']),
                                    'component_sizes': sorted(map(int, row['component_sizes'].split(';'))),
                                    'primitive_word': list(map(int, row['primitive_word'].split(';')))})
    actual_groups = []
    for stage in documents['main']['stages']:
        grouped = {}
        for component in stage['components']:
            if component['certified']:
                key = (component['d'], tuple(component['word']))
                grouped.setdefault(key, []).append(len(component['vertices']))
        for (d, word), sizes in grouped.items():
            actual_groups.append({'K': stage['K'], 'd': d, 'component_count': len(sizes),
                                  'component_sizes': sorted(sizes), 'primitive_word': list(word)})
    sort_groups = lambda groups: sorted(groups, key=lambda x: (x['K'], x['d'], x['primitive_word']))
    assert sort_groups(actual_groups) == sort_groups(expected_groups)
    actual_known = []
    for case in ('three-halves', 'four-thirds', 'five-fourths'):
        document = documents[case]
        stage = summarize(document)['stages'][0]
        actual_known.append({**{key: document['parameters'][key] for key in ('a', 'b', 'M')},
                             **{key: stage[key] for key in ('K', 'vertices', 'edges',
                                                          'cyclic_components', 'certified_components')},
                             'remaining_vertices': stage['retained_vertices']})
    with (expected / 'known-cases.csv').open() as stream:
        wanted_known = [{k: int(v) for k, v in row.items()} for row in csv.DictReader(stream)]
    assert actual_known == wanted_known
    return {'status': 'PASS', 'main_rows': actual_main,
            'periodic_groups': sort_groups(actual_groups), 'known_cases': actual_known}


def corruption_checks(original):
    records = []

    def reject(name, edit):
        document = copy.deepcopy(original)
        edit(document)
        try:
            check_document(document)
        except (ValueError, AssertionError, KeyError, TypeError):
            records.append({'mutation': name, 'result': 'REJECTED'})
        else:
            raise AssertionError('Accepted corruption: ' + name)

    def first_certified(document):
        return next(c for c in document['stages'][0]['components'] if c['certified'])

    def first_retained(document):
        return next(c for c in document['stages'][0]['components']
                    if c['cyclic'] and not c['certified'])

    reject('edge endpoint outside W, edge count preserved',
           lambda d: d['stages'][0]['edges'][0].__setitem__(0, -1))
    reject('duplicate edge replacing another, edge count preserved',
           lambda d: d['stages'][0]['edges'].__setitem__(1, d['stages'][0]['edges'][0]))
    reject('missing noncyclic SCC', lambda d: d['stages'][0]['components'].pop(0))
    reject('invalid shortest distance', lambda d: first_certified(d)['h'].__setitem__(0, 1))
    reject('incorrect gcd d', lambda d: first_certified(d).__setitem__('d', 7))
    reject('incorrect certification flag', lambda d: first_certified(d).__setitem__('certified', False))
    reject('incorrect phase label', lambda d: first_certified(d)['phase_labels'].__setitem__(0, 999))
    reject('incorrect primitive word', lambda d: first_certified(d)['word'].__setitem__(0, 999))
    reject('collision repeats identical edge',
           lambda d: first_retained(d)['collision'].__setitem__(1, first_retained(d)['collision'][0]))
    reject('retained set omission', lambda d: d['stages'][0]['retained'].pop())
    reject('refinement omission', lambda d: d['stages'][0]['refined_vertices'].pop())
    reject('next-stage vertex omission', lambda d: d['stages'][1]['vertices'].pop())
    reject('false termination', lambda d: d.__setitem__('termination', 'inconclusive'))
    return {'status': 'PASS', 'rejected_corruptions': records}






