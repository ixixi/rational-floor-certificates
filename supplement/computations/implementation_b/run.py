"""Bounded runs with pre-execution provenance; standard library only."""

import argparse
import csv
from datetime import datetime, timezone
import gzip
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import subprocess
import sys
import time

from core import calculate

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
CASES = {'main': (7, 5, 4290, 32, 4, 4),
         'three-halves': (3, 2, 770, 32, 4, 1),
         'four-thirds': (4, 3, 30, 32, 4, 1),
         'five-fourths': (5, 4, 6006, 32, 4, 1)}


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        while chunk := stream.read(1 << 20):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path, data):
    Path(path).write_text(json.dumps(data, sort_keys=True, indent=2,
                                    ensure_ascii=False) + '\n')


def write_scientific(path, data):
    encoded = (json.dumps(data, separators=(',', ':'), sort_keys=True) + '\n').encode()
    with Path(path).open('wb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as packed:
            packed.write(encoded)


def summarize(scientific):
    rows = []
    periodic = []
    for index, stage in enumerate(scientific['stages']):
        components = stage['components']
        cyclic = [c for c in components if c['cyclic']]
        certified = [c for c in cyclic if c['certified']]
        rows.append({'stage': index, 'K': stage['K'],
                     'vertices': len(stage['vertices']), 'edges': len(stage['edges']),
                     'components': len(components), 'cyclic_components': len(cyclic),
                     'certified_components': len(certified),
                     'retained_vertices': len(stage['retained']),
                     'uncertified_cyclic_components': len(cyclic) - len(certified)})
        classes = {}
        for component in certified:
            key = (len(component['vertices']), component['internal_edge_count'],
                   component['d'], tuple(component['word']))
            classes[key] = classes.get(key, 0) + 1
        for (n, m, d, word), multiplicity in sorted(classes.items()):
            periodic.append({'stage': index, 'K': stage['K'],
                             'vertices_per_component': n, 'edges_per_component': m,
                             'd': d, 'primitive_period': len(word), 'word': list(word),
                             'multiplicity': multiplicity})
    return {'termination': scientific['termination'], 'stages': rows,
            'periodic_component_groups': periodic}


def worker(case, raw, results):
    parameters = dict(zip(('a', 'b', 'M', 'K0', 'f', 'max_stages'), CASES[case]))

    def checkpoint(index, stage):
        write_scientific(raw / f'stage-{index:03}.json.gz', stage)
        print(json.dumps({'stage': index, 'K': stage['K'],
                          'vertices': len(stage['vertices']), 'edges': len(stage['edges']),
                          'retained': len(stage['retained'])}), flush=True)

    scientific = calculate(parameters, checkpoint)
    write_scientific(raw / 'scientific.json.gz', scientific)
    summary = summarize(scientific)
    write_json(results / 'summary.json', summary)
    for name, records in (('stages', summary['stages']),
                          ('periodic-components', summary['periodic_component_groups'])):
        if records:
            with (results / f'{name}.csv').open('w', newline='') as stream:
                writer = csv.DictWriter(stream, fieldnames=list(records[0]))
                writer.writeheader()
                writer.writerows(records)
    print(json.dumps({'termination': scientific['termination']}), flush=True)




def main():
    parser = argparse.ArgumentParser(description="One-step B worker; use reproduce.py for bounded runs.")
    parser.add_argument("case", choices=[*CASES, "tests"])
    parser.add_argument("--worker", action="store_true", required=True)
    parser.add_argument("--raw", type=Path, required=True)
    parser.add_argument("--results", type=Path, required=True)
    args = parser.parse_args()
    worker(args.case, args.raw, args.results)


if __name__ == '__main__':
    main()
