#!/usr/bin/env python3
"""Recompute one-step A/B data and compare fresh arrays, tables and witnesses."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys
import time

from reproduce import bounded, dump, sha

PUBLIC = Path(__file__).resolve().parent
CASES = ('main', 'three-halves', 'four-thirds', 'five-fourths')

def selected(scope):
    return CASES if scope == 'full' else ('four-thirds',)

def compare_fresh(args):
    sys.path.insert(0, str(args.workspace / 'computations/implementation_b'))
    from compare import compare_documents, load
    from validate_results import table_checks, corruption_checks
    reference = json.loads((PUBLIC / 'checks/reference.json').read_text())
    records = []
    for case in selected(args.scope):
        a = args.output / f'a-{case}/raw/scientific.json'
        b = args.output / f'b-{case}/raw/scientific.json.gz'
        row = {'case': case, **compare_documents(load(a), load(b)), 'reference_matches': {}}
        for kind, path in (('A', a), ('B', b)):
            expected = reference['step'][case][kind]
            actual = {'bytes': path.stat().st_size, 'sha256': sha(path)}
            if actual != expected:
                raise ValueError(f'{case} {kind}: regenerated output differs from the reference fingerprint')
            row['reference_matches'][kind] = actual
        records.append(row)
    result = {'status': 'PASS', 'scope': args.scope, 'cases': records}
    if args.scope == 'full':
        certificate = args.output / 'a-main/raw/certificate.json'
        actual = {'bytes': certificate.stat().st_size, 'sha256': sha(certificate)}
        if actual != reference['step_certificate']:
            raise ValueError('Regenerated one-step certificate differs from its reference fingerprint')
        result['main_certificate'] = actual
        documents = {case: load(args.output / f'b-{case}/raw/scientific.json.gz') for case in CASES}
        result['expected_tables'] = table_checks(documents)
        result['corruption_detection'] = corruption_checks(documents['main'])
        if len(result['corruption_detection']['rejected_corruptions']) != 13:
            raise ValueError('Incomplete corruption rejection checks')
    dump(args.output / 'fresh-comparison.json', result)

def run(args):
    if args.output.exists():
        raise ValueError('Choose a fresh output directory')
    if args.output.is_relative_to(PUBLIC) or PUBLIC.is_relative_to(args.output):
        raise ValueError('Output must be outside the distributed repository')
    args.output.mkdir(parents=True)
    reference = json.loads((PUBLIC / 'checks/reference.json').read_text())
    record = {'status': 'running', 'scope': args.scope, 'commands': [],
              'reference_sha256': sha(PUBLIC / 'checks/reference.json'),
              'limits': {'per_command_seconds': args.command_seconds, 'total_seconds': args.total_seconds,
                         'memory_gib': args.memory_gib}}
    dump(args.output / 'record.json', record)
    started = time.monotonic()
    python = [sys.executable, '-B']
    commands = [
        (python + ['-m', 'unittest', 'discover', '-s', 'computations/implementation_a', '-p', 'test_verifier.py', '-v'], 'a-tests', 60, 512 << 20),
        (python + ['computations/implementation_b/checks.py'], 'b-tests', 60, 512 << 20),
    ]
    for case in selected(args.scope):
        parameters = reference['step'][case]['parameters']
        for kind in ('a', 'b'):
            base = args.output / f'{kind}-{case}'
            (base / 'raw').mkdir(parents=True)
            (base / 'results').mkdir()
            if kind == 'a':
                config = {'parameters': parameters, 'limits': {'address_space_bytes': min(4, args.memory_gib) << 30},
                          'raw_directory': str(base / 'raw'), 'results_directory': str(base / 'results')}
                dump(base / 'config.json', config)
                command = python + ['computations/implementation_a/run_case.py', '--worker', str(base / 'config.json')]
            else:
                command = python + ['computations/implementation_b/run.py', case, '--worker',
                                    '--raw', str(base / 'raw'), '--results', str(base / 'results')]
            commands.append((command, kind + '-' + case, 600, min(4, args.memory_gib) << 30))
    commands.append((python + [str(PUBLIC / 'reproduce_step.py'), 'compare-fresh', '--scope', args.scope,
                               '--workspace', str(args.workspace), '--output', str(args.output)],
                     'fresh-comparison', 120, min(4, args.memory_gib) << 30))
    try:
        for command, name, seconds, memory in commands:
            remaining = args.total_seconds - (time.monotonic() - started)
            if remaining <= 0:
                record['status'] = 'inconclusive'
                raise TimeoutError('One-step replay deadline reached')
            row = bounded(command, args.output, name, min(seconds, args.command_seconds, remaining),
                          memory, cwd=args.workspace)
            record['commands'].append(row)
            dump(args.output / 'record.json', record)
            if row['status'] != 'PASS':
                record['status'] = row['status']
                raise RuntimeError(name + ': ' + row['status'])
        if json.loads((args.output / 'fresh-comparison.json').read_text())['status'] != 'PASS':
            raise ValueError('Fresh comparison did not pass')
        if sha(PUBLIC / 'checks/reference.json') != record['reference_sha256']:
            raise ValueError('Reference changed during replay')
        record['status'] = 'PASS'
    except BaseException as error:
        if record['status'] == 'running':
            record['status'] = 'inconclusive' if isinstance(error, (TimeoutError, MemoryError)) else 'FAIL'
        record['error'] = repr(error)
        raise
    finally:
        record['elapsed_seconds'] = time.monotonic() - started
        record['outputs'] = [{'path': p.relative_to(args.output).as_posix(), 'bytes': p.stat().st_size, 'sha256': sha(p)}
                             for p in sorted(args.output.rglob('*')) if p.is_file() and p.name != 'record.json']
        dump(args.output / 'record.json', record)
        print(json.dumps({'status': record['status'], 'scope': args.scope}), flush=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('run', 'compare-fresh'))
    parser.add_argument('--scope', choices=('preflight', 'full'), required=True)
    parser.add_argument('--workspace', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--command-seconds', type=int, default=600)
    parser.add_argument('--total-seconds', type=int, default=1800)
    parser.add_argument('--memory-gib', type=int, default=8)
    args = parser.parse_args()
    if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
        parser.error('Keep assertions enabled')
    if min(args.command_seconds, args.total_seconds, args.memory_gib) <= 0:
        parser.error('Resource limits must be positive')
    args.workspace = args.workspace.resolve()
    args.output = args.output.resolve()
    if args.mode == 'compare-fresh':
        compare_fresh(args)
    else:
        run(args)

if __name__ == '__main__':
    main()
