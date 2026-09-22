#!/usr/bin/env python3
"""Render untrusted A witness data; every semantic condition is checked in Lean."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--certificate', required=True, type=Path)
parser.add_argument('--output-root', required=True, type=Path)
args = parser.parse_args()
ROOT = args.output_root.resolve()
if ROOT.exists():
    parser.error('Choose a fresh output root')
(ROOT / 'lean/MathPaper/Finite').mkdir(parents=True)
(ROOT / 'lean/certificates').mkdir(parents=True)
INPUT = args.certificate.resolve()
EXPECTED = 'a7701fa1fa236efde4a36ece8fa4774def80ddf3a009a57c10ef149ac267f718'
OUT = ROOT / 'lean/MathPaper/Finite'
raw = INPUT.read_bytes()
assert hashlib.sha256(raw).hexdigest() == EXPECTED
source = json.loads(raw)
manifest = {'input': INPUT.name, 'input_sha256': EXPECTED, 'stages': []}


def data_expr(items):
    if not items:
        return '.nil'
    m = len(items) // 2
    k, owner, phase = items[m]
    return f'(.node {k} ⟨{owner}, {phase}⟩ {data_expr(items[:m])} {data_expr(items[m+1:])})'


for t, stage in enumerate(source['stages']):
    K = stage['K']
    items = []
    for (q, j), b, phase in zip(stage['vertices'], stage['owner'], stage['phase'], strict=True):
        block = stage['blocks'][b]
        word = sum((e+4) * 16**p for p, e in enumerate(block['phase_labels']))
        desc = int(block['kind'] == 'retained') + 2 * block['d'] + 32 * word
        assert 0 <= desc < 2**64
        owner = block['rank'] * 2**64 + desc
        items.append((q*K+j, owner, phase))
    assert items == sorted(items)
    declarations = []
    nodes = []
    def emit(xs, name):
        if len(xs) <= 127:
            declarations.append(f'noncomputable def {name} : Tree := {data_expr(xs)}\n')
            nodes.append({'name': name, 'size': len(xs), 'kind': 'leaf'})
        else:
            m = len(xs)//2
            left, right = name+'l', name+'r'
            emit(xs[:m], left)
            emit(xs[m+1:], right)
            k, o, p = xs[m]
            declarations.append(f'noncomputable def {name} : Tree := .node {k} ⟨{o}, {p}⟩ {left} {right}\n')
            nodes.append({'name':name, 'size':len(xs), 'kind':'node', 'key':k, 'owner':o, 'phase':p, 'left':left,'right':right})
    name = f'data{t}'
    emit(items, name)
    path = OUT / f'Data{t}.lean'
    path.write_text('import MathPaper.Finite.Checker\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace MathPaper.Finite\n\n'+'\n'.join(declarations)+'\nend MathPaper.Finite\n')
    manifest['stages'].append({'K': K, 'root': name, 'nodes':nodes, 'path':str(path.relative_to(ROOT)), 'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
manifest['generator_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(ROOT / 'lean/certificates/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Generated four trees:', [(s['K'],len(s['nodes'])) for s in manifest['stages']])
