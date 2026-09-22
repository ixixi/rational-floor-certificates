#!/usr/bin/env python3
"""Generate kernel proof commands and structural compositions, never proof axioms."""
import argparse
import json
from pathlib import Path
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output-root', required=True, type=Path)
ROOT = parser.parse_args().output_root.resolve()
OUT=ROOT/'lean/MathPaper/Finite'
m=json.loads((ROOT/'lean/certificates/manifest.json').read_text())
modules=[]
for t,s in enumerate(m['stages']):
    prev=f'MathPaper.Finite.Data{t}'
    nodes=s['nodes'];K=s['K'];root=s['root']
    for start in range(0,len(nodes),32):
        mod=f'MathPaper.Finite.Verify{t}_{start//32:02d}'
        lines=[f'import {prev}', 'import MathPaper.Finite.Fast', 'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', 'namespace MathPaper.Finite', '']
        for n in nodes[start:start+32]:
            name=n['name']
            head=f'theorem {name}_checked : {name}.all (checkSourceFast {root} {K}) = true := by'
            lines.append(head)
            if n['kind']=='leaf':
                lines.append('  decide +kernel')
            else:
                lines.append(f'  exact Tree.all_node_true (checkSourceFast {root} {K}) {n["key"]} ⟨{n["owner"]}, {n["phase"]}⟩ {n["left"]} {n["right"]} (by decide +kernel) {n["left"]}_checked {n["right"]}_checked')
            lines.append('')
        lines.append('end MathPaper.Finite\n')
        (OUT/(mod.rsplit('.',1)[1]+'.lean')).write_text('\n'.join(lines))
        modules.append(mod);prev=mod
    s['verification_module']=prev
# Partition transition, initial-cover, and empty-set checks as well.
def tree_checks(nodes, predicate, suffix, imports, module_prefix):
    previous = None
    for start in range(0, len(nodes), 32):
        mod = f'MathPaper.Finite.{module_prefix}{start//32:02d}'
        lines = [f'import {previous}'] if previous else [f'import {name}' for name in imports]
        lines += ['set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', 'namespace MathPaper.Finite', '']
        for node in nodes[start:start+32]:
            name = node['name']
            lines.append(f'theorem {name}_{suffix} : {name}.all ({predicate}) = true := by')
            if node['kind'] == 'leaf':
                lines.append('  decide +kernel')
            else:
                lines.append(f'  exact Tree.all_node_true ({predicate}) {node["key"]} ⟨{node["owner"]}, {node["phase"]}⟩ {node["left"]} {node["right"]} (by decide +kernel) {node["left"]}_{suffix} {node["right"]}_{suffix}')
            lines.append('')
        lines.append('end MathPaper.Finite\n')
        (OUT/(mod.rsplit('.',1)[1]+'.lean')).write_text('\n'.join(lines))
        modules.append(mod)
        previous = mod
    return previous

for t in range(3):
    predicate = f'checkRefine data{t+1} {m["stages"][t]["K"]}'
    previous = tree_checks(m['stages'][t]['nodes'], predicate, 'refined',
        [f'MathPaper.Finite.Data{t}', f'MathPaper.Finite.Data{t+1}'], f'Refine{t}_')
    mod = f'MathPaper.Finite.Refinement{t}'
    (OUT/f'Refinement{t}.lean').write_text(f"""import {previous}
namespace MathPaper.Finite
theorem refinement{t}_checked : data{t}.all ({predicate}) = true := data{t}_refined
end MathPaper.Finite
""")
    modules.append(mod)

# 67 full blocks of 64 residues and one block of 2 residues: exactly 4290.
previous = None
for first in range(0,68,8):
    mod = f'MathPaper.Finite.Initial{first//8:02d}'
    lines = [f'import {previous}'] if previous else ['import MathPaper.Finite.Data0', 'import MathPaper.Finite.Split']
    lines += ['set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', 'namespace MathPaper.Finite', '']
    if first == 0:
        lines.append('theorem initialPrefix0 : allBelow 0 (initialRow data0) = true := rfl\n')
    for b in range(first,min(first+8,68)):
        offset=b*64;count=min(64,4290-offset)
        lines += [f'theorem initialChunk{b} : allBelow {count} (fun i => initialRow data0 ({offset} + i)) = true := by decide +kernel',
                  f'theorem initialPrefix{b+1} : allBelow {offset+count} (initialRow data0) = true :=',
                  f'  allBelow_join {offset} {count} (initialRow data0) initialPrefix{b} initialChunk{b}', '']
    lines.append('end MathPaper.Finite\n')
    (OUT/(mod.rsplit('.',1)[1]+'.lean')).write_text('\n'.join(lines))
    modules.append(mod);previous=mod
initial_module=previous
empty_module=tree_checks(m['stages'][3]['nodes'], 'fun _ d => !ownerRetained d.owner',
    'empty', ['MathPaper.Finite.Data3'], 'Empty')
(OUT/'Boundary.lean').write_text(f"""import {initial_module}
import {empty_module}
namespace MathPaper.Finite
theorem initial_checked : checkInitial data0 = true := initialPrefix68
theorem final_checked : checkEmpty data3 = true := data3_empty
end MathPaper.Finite
""")
modules.append('MathPaper.Finite.Boundary')
(ROOT/'lean/certificates/verification-modules.json').write_text(json.dumps(modules,indent=2)+'\n')
(ROOT/'lean/certificates/manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print('Generated',len(modules),'verification modules; no evaluations have been run by this script.')
