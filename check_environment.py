#!/usr/bin/env python3
"""Report prerequisites without running the paper's proofs or finite reproduction."""
from __future__ import annotations

import argparse
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scope', choices=('compute', 'pdf', 'figures', 'lean', 'all'), default='compute')
    parser.add_argument('--output', type=Path, help='Optional new JSON file outside the package')
    args = parser.parse_args()
    if args.output and (args.output.resolve().is_relative_to(ROOT) or args.output.exists()):
        parser.error('Choose a new output file outside the package')
    checks = []

    def add(name, ok, detail):
        checks.append({'name': name, 'status': 'PASS' if ok else 'FAIL', 'detail': detail})

    def run(command, cwd=None):
        try:
            p = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=60)
            return p.returncode == 0, p.stdout.strip()
        except (OSError, subprocess.TimeoutExpired) as error:
            return False, str(error)

    def tool(name, flag='--version', cwd=None):
        ok, detail = run([name, flag], cwd)
        add(name, ok, detail.splitlines()[0] if detail else 'No version output')
        return ok

    add('python', (3, 10) <= sys.version_info[:2] < (3, 14), platform.python_version())
    add('assertions', __debug__, 'enabled' if __debug__ else 'disabled; remove -O / PYTHONOPTIMIZE')
    add('linux', sys.platform == 'linux' and Path('/proc/self/status').is_file(), platform.system())
    try:
        import resource
        add('POSIX resource controls', hasattr(os, 'killpg') and hasattr(resource, 'RLIMIT_AS'), 'resource.RLIMIT_AS and os.killpg')
    except ImportError:
        add('POSIX resource controls', False, 'Python resource module is unavailable')

    if args.scope in ('compute', 'all'):
        if tool('g++'):
            with tempfile.TemporaryDirectory(prefix='floor-environment-') as directory:
                work = Path(directory)
                source = work / 'check.cpp'
                source.write_text('#include <numeric>\n#include <vector>\nint main(){std::vector<int> v{14,10}; return std::gcd(v[0],v[1]) == 2 ? 0 : 1;}\n')
                ok, detail = run(['g++', '-std=c++17', str(source), '-o', str(work / 'check')])
                if ok:
                    ok, detail = run([str(work / 'check')])
                add('C++17 compile and run', ok, detail or 'exact integer smoke check passed')

    if args.scope in ('pdf', 'all'):
        try:
            version = importlib.metadata.version('pypdf')
            add('pypdf', version == '6.8.0', version + '; lock requires 6.8.0')
        except importlib.metadata.PackageNotFoundError:
            add('pypdf', False, 'Install requirements-pdf.txt or the locked pdf extra')
        if sys.version_info < (3, 11):
            try:
                version = importlib.metadata.version('typing_extensions')
                add('typing_extensions', version == '4.15.0', version)
            except importlib.metadata.PackageNotFoundError:
                add('typing_extensions', False, 'Install the complete locked PDF dependency set')
        tool('pdflatex')
        tool('lualatex')
        for filename in ('amsart.cls', 'lmodern.sty', 'fvextra.sty',
                         'luatexja-fontspec.sty', 'geometry.sty', 'booktabs.sty', 'needspace.sty',
                         'xurl.sty', 'hyperref.sty', 'tikz.sty', 'standalone.cls',
                         'HaranoAjiMincho-Regular.otf', 'HaranoAjiMincho-Bold.otf',
                         'HaranoAjiGothic-Medium.otf', 'HaranoAjiGothic-Bold.otf',
                         'lmromancaps10-regular.otf'):
            ok, detail = run(['kpsewhich', filename])
            identity = {'available': ok}
            if ok and Path(detail).is_file():
                identity['sha256'] = hashlib.sha256(Path(detail).read_bytes()).hexdigest()
            add(filename, ok, identity)
        ok, _ = run(['kpsewhich', 'lltjp-fancyvrb.sty'])
        japanese_source = ROOT / 'sources/paper-ja.tex'
        compatible = (japanese_source.is_file() and
                      r'\IfFileExists{lltjp-fancyvrb.sty}' in japanese_source.read_text())
        add('lltjp-fancyvrb.sty', ok or compatible,
            {'available': ok, 'conditional_compatibility_branch': compatible,
             'note': 'Recent LuaTeX-ja patch; older TeX distributions use the source compatibility branch.'})
    if args.scope in ('figures', 'all'):
        tool('pdflatex')
        tool('pdftocairo', '-v')
        tool('pdftoppm', '-v')
        tool('pdfinfo', '-v')
        tool('lualatex')
        for filename in ('tikz.sty', 'standalone.cls', 'lmodern.sty', 'luatexja-fontspec.sty',
                         'HaranoAjiMincho-Regular.otf', 'HaranoAjiMincho-Bold.otf',
                         'HaranoAjiGothic-Medium.otf'):
            ok, _ = run(['kpsewhich', filename])
            add(filename, ok, 'TeX file lookup')
    if args.scope in ('lean', 'all'):
        project = ROOT / 'supplement/lean'
        expected = (project / 'lean-toolchain').read_text().strip()
        ok, detail = run(['lean', '--version'], project)
        add('Lean toolchain', ok and '4.29.1' in detail, {'expected': expected, 'actual': detail})
        tool('lake', cwd=project)
        manifest = json.loads((project / 'lake-manifest.json').read_text())
        actual = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
        add('mathlib lock', actual == '5e932f97dd25535344f80f9dd8da3aab83df0fe6', actual)
        add('Lean project check scope', True, 'Only toolchain and lock checked; no Lean module was compiled')
    report = {'schema_version': 1, 'scope': args.scope,
              'status': 'PASS' if all(c['status'] == 'PASS' for c in checks) else 'FAIL',
              'platform': {'system': platform.system(), 'machine': platform.machine()},
              'checks': checks,
              'meaning': 'Prerequisite diagnostics only; not a finite computation or formal proof check.'}
    serialized = json.dumps(report, indent=2, ensure_ascii=False) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized)
    print(serialized, end='')
    return 0 if report['status'] == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
