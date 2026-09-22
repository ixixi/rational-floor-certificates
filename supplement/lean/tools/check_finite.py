#!/usr/bin/env python3
"""Sequential, bounded Lean builds. A successful exit is a record, not a Lean axiom."""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import time

ROOT=Path(__file__).resolve().parents[2]
LIMIT_SECONDS=1200
LIMIT_RSS=8*1024**3
PAGE_SIZE=os.sysconf('SC_PAGE_SIZE')

def group_rss(group):
    total=0
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():
            continue
        try:
            # fields following '(comm)' begin with state (field 3).
            fields=(p/'stat').read_text().rsplit(')',1)[1].split()
            if int(fields[2]) == group:  # process group, field 5
                total += int((p/'statm').read_text().split()[1])*PAGE_SIZE
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            pass
    return total

parser=argparse.ArgumentParser()
parser.add_argument('modules',nargs='*')
args=parser.parse_args()
modules=args.modules or ([f'MathPaper.Finite.Data{t}' for t in range(4)] +
    json.loads((ROOT/'lean/certificates/verification-modules.json').read_text()) + ['MathPaper.MainCertificate', 'MathPaper.Finite.CertificateAudit'])
run_id=time.strftime('%Y%m%d-%H%M%S')
results=[]
(ROOT/'build').mkdir(parents=True, exist_ok=True)
for module in modules:
    log=ROOT/f'build/lean-finite-{run_id}-{module.rsplit(".",1)[-1]}.log'
    start=time.monotonic();peak=0;reason='exit'
    with log.open('w') as stream:
        proc=subprocess.Popen(['lake','build',module],cwd=ROOT/'lean',stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
        while proc.poll() is None:
            rss=group_rss(proc.pid);peak=max(peak,rss)
            if rss > LIMIT_RSS or time.monotonic()-start > LIMIT_SECONDS:
                reason='rss_limit' if rss>LIMIT_RSS else 'time_limit'
                os.killpg(proc.pid,signal.SIGTERM)
                try: proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid,signal.SIGKILL);proc.wait()
                break
            time.sleep(0.25)
    row={'module':module,'returncode':proc.returncode,'reason':reason,
         'seconds':round(time.monotonic()-start,3),'peak_group_rss_bytes':peak,'log':str(log.relative_to(ROOT))}
    results.append(row)
    (ROOT/f'build/lean-finite-run-{run_id}.json').write_text(json.dumps({'limits':{'seconds_per_module':LIMIT_SECONDS,'group_rss_bytes':LIMIT_RSS},'results':results},indent=2)+'\n')
    print(json.dumps(row),flush=True)
    if proc.returncode or reason!='exit':
        raise SystemExit(1)
