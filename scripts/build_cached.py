"""Compile every project module using the existing, pinned local Mathlib cache.

The public portable build is `lake build`. This offline local runner uses an
ASCII temporary working directory and records source hashes and compiler output.
It does not treat a generated certificate or Python assertion as a Lean proof.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = ROOT.parent
MATHLIB = WORKSPACE / 'lean_deps/mathlib4-4.33.1'
LEAN = Path.home() / '.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean.exe'
sys.stdout.reconfigure(encoding='utf-8')
BUILD = Path(tempfile.mkdtemp(prefix='lemniscate-lean-'))
RESULTS = ROOT / 'audit/results'
RESULTS.mkdir(parents=True, exist_ok=True)
previous = {}
if (RESULTS/'build.json').exists() and '--fresh' not in sys.argv:
    previous = json.loads((RESULTS/'build.json').read_text(encoding='utf-8'))
sources = list((ROOT/'Lemniscate').glob('*.lean'))
sources = [p for p in sources if p.stem not in ('Probe', 'SmallProbe')]
sources += [ROOT/'Lemniscate.lean'] if (ROOT/'Lemniscate.lean').exists() else []
modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p for p in sources}
order, active, done = [], set(), set()
def visit(m):
    if m in done:
        return
    if m in active:
        raise RuntimeError('cyclic import: '+m)
    active.add(m)
    for dep in re.findall(r'^import\s+(\S+)', modules[m].read_text(encoding='utf-8'), re.M):
        if dep in modules:
            visit(dep)
    active.remove(m)
    done.add(m)
    order.append(m)
for m in modules:
    visit(m)

old_modules = {m['module']: m for m in previous.get('modules', []) if m.get('exit_code') == 0}
old_build = Path(previous.get('build_directory', '__missing_build__'))
reusable = {}
def can_reuse(m):
    if m in reusable:
        return reusable[m]
    src = modules[m]
    old = old_modules.get(m, {})
    result = old.get('sha256') == hashlib.sha256(src.read_bytes()).hexdigest()
    result = result and (old_build/src.relative_to(ROOT).with_suffix('.olean')).exists()
    if result:
        for dep in re.findall(r'^import\s+(\S+)', src.read_text(encoding='utf-8'), re.M):
            if dep in modules and not can_reuse(dep):
                result = False
                break
    reusable[m] = result
    return result

paths = [BUILD, MATHLIB/'.lake/build/lib/lean']
paths += [p/'.lake/build/lib/lean' for p in (MATHLIB/'.lake/packages').iterdir() if p.is_dir()]
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
report = {'build_directory': str(BUILD), 'compiler': str(LEAN), 'modules': []}
failed = set()
version = subprocess.run([str(LEAN), '--version'], capture_output=True, text=True, check=True)
report['version'] = version.stdout.strip()
print(report['version'], flush=True)
for m in order:
    src = modules[m]
    rel = src.relative_to(ROOT)
    dst = BUILD/rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)
    deps = re.findall(r'^import\s+(\S+)', src.read_text(encoding='utf-8'), re.M)
    if any(dep in failed for dep in deps):
        failed.add(m)
        report['modules'].append({'module': m, 'skipped': 'failed dependency'})
        continue
    if can_reuse(m):
        shutil.copyfile(old_build/rel.with_suffix('.olean'), dst.with_suffix('.olean'))
        report['modules'].append({'module': m, 'sha256': hashlib.sha256(src.read_bytes()).hexdigest(),
            'exit_code': 0, 'reused_from': str(old_build), 'elapsed_seconds': 0})
        print('Reusing checked module '+m, flush=True)
        continue
    start = time.monotonic()
    print('Compiling '+m, flush=True)
    proc = subprocess.run([str(LEAN), '-o', str(rel.with_suffix('.olean')), str(rel)],
                          cwd=BUILD, env=env, capture_output=True, text=True, encoding='utf-8', timeout=600)
    log = proc.stdout+proc.stderr
    (RESULTS/(m+'.log')).write_text(log, encoding='utf-8')
    item = {'module': m, 'sha256': hashlib.sha256(src.read_bytes()).hexdigest(),
            'exit_code': proc.returncode, 'elapsed_seconds': round(time.monotonic()-start, 3)}
    report['modules'].append(item)
    print(log, end='', flush=True)
    print('Exit '+str(proc.returncode), flush=True)
    (RESULTS/'build.json').write_text(json.dumps(report, indent=2), encoding='utf-8')
    if proc.returncode:
        failed.add(m)
report['all_succeeded'] = not failed
(RESULTS/'build.json').write_text(json.dumps(report, indent=2), encoding='utf-8')
if failed:
    print('Failed modules: '+', '.join(sorted(failed)), flush=True)
    raise SystemExit(1)
print('All '+str(len(order))+' modules compiled.', flush=True)
