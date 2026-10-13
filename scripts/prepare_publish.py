"""Prepare an explicit publication file list only after source-matched Lean success.

This does not publish or authenticate. It refuses stale or partial build records.
The JSON payload is consumed by the connected GitHub API, not by a shell.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
results = root/'audit/results'
report = json.loads((results/'build.json').read_text(encoding='utf-8'))
if not report.get('all_succeeded'):
    raise SystemExit('The latest Lean build did not succeed.')
sources = list((root/'Lemniscate').glob('*.lean')) + [root/'Lemniscate.lean']
source_modules = {'.'.join(p.relative_to(root).with_suffix('').parts): p for p in sources}
modules = {m['module']: m for m in report['modules']}
if set(source_modules) != set(modules):
    raise SystemExit('Build record does not cover exactly all Lean modules.')
for name, path in source_modules.items():
    item = modules[name]
    if item.get('exit_code') != 0 or item['sha256'] != hashlib.sha256(path.read_bytes()).hexdigest():
        raise SystemExit('Uncompiled or changed source: ' + name)
subprocess.run([sys.executable, str(root/'scripts/check_axioms.py'),
                str(results/'Lemniscate.AxiomAudit.log')], check=True, stdout=sys.stderr)
public = {
    'scope': 'Partial formalization; the full paper theorem is not yet formalized.',
    'version': report['version'], 'all_listed_modules_compiled': True,
    'modules': [{'module': m, 'sha256': modules[m]['sha256'], 'exit_code': 0}
                for m in sorted(modules)]
}
(results/'verification.json').write_text(json.dumps(public, indent=2)+'\n', encoding='utf-8')
files = [root/'README.md', root/'lakefile.toml', root/'lake-manifest.json',
         root/'lean-toolchain', root/'.gitignore']
for pattern in ['Lemniscate*.lean', 'Lemniscate/*.lean', '.github/workflows/*.yml',
                'scripts/*.py', 'audit/*.md', 'audit/source/original.tex',
                'audit/source/sections/*.tex', 'audit/recompute/*.py',
                'audit/recompute/*.json', 'audit/results/Lemniscate*.log']:
    files += list(root.glob(pattern))
files += [results/'verification.json', results/'expanded_arithmetic_data.json']
entries = []
for p in sorted(set(files)):
    entries.append({'path': p.relative_to(root).as_posix(), 'mode':'100644',
                    'type':'blob', 'content':p.read_text(encoding='utf-8')})
payload = {'tree_elements': entries}
(results/'publish-payload.json').write_text(json.dumps(payload, ensure_ascii=False), encoding='utf-8')
if '--emit' in sys.argv:
    sys.stdout.reconfigure(encoding='utf-8')
    print(json.dumps(payload, ensure_ascii=False))
else:
    print(f'Prepared {len(entries)} files after checking {len(modules)} source hashes.')
