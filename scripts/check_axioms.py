"""Reject missing audit output or axioms outside Lean's standard foundations."""
from pathlib import Path
import re
import sys

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
audit_source = Path(__file__).resolve().parents[1] / 'Lemniscate/AxiomAudit.lean'
expected = re.findall(r'^#print axioms (\S+)', audit_source.read_text(encoding='utf-8'), re.M)
log = Path(sys.argv[1]).read_text(encoding='utf-8')
found = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    found[name] = {a.strip() for a in axioms.split(',') if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
    found[name] = set()
for name in expected:
    if name not in found:
        raise SystemExit('Missing axiom audit: ' + name)
    extra = found[name] - allowed
    if extra:
        raise SystemExit(f'Unexpected axioms for {name}: {sorted(extra)}')
if not expected:
    raise SystemExit('Empty axiom audit')
print(f'Checked {len(expected)} declarations: only standard foundational axioms.')
