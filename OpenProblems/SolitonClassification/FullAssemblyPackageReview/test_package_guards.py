"""Synthetic package rejection checks and real import/CLI-layout observations.
No Lean, network, full250 data, or production-validator entrypoint is invoked.
"""
from pathlib import Path
import copy
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve()
FORMAL = HERE.parents[1]
PACKAGE = FORMAL / 'full_assembly_tools_package_v1'
PARTIAL = FORMAL / 'first_four_partial_metadata_package_v1'
PIN = 'e7502fbabbbf9116c1c03c783e8b07f5cbac04009356c9e5266f524895097d24'
ppin = '8b9fe4d5061e6d4d53e67e284d054e512eb4ba17304899a25e122cdda1199fc6'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_bytes())
assert sha(PACKAGE / 'FullAssemblyToolsInventory.json') == PIN
spec = importlib.util.spec_from_file_location('package_guard', PACKAGE / 'tools/verify_full_assembly_tools_package.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
scratch = HERE.parent / 'mutable_structural_fixture'
assert not scratch.exists()
shutil.copytree(PACKAGE, scratch)
index = scratch / 'FullAssemblyToolsInventory.json'
original_index = index.read_bytes()
checks = []

def reject(name, action, restore, expected, repin=False):
    action()
    pin = sha(index) if repin else PIN
    try:
        guard.verify(scratch, pin)
    except (ValueError, FileNotFoundError) as error:
        assert expected in str(error), (name, str(error))
        checks.append({'name': name, 'rejected': True, 'reason': str(error), 'scope': 'synthetic package structure'})
    else:
        raise AssertionError('Accepted invalid package: ' + name)
    finally:
        restore()
        index.write_bytes(original_index)

try:
    guard.verify(scratch, '0' * 64)
except ValueError as e:
    assert 'External inventory pin differs' in str(e)
    checks.append({'name': 'wrong_external_inventory_pin', 'rejected': True, 'reason': str(e), 'scope': 'synthetic package structure'})
else:
    raise AssertionError('Wrong inventory was accepted')

extra = scratch / 'extra.olean'
reject('extra_binary_name', lambda: extra.write_bytes(b'not a Lean artifact; rejection fixture only'), extra.unlink,
       'Missing or extra package file')
ref = scratch / 'performance/reference.py'; rbytes = ref.read_bytes()
reject('missing_sibling_arithmetic', ref.unlink, lambda: ref.write_bytes(rbytes), 'Missing or extra package file')
compiler = scratch / 'tools/production_full_assembly_compile.py'; cb = compiler.read_bytes()
reject('changed_frozen_compiler', lambda: compiler.write_bytes(cb + b'\n# synthetic changed bytes\n'), lambda: compiler.write_bytes(cb),
       'Changed package bytes')
source = next((scratch / 'uncompiled/assembly').rglob('*.lean')); sb = source.read_bytes()
reject('changed_uncompiled_source', lambda: source.write_bytes(sb + b'\n'), lambda: source.write_bytes(sb), 'Changed package bytes')

def false_scope():
    obj = read(index); obj['full_certificate_proved'] = True
    index.write_text(json.dumps(obj), encoding='utf-8')
reject('self_declared_full_proof_even_when_repinning', false_scope, lambda: None,
       'Package scope is not unexecuted tools/source', True)
refs = scratch / 'inputs/ExternalSources.json'; original_refs = refs.read_bytes()
def wrong_candidate():
    obj = read(refs); obj['candidate']['sha256'] = '0' * 64
    refs.write_text(json.dumps(obj), encoding='utf-8')
    inv = read(index)
    inv['files']['inputs/ExternalSources.json']['sha256'] = sha(refs)
    inv['files']['inputs/ExternalSources.json']['bytes'] = refs.stat().st_size
    index.write_text(json.dumps(inv), encoding='utf-8')
reject('wrong_external_candidate_even_when_repinning', wrong_candidate,
       lambda: refs.write_bytes(original_refs), 'Published candidate reference differs', True)

# Preserve exact help bytes for the packaged real command parsers. --help exits
# before the production D509 gate and therefore before any compiler action.
helps = []
env = os.environ.copy(); env.pop('PYTHONPATH', None); env['PYTHONDONTWRITEBYTECODE'] = '1'
for name in ('production_full_assembly_compile.py', 'production_full_assembly_plan.py'):
    result = subprocess.run([sys.executable, '-B', str(PACKAGE / 'tools' / name), '--help'],
                            capture_output=True, env=env, timeout=30)
    assert result.returncode == 0 and not result.stderr
    path = HERE.parent / (name + '.help.txt')
    assert not path.exists(); path.write_bytes(result.stdout)
    helps.append({'tool': name, 'returncode': 0, 'stdout_sha256': sha(path)})

# Original package and restored mutable fixture must still be byte-identical.
manifest = read(PACKAGE / 'FullAssemblyToolsInventory.json')
assert sha(index) == PIN
for n, r in manifest['files'].items():
    assert sha(PACKAGE / n) == sha(scratch / n) == r['sha256']
assert sha(PARTIAL / 'PartialEvidenceInventory.json') == ppin
partial = read(PARTIAL / 'PartialEvidenceInventory.json')
assert partial['mode'] == 'pilot' and partial['binary_artifacts_included'] is False
actual = {p.relative_to(PARTIAL).as_posix() for p in PARTIAL.rglob('*') if p.is_file()}
assert actual == set(partial['files']) | {'PartialEvidenceInventory.json'}
for n, r in partial['files'].items():
    p = PARTIAL / n
    assert sha(p) == r['sha256'] and p.stat().st_size == r['bytes']
    p.read_bytes().decode('utf-8')
    assert not n.lower().endswith(('.olean', '.private', '.server', '.xz', '.zip', '.ir', '.sig'))
result = {'schema': 'rotating.full-assembly-package-guards.v1', 'status': 'passed',
          'test_source_sha256': sha(HERE), 'inventory_sha256': PIN, 'partial_inventory_sha256': ppin,
          'structural_rejection_checks': checks, 'actual_help_calls': helps,
          'actual_layout_import_report_sha256': sha(HERE.parent / 'package_check.json'),
          'partial_text_files_checked': len(partial['files']), 'original_packages_unchanged': True,
          'new_Lean_calls': 0, 'new_network_calls': 0, 'full250_inputs_supplied': False, 'full_certificate_proved': False}
target = HERE.parent / 'guard_report.json'
assert not target.exists(); target.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'status': 'passed', 'rejections': len(checks), 'report_sha256': sha(target), 'new_Lean_calls': 0}))
