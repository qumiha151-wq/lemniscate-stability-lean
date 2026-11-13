"""Verify the separate unexecuted full-assembly tool/source package.

An externally pinned inventory is required. No network or Lean calls occur.
This is package validation, not D509 production validation or a full proof.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

COMPILER = 'a0e2b19e60ebefdf1b35ac162df0a5a7f9b67188b4eb26d604d0664a1186456a'
VALIDATOR = 'd50998d092942c3cb60d24632d446d9e4d4108269bc6bc1a35b3c7fc505cb0e4'
SOURCE = 'cff971bcac7ac2d83aba04596ce09e44fda1ac29'
PINS = {
    'tools/production_full_assembly_compile.py': COMPILER,
    'tools/production_full_assembly_plan.py': VALIDATOR,
    'uncompiled/assembly/assembly_manifest.json': '93675bac7479a6fdcde5c247ef21fa568f4971c5c114078a7fb5f4c976e5c492',
    'uncompiled/endpoints/endpoint_links_manifest.json': '9b559bff52f049ffe627982256f5ec2d4a732ebcc4518ba491e4d2834f26ebb0',
    'inputs/FullAssemblyDesignCensus.json': '1b445de33e2fdcb97676b22c5a50f014845c616c7bd845d880bd74f6672ce116',
}
CANDIDATE = '697b53e7bd0546a26c2dc10769a9b93c5d5082a386644d6f9ac908d53f28bb70'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    def pairs(items):
        out = {}
        for k, v in items:
            require(k not in out, 'Duplicate JSON key')
            out[k] = v
        return out
    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs)

def safe(root, name):
    p = PurePosixPath(name)
    require(isinstance(name, str) and p.as_posix() == name and not p.is_absolute()
            and all(x not in ('.', '..') for x in p.parts), 'Unsafe package path')
    target = root / name
    require(target.resolve().is_relative_to(root.resolve()), 'Package path escapes root')
    for part in (target, *target.parents):
        require(not part.is_symlink() and not (hasattr(part, 'is_junction') and part.is_junction()), 'Linked package path')
    return target

def verify(root, expected):
    root = Path(root).resolve()
    inventory = safe(root, 'FullAssemblyToolsInventory.json')
    require(re.fullmatch('[0-9a-f]{64}', expected or '') and digest(inventory) == expected, 'External inventory pin differs')
    data = read(inventory)
    require(data['schema'] == 'rotating.full-assembly-tools-package.v1'
            and data['source_revision'] == SOURCE, 'Wrong package identity')
    require(data['full250_inputs_supplied'] is False and data['full_assembly_executed'] is False
            and data['full_certificate_proved'] is False and data['cloud_workflow_included'] is False,
            'Package scope is not unexecuted tools/source')
    records = data['files']
    require(len({n.casefold() for n in records}) == len(records), 'Case-fold duplicate')
    actual = set()
    for p in root.rglob('*'):
        safe(root, p.relative_to(root).as_posix())
        if p.is_file():
            actual.add(p.relative_to(root).as_posix())
    require(actual == set(records) | {'FullAssemblyToolsInventory.json'}, 'Missing or extra package file')
    for name, wanted in records.items():
        p = safe(root, name)
        require(p.stat().st_size == wanted['bytes'] and digest(p) == wanted['sha256'], 'Changed package bytes: ' + name)
        require(not name.lower().endswith(('.olean', '.private', '.server', '.ir', '.sig', '.xz', '.zip', '.yml', '.yaml')),
                'Binary proof/archive/workflow not allowed in source package')
        p.read_bytes().decode('utf-8')
    for name, wanted in PINS.items():
        require(digest(root / name) == wanted, 'Frozen production input differs: ' + name)
    manifests = [read(root / n) for n in ('uncompiled/assembly/assembly_manifest.json',
                                         'uncompiled/endpoints/endpoint_links_manifest.json')]
    names = []
    for m, folder, count in zip(manifests, ('uncompiled/assembly', 'uncompiled/endpoints'), (499, 2)):
        require(m['kernel_checked'] is False and m['full_certificate_proved'] is False and len(m['modules']) == count,
                'Wrong uncompiled source scope/count')
        for row in m['modules']:
            require(digest(safe(root / folder, row['source'])) == row['sha256'], 'Uncompiled source differs from original manifest')
            names.append(row['name'])
    require(len(set(names)) == 501, 'Duplicate assembly module')
    refs = read(root / 'inputs/ExternalSources.json')
    candidate = refs['candidate']
    require(candidate['revision'] == 'ec3547c9456f47b5bf7c8b9d07ff07bf56ff24d9'
            and candidate['sha256'] == CANDIDATE and candidate['git_blob_sha1'] == 'e2e97b45620c6305fe22fddc44d63da417e8f1f4'
            and candidate['path'] == 'OpenProblems/SolitonClassification/ProductionPipeline/future/uncompiled/FullCandidate.lean'
            and candidate['kernel_checked'] is False, 'Published candidate reference differs')
    require(not list((root / 'uncompiled').rglob('FullCandidate.lean')), 'Already-published candidate duplicated')
    census = read(root / 'inputs/FullAssemblyDesignCensus.json')
    ordered = census['actual_assembly_sources_read_and_hashed']
    require([r['name'] for r in ordered[:-1]] == names and ordered[-1]['source_sha256'] == CANDIDATE,
            'Frozen 502-source order/candidate differs')
    tiny = read(root / 'full_assembly_compiler_tiny_v1/report.json')
    require(tiny['status'] == 'passed' and tiny['compiler_sha256'] == COMPILER and tiny['validator_sha256'] == VALIDATOR
            and tiny['actual_successful_Lean_calls'] == 5 and tiny['actual_fullgrid_Lean_calls'] == 0
            and tiny['full_certificate_proved'] is False, 'Wrong historical tiny evidence')
    # Fresh Python import only: the deployed tools/performance sibling layout is
    # exercised, and D509 checks actual origins and all12 frozen helper hashes.
    code = """import json,sys
from pathlib import Path
sys.path.insert(0,sys.argv[1])
import production_full_assembly_compile as c
v=c.load_validator();v.load_helpers()
print(json.dumps({'compiler':str(Path(c.__file__).resolve()),'validator':str(Path(v.__file__).resolve()),'tools':c.tools_now(v)},sort_keys=True))
"""
    env = os.environ.copy()
    env.pop('PYTHONPATH', None)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    result = subprocess.run([sys.executable, '-B', '-c', code, str(root / 'tools')], cwd=root,
                            env=env, capture_output=True, timeout=30)
    require(result.returncode == 0 and not result.stderr, 'Actual packaged helper imports failed: ' + result.stderr.decode(errors='replace'))
    imports = json.loads(result.stdout)
    require(Path(imports['compiler']) == root / 'tools/production_full_assembly_compile.py'
            and Path(imports['validator']) == root / 'tools/production_full_assembly_plan.py', 'Wrong actual packaged entrypoints')
    require(len(imports['tools']) == 14 and all(Path(p).is_relative_to(root) for p in imports['tools']),
            'Helper import closure escaped package')
    for p, h in imports['tools'].items():
        require(digest(p) == h, 'Imported helper changed')
    for name, wanted in records.items():
        require(digest(root / name) == wanted['sha256'], 'Package changed during import probe')
    require(digest(inventory) == expected, 'Inventory changed during verification')
    return {'schema': 'rotating.full-assembly-tools-package-check.v1', 'status': 'checked',
            'inventory_sha256': expected, 'files': len(records), 'bytes': sum(r['bytes'] for r in records.values()),
            'uncompiled_source_modules_included': 501, 'candidate_referenced_without_copy': True,
            'actual_packaged_python_imports': imports, 'new_Lean_calls': 0, 'new_network_calls': 0,
            'full250_inputs_supplied': False, 'full_certificate_proved': False}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package', type=Path, required=True)
    p.add_argument('--inventory-sha256', required=True)
    p.add_argument('--report', type=Path, required=True)
    a = p.parse_args()
    require(not a.report.exists() and not a.report.resolve().is_relative_to(a.package.resolve()), 'Fresh external report required')
    result = verify(a.package, a.inventory_sha256)
    a.report.parent.mkdir(parents=True, exist_ok=True)
    with a.report.open('x', encoding='utf-8', newline='\n') as f:
        f.write(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'status': 'checked', 'files': result['files'], 'bytes': result['bytes'],
                      'report_sha256': digest(a.report), 'new_Lean_calls': 0}))

if __name__ == '__main__':
    main()
