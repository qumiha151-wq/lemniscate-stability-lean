"""Prepare a new transport-only source package; never alter ModuleProduction."""
from pathlib import Path
import argparse, json
import verify_production_tools as verifier

TOOLS = ['production_core_artifact.py', 'production_compile_shard.py', 'production_artifact.py',
         'production_environment.py', 'production_core_import_check.py',
         'verify_production_tools.py', 'prepare_production_tools.py']


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--source-dir', type=Path, required=True)
    p.add_argument('--core-project', type=Path, required=True)
    p.add_argument('--workflow', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    output = a.output.resolve()
    protected = [a.source_dir.resolve(), a.core_project.resolve()]
    if output.exists() or any(output.is_relative_to(r) or r.is_relative_to(output) for r in protected):
        raise ValueError('Require a new source-package destination outside the protected sources')
    for path in [a.output, *a.output.parents]:
        if path.is_symlink() or (hasattr(path, 'is_junction') and path.is_junction()):
            raise ValueError('Output link/junction forbidden')
    inventory = (a.core_project/'ModuleProductionSourceInventory.json').read_bytes()
    if verifier.digest(inventory) != verifier.CORE_SHA:
        raise ValueError('Wrong unchanged core source inventory')
    blobs = {'tools/'+name: (a.source_dir/name).read_bytes() for name in TOOLS}
    for name, sha in verifier.FROZEN.items():
        if verifier.digest(blobs['tools/'+name]) != sha:
            raise ValueError('Frozen helper bytes differ: '+name)
    blobs['workflow/rotating-core-transfer.yml'] = a.workflow.read_bytes()
    blobs['.gitattributes'] = b'* -text\n'
    blobs['Scope.txt'] = b'''Exact-core transfer source package

This independent ProductionTools directory leaves ModuleProduction's frozen
108-file inventory and 88 Lean sources unchanged. Four existing production
helpers are copied byte-for-byte. New wrappers and a two-job workflow compose
their actual checks; package preparation is not a new theorem or Linux run.

Job one builds the 88-module core, explicitly builds the upstream Complex.Arctan
dependency, performs a fresh private audit, captures actual Linux bytes and
archives all locked nonstdlib roots. Job two is a distinct fresh runner with the
same pinned Lean version. It obtains no Mathlib/Lake cache, restores exactly those
bytes, and performs a fresh all-private generic audit plus a real Arctan import.
The consumer uses only restored explicit LEAN_PATH roots and checks Lean's actual
resolved dependencies and the full base before/after. Output is not an import root.

The recent Linux pilot had about 6.02 GB of locked nonstdlib files, rather than
the smaller Windows library layout. Separate workers avoid keeping the original
and restored 6 GB copies on the same machine. Actual disk usage is logged; the
8 GiB complete expanded TAR limit remains enforced. No universal fit or runtime
bound is inferred from the earlier small fixture. No old 32-step numeric shard
is compiled by this workflow, and no full 8000-step result is asserted.

Actions artifacts expire after 30 days here. They are transport/test evidence,
not a claim of permanent proof-source archival storage. Later complete-proof
delivery must preserve its reproducible sources durably.

Run Python with PYTHONDONTWRITEBYTECODE=1 or -B: exact source-package verification
rejects unexpected files, including stale __pycache__ artifacts. Verify with:
  python -B tools/verify_production_tools.py --package . --project ../ModuleProduction
The included workflow is intended for .github/workflows/rotating-core-transfer.yml
without byte changes. It supports workflow_dispatch and narrowly scoped pushes
on research/remaining-open-problems affecting this workflow or ProductionTools.
It does not change the older 32-step numerical pilot's trigger paths.
'''
    records = {name: {'sha256': verifier.digest(raw), 'bytes': len(raw)} for name, raw in blobs.items()}
    manifest = {'schema': 'rotating.production-tools-source.v1', 'source_only': True,
                'core_inventory_sha256': verifier.CORE_SHA, 'frozen_tools': verifier.FROZEN,
                'workflow_sha256': verifier.digest(blobs['workflow/rotating-core-transfer.yml']),
                'files': records, 'full_certificate_proved': False,
                'linux_two_job_transfer_executed_by_packaging': False}
    output.mkdir(parents=True)
    for name, raw in blobs.items():
        path = output/verifier.relative(name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
    (output/'ProductionToolsInventory.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8')
    if ((a.core_project/'ModuleProductionSourceInventory.json').read_bytes() != inventory
            or any((a.source_dir/name).read_bytes() != blobs['tools/'+name] for name in TOOLS)
            or a.workflow.read_bytes() != blobs['workflow/rotating-core-transfer.yml']):
        raise ValueError('Source changed during preparation')
    print('PREPARED_PRODUCTION_TOOLS='+verifier.verify(output, a.core_project))


if __name__ == '__main__':
    main()
