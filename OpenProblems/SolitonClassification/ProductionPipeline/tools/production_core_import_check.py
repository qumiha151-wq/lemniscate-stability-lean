"""Fresh all-private generic audit and Arctan import on a restored exact core.

No Lake invocation, dependency cache, numerical leaf or generic source rebuild.
The full locked base and compiler are checked before and after the two fresh Lean
source checks. Outputs never enter the library search path.
"""
from pathlib import Path
import argparse, json, os, re, subprocess, time
import production_compile_shard as compiler
import production_core_artifact as core
import production_environment as environment

AUDIT = 'SolitonClassification.Rotating.ModuleFullGenericAudit'
ARCTAN = 'Mathlib.Analysis.SpecialFunctions.Complex.Arctan'
CORE_INVENTORY_SHA = '2c252cf849e22e027ca2630b836e5227b8ff8390cf45f36a6b467db64580c924'
EXPECTED_GENERIC_DECLARATIONS = 1704
EXPECTED_PRIVATE_DECLARATIONS = 331
PROBE = '''module
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Lean.Util.CollectAxioms
#check Real.hasSum_arctan
#check Real.four_mul_arctan_inv_5_sub_arctan_inv_239
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms `Real.four_mul_arctan_inv_5_sub_arctan_inv_239) do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Arctan import contains unexpected axiom {ax}"
  logInfo "RESTORED_ARCTAN_IMPORT_CHECKED=true"
'''


def check(args):
    restored = core.plain_path(args.restored, 'dir')
    project = core.plain_path(args.project, 'dir')
    output = core.fresh_path(args.output)
    initial = {n: (restored/n).read_bytes() for n in
               ('base_args.json', 'base_lock.json', 'restore_receipt.json', 'core-metadata.json')}
    lock = core.strict_json(initial['base_lock.json'])
    core.validate_lock(lock)
    receipt = core.strict_json(initial['restore_receipt.json'])
    if (receipt.get('schema') != 'rotating.production-core-restore.v1' or receipt.get('status') != 'checked'
            or receipt['revision'] != args.revision or receipt['archive_sha256'] != args.archive_sha256
            or receipt['base_lock_sha256'] != args.base_lock_sha256
            or core.hash_bytes(initial['base_lock.json']) != args.base_lock_sha256
            or core.hash_bytes(initial['base_args.json']) != receipt['restored_base_args_sha256']
            or core.hash_bytes(initial['core-metadata.json']) != receipt['header_sha256']
            or receipt['producer_tools'] != core.frozen_tools()):
        raise ValueError('Restored receipt differs from pinned upstream inputs')
    raw_inventory, inventory = environment.verify_sources(project)
    if (core.hash_bytes(raw_inventory) != CORE_INVENTORY_SHA
            or receipt['source_inventory_sha256'] != CORE_INVENTORY_SHA
            or (restored/'metadata/source_inventory.json').read_bytes() != raw_inventory):
        raise ValueError('Source inventory differs from the unchanged core project')
    executable, locations = core.parse_source_args(initial['base_args.json'], lock['root_order'])
    roots = core.checked_roots(locations)
    lean, prefix, identity = core.actual_lean(executable)
    if (identity != lock['lean'] or roots['stdlib'] != prefix/'lib'/'lean'
            or {n: str(p) for n, p in roots.items()} != receipt['roots']):
        raise ValueError('Restored search path/compiler differs')
    core.disjoint(output, roots)
    if output == restored or restored.is_relative_to(output) or output.is_relative_to(restored):
        raise ValueError('Audit output must be separate from restored core')
    if output == project or project.is_relative_to(output) or output.is_relative_to(project):
        raise ValueError('Audit output must be separate from source project')
    expected_modules = {m['name'] for m in inventory['topological_modules']}
    actual = {p.relative_to(roots['generic']).as_posix() for p in roots['generic'].rglob('*.olean')}
    if actual != {compiler.module_file(n) for n in expected_modules}:
        raise ValueError('Restored generic primary set differs from frozen 88')
    for name in expected_modules:
        if set(compiler.bundle(roots['generic']/compiler.module_file(name))) != set(compiler.SIDE):
            raise ValueError('Missing generic private/server layer')
    if compiler.base_snapshot(roots) != lock['files']:
        raise ValueError('Whole restored base changed before audit')
    helpers = {str(Path(p).resolve()): compiler.digest(p) for p in
               [__file__, core.__file__, compiler.__file__, environment.__file__]}
    output.mkdir(parents=True, exist_ok=False)
    args.owned_output = output
    source = output/'source'
    build = output/'checked_outputs'
    logs = output/'logs'
    logs.mkdir()
    audit_raw = (project/(AUDIT.replace('.', '/')+'.lean')).read_bytes()
    inputs = [(AUDIT, audit_raw), ('RestoredArctanProbe', PROBE.encode())]
    report = {'schema': 'rotating.restored-core-import.v1', 'status': 'running',
              'revision': args.revision, 'archive_sha256': args.archive_sha256,
              'base_lock_sha256': args.base_lock_sha256, 'source_inventory_sha256': CORE_INVENTORY_SHA,
              'helper_sha256': helpers, 'modules': [], 'numerical_leaves_checked': 0,
              'full_certificate_proved': False}
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(str(p) for p in roots.values())
    env['LC_ALL'] = 'C'

    def dependencies(path):
        deps = ['Init', *compiler.header_imports(path)]
        expected = {}
        for name in deps:
            relative = compiler.module_file(name)
            label = next((n for n, r in roots.items() if (r/relative).is_file()), None)
            if label is None:
                raise ValueError('Missing restored import: '+name)
            actual_bundle = compiler.bundle(roots[label]/relative)
            locked = {suffix: lock['files'][label+'/'+relative+suffix] for suffix in compiler.SIDE
                      if label+'/'+relative+suffix in lock['files']}
            if actual_bundle != locked:
                raise ValueError('Restored import bytes differ: '+name)
            expected[name] = {'path': str(roots[label]/relative), 'artifacts': actual_bundle}
        raw = subprocess.check_output([str(lean), '--deps', str(path)], cwd=source,
                                      env=env, text=True, encoding='utf-8', timeout=60)
        found = {Path(p.strip()).resolve() for p in raw.splitlines() if p.strip()}
        if found != {Path(d['path']).resolve() for d in expected.values()}:
            raise ValueError('Lean resolved a dependency outside explicit restored roots')
        return expected

    for name, raw in inputs:
        relative = name.replace('.', '/')+'.lean'
        path = source/relative
        core.write_new(path, raw)
        before = dependencies(path)
        target = build/compiler.module_file(name)
        target.parent.mkdir(parents=True, exist_ok=True)
        log = logs/(name.split('.')[-1]+'.log')
        started = time.perf_counter()
        with log.open('xb') as stream:
            child = subprocess.Popen([str(lean), '-j', '1', '-M', str(args.memory_mb),
                '-o', str(target), relative], cwd=source, env=env, stdout=stream, stderr=subprocess.STDOUT)
            compiler.atomic_json(output/'active_child.json', {'pid': child.pid, 'module': name, 'command': child.args})
            try:
                code = child.wait(timeout=args.seconds)
            except BaseException:
                if child.poll() is None:
                    child.terminate()
                    try:
                        child.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        child.kill()
                        child.wait()
                raise
        row = {'name': name, 'exit_code': code, 'wall_seconds': time.perf_counter()-started,
               'source_sha256': core.hash_bytes(raw), 'imports_before': before,
               'log_sha256': compiler.digest(log), 'cpu_seconds': None, 'peak_memory_bytes': None}
        report['modules'].append(row)
        compiler.atomic_json(output/'report.json', report)
        if code:
            raise RuntimeError(str(log))
        text = log.read_text(encoding='utf-8')
        if name == AUDIT:
            match = re.search(r'Full generic module audit: (\d+) declarations \((\d+) private\), standard axioms only\.', text)
            if (not match or int(match[1]) != EXPECTED_GENERIC_DECLARATIONS
                    or int(match[2]) != EXPECTED_PRIVATE_DECLARATIONS):
                raise ValueError('Missing actual all-private standard-axiom audit')
            row.update(declarations=int(match[1]), private_declarations=int(match[2]))
        elif 'RESTORED_ARCTAN_IMPORT_CHECKED=true' not in text:
            raise ValueError('Missing actual Arctan import audit')
        row['imports_after'] = dependencies(path)
        if row['imports_after'] != before or path.read_bytes() != raw:
            raise ValueError('Import/source changed during fresh audit')
        row['artifacts'] = compiler.bundle(target)
        if set(row['artifacts']) != set(compiler.SIDE):
            raise ValueError('Fresh module output lacks a private/server layer')
        relatives = [compiler.module_file(name)+suffix for suffix in compiler.SIDE]
        relatives += [compiler.module_file(name).removesuffix('.olean')+suffix
                      for suffix in ('.ir', '.ir.sig')]
        row['all_outputs'] = {relative: {'sha256': compiler.digest(build/relative),
                               'bytes': (build/relative).stat().st_size}
                              for relative in relatives if (build/relative).is_file()}
    if (compiler.base_snapshot(roots) != lock['files'] or core.actual_lean(str(lean))[2] != identity
            or environment.verify_sources(project)[0] != raw_inventory
            or any((restored/n).read_bytes() != raw for n, raw in initial.items())
            or any(compiler.digest(p) != sha for p, sha in helpers.items())):
        raise ValueError('Whole base/compiler/source/receipt/helper changed during audit')
    # Close the first audit's evidence window across the second fresh Lean call.
    expected_outputs = {}
    for row in report['modules']:
        name = row['name']
        source_path = source/(name.replace('.', '/')+'.lean')
        log_path = logs/(name.split('.')[-1]+'.log')
        if (compiler.digest(source_path) != row['source_sha256']
                or compiler.digest(log_path) != row['log_sha256']
                or compiler.bundle(build/compiler.module_file(name)) != row['artifacts']
                or dependencies(source_path) != row['imports_after']):
            raise ValueError('Earlier fresh audit evidence changed')
        expected_outputs.update(row['all_outputs'])
    actual_outputs = set()
    for path in build.rglob('*'):
        core.plain_path(path)
        if path.is_file():
            actual_outputs.add(path.relative_to(build).as_posix())
    if actual_outputs != set(expected_outputs):
        raise ValueError('Missing or extra fresh Lean output')
    for relative, expected in expected_outputs.items():
        path = build/relative
        if path.stat().st_size != expected['bytes'] or compiler.digest(path) != expected['sha256']:
            raise ValueError('Fresh output bytes changed before final receipt')
    report.update(status='checked', complete_base_before_after_checked=True,
                  actual_fresh_private_audit=True, actual_arctan_import=True,
                  used_lake_or_mathlib_cache=False, output_on_library_search_path=False)
    compiler.atomic_json(output/'report.json', report)
    print('RESTORED_CORE_IMPORT_CHECKED=true', flush=True)


def main():
    p = argparse.ArgumentParser()
    for name in ('restored', 'project', 'output'):
        p.add_argument('--'+name, type=Path, required=True)
    for name in ('revision', 'archive-sha256', 'base-lock-sha256'):
        p.add_argument('--'+name, required=True)
    p.add_argument('--seconds', type=int, default=600)
    p.add_argument('--memory-mb', type=int, default=4096)
    a = p.parse_args()
    if (not core.REVISION.fullmatch(a.revision) or not compiler.SHA.fullmatch(a.archive_sha256)
            or not compiler.SHA.fullmatch(a.base_lock_sha256) or a.seconds <= 0 or a.memory_mb <= 0):
        raise ValueError('Invalid pinned identity or resource limit')
    try:
        check(a)
    except BaseException as error:
        if hasattr(a, 'owned_output'):
            path = a.owned_output/'report.json'
            report = json.loads(path.read_bytes()) if path.exists() else {
                'schema': 'rotating.restored-core-import.v1', 'modules': []}
            report.update(status='failed', failure=repr(error), full_certificate_proved=False)
            compiler.atomic_json(path, report)
        raise


if __name__ == '__main__':
    main()
