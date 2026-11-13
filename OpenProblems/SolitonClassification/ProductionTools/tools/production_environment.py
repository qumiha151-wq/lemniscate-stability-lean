"""Capture the actual Lake/Lean library environment for a strict shard run.

Run inside ``lake env`` after the isolated generic project has built. This
records inputs and their hashes; it is not a mathematical proof or a build.
No platform-specific path or previously compiled Windows artifact is reused.
"""
from pathlib import Path
import argparse
import json
import os
import re
import shutil
import subprocess

import production_compile_shard as compiler


def verify_sources(project):
    inventory_path = project / 'ModuleProductionSourceInventory.json'
    raw = inventory_path.read_bytes()
    inventory = json.loads(raw.decode('utf-8-sig'))
    if (inventory.get('schema') != 'rotating.module-production-source.v1'
            or inventory.get('source_only') is not True
            or inventory.get('generic_count') != 87
            or inventory.get('fresh_all_private_audit_count') != 1):
        raise ValueError('Unexpected source-only production inventory')
    files = inventory['files']
    for relative, expected in files.items():
        path = compiler.confined(project, relative)
        if (path.is_symlink() or path.stat().st_size != expected['bytes']
                or compiler.digest(path) != expected['sha256']):
            raise ValueError('Inventory source changed: ' + relative)
    modules = inventory['topological_modules']
    if (len(modules) != 88 or len({m['name'] for m in modules}) != 88
            or modules[-1]['name'] != 'SolitonClassification.Rotating.ModuleFullGenericAudit'):
        raise ValueError('Unexpected generic module inventory')
    seen = set()
    for module in modules:
        name = module['name']
        source = name.replace('.', '/') + '.lean'
        if (not name.startswith('SolitonClassification.Rotating.')
                or source != module['source'] or files[source]['sha256'] != module['sha256']):
            raise ValueError('Generic module source identity differs')
        imports = compiler.header_imports(project / source)
        if imports != module['imports']:
            raise ValueError('Generic imports changed')
        for imported in imports:
            if imported.startswith('SolitonClassification.') and imported not in seen:
                raise ValueError('Missing or non-topological generic dependency')
            if imported.startswith(('CentroidEscape', 'Migration', 'OpenTranslators', 'LengthGrowth')):
                raise ValueError('Another open problem is imported')
        seen.add(name)
    return raw, inventory


def discover_roots(project, prefix, lean_path, omitted=None):
    """Preserve Lake's actual first-hit order, then its implicit stdlib root."""
    generic = (project / '.lake/build/lib/lean').resolve()
    stdlib = (prefix / 'lib/lean').resolve()
    if not lean_path:
        raise ValueError('LEAN_PATH is absent: invoke this command through lake env')
    values = lean_path.split(os.pathsep)
    if any(not value for value in values):
        raise ValueError('Empty LEAN_PATH entry would introduce an implicit directory')
    paths = []
    for value in [*values, str(stdlib)]:
        path = Path(value).resolve()
        if not path.exists() and path not in (generic, stdlib):
            # Lake lists optional package build roots even when no imported
            # module required that package (for example Cli). Such a path
            # cannot contribute an artifact. Omit it from the explicit search
            # paths later passed to Lean; never create or silently search it.
            if omitted is not None and str(path) not in omitted:
                omitted.append(str(path))
            continue
        if not path.is_dir():
            raise NotADirectoryError(path)
        if path not in paths:
            paths.append(path)
    if generic not in paths:
        raise ValueError('Lake environment omits the isolated project build root')
    roots = {}
    for index, path in enumerate(paths):
        if path == generic:
            label = 'generic'
        elif path == stdlib:
            label = 'stdlib'
        else:
            label = f'env_{index:03d}'
        roots[label] = path
    return roots


def capture(args):
    project = args.project.resolve()
    output = args.output.resolve()
    original_inventory, inventory = verify_sources(project)
    helper_hashes = {str(Path(p).resolve()): compiler.digest(p)
                     for p in [__file__, compiler.__file__]}
    shim = shutil.which(args.lean) or args.lean
    prefix = Path(subprocess.check_output([str(shim), '--print-prefix'], text=True).strip()).resolve()
    executable = prefix / 'bin' / ('lean.exe' if os.name == 'nt' else 'lean')
    if not executable.is_file():
        raise FileNotFoundError('The selected Lean prefix has no actual compiler executable')
    lean, identity = compiler.lean_identity(str(executable))
    toolchain = (project / 'lean-toolchain').read_text(encoding='utf-8-sig').strip()
    if toolchain != 'leanprover/lean4:v4.33.1' or not re.search(r'\bversion 4\.33\.1\b', identity['version']):
        raise ValueError('Expected the pinned Lean 4.33.1 toolchain')
    if Path(subprocess.check_output([str(lean), '--print-prefix'], text=True).strip()).resolve() != prefix:
        raise ValueError('Shim and actual Lean executable disagree on prefix')
    environment_path = os.environ.get('LEAN_PATH', '')
    omitted = []
    roots = discover_roots(project, prefix, environment_path, omitted)
    for label, root in roots.items():
        if label != 'generic' and ((root / 'SolitonClassification').exists()
                                   or (root / 'SolitonClassification.olean').exists()):
            raise ValueError('Project namespace is shadowed by an external library root')
    for root in roots.values():
        if output.is_relative_to(root) or root.is_relative_to(output):
            raise ValueError('Evidence output must be disjoint from every locked library root')
    if output == project or (output.exists() and any(output.iterdir())):
        raise ValueError('Evidence output must be a fresh or empty directory')
    generic = roots['generic']
    expected_oleans = {compiler.module_file(m['name']) for m in inventory['topological_modules']}
    actual_oleans = {p.relative_to(generic).as_posix() for p in generic.rglob('*.olean')}
    if actual_oleans != expected_oleans:
        raise ValueError('Generic build has missing or unexpected primary modules')
    for path in generic.rglob('*'):
        for suffix in ['.private', '.server']:
            if path.name.endswith('.olean' + suffix):
                primary = path.relative_to(generic).as_posix().removesuffix(suffix)
                if primary not in expected_oleans:
                    raise ValueError('Orphan generic module sidecar: ' + str(path))
    for relative in expected_oleans:
        if set(compiler.bundle(generic / relative)) != set(compiler.SIDE):
            raise ValueError('Generic module has incomplete private/server sidecars: ' + relative)
    # Hash only after the build and fresh private audit have finished. Generated
    # shard output must subsequently use a different build root.
    snapshot = compiler.base_snapshot(roots)
    lock = {'schema': 'rotating.production-base.v1', 'lean': identity,
            'root_order': list(roots), 'files': snapshot}
    common = ['--lean', str(lean)]
    for label, path in roots.items():
        common += ['--base-root', label + '=' + str(path)]
    if verify_sources(project)[0] != original_inventory:
        raise ValueError('Source inventory changed during capture')
    if compiler.lean_identity(str(lean))[1] != identity:
        raise ValueError('Compiler changed during capture')
    if any(Path(path).exists() for path in omitted):
        raise ValueError('An omitted nonexistent search root appeared during capture')
    for path, expected in helper_hashes.items():
        if compiler.digest(path) != expected:
            raise ValueError('Environment capture code changed')
    output.mkdir(parents=True, exist_ok=True)
    compiler.atomic_json(output / 'base_args.json', common)
    compiler.atomic_json(output / 'base_lock.json', lock)
    compiler.atomic_json(output / 'environment.json', {
        'schema': 'rotating.production-environment.v1',
        'platform': os.name, 'project': str(project), 'lean_prefix': str(prefix),
        'original_lean_path': environment_path,
        'omitted_nonexistent_roots': omitted,
        'roots': {label: str(path) for label, path in roots.items()},
        'inventory_sha256': compiler.digest(project / 'ModuleProductionSourceInventory.json'),
        'helper_sha256': helper_hashes, 'lean': identity,
        'base_args_sha256': compiler.digest(output / 'base_args.json'),
        'base_lock_sha256': compiler.digest(output / 'base_lock.json'),
        'generic_modules': 88, 'locked_files': len(snapshot),
        'meaning': 'Actual environment capture only, not a new Lean compilation or theorem.'})
    print(json.dumps({'generic_modules': 88, 'locked_files': len(snapshot),
                      'base_lock_sha256': compiler.digest(output / 'base_lock.json')}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--verify-source-only', action='store_true')
    args = parser.parse_args()
    if args.verify_source_only:
        _, inventory = verify_sources(args.project.resolve())
        print(json.dumps({'source_inventory_verified': True, 'files': len(inventory['files']),
                          'compiled': False}), flush=True)
    else:
        if args.output is None:
            parser.error('--output is required for environment capture')
        capture(args)


if __name__ == '__main__':
    main()
