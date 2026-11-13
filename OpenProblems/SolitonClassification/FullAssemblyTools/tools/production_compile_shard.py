"""Pinned, sequential Lean compilation. JSON evidence is not a mathematical proof.

Create a base lock once from the actual external libraries, then use that same
lock for every shard. Only byte-matching prior results may be reused; the final
axiom audit always runs afresh. Generated outputs never overwrite base libraries.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time

SCHEMA = 'rotating.production-shard.v1'
REPORT_SCHEMA = 'rotating.production-build.v1'
SIDE = ('', '.private', '.server')
NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z')
SHA = re.compile(r'[0-9a-f]{64}\Z')


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def atomic_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', dir=path.parent,
                                     prefix='.report-', delete=False) as stream:
        temporary = Path(stream.name)
        json.dump(value, stream, indent=2, ensure_ascii=True)
        stream.write('\n')
    temporary.replace(path)


def confined(root, relative):
    if not isinstance(relative, str):
        raise ValueError('Non-string path')
    p = PurePosixPath(relative)
    if (not relative or not re.fullmatch(r'[A-Za-z0-9_./-]+', relative)
            or p.is_absolute() or '..' in p.parts or p.as_posix() != relative):
        raise ValueError(f'Noncanonical relative path: {relative}')
    root = Path(root).resolve()
    result = (root / relative).resolve()
    if not result.is_relative_to(root):
        raise ValueError(f'Path escapes root: {relative}')
    return result


def module_file(name):
    if not NAME.fullmatch(name):
        raise ValueError(f'Invalid module name: {name}')
    return name.replace('.', '/') + '.olean'


def bundle(path):
    path = Path(path)
    if not path.is_file():
        raise FileNotFoundError(path)
    return {suffix: {'sha256': digest(Path(str(path) + suffix)),
                     'bytes': Path(str(path) + suffix).stat().st_size}
            for suffix in SIDE if Path(str(path) + suffix).is_file()}


def validate_output_tree(build, names, mirrors=None, allow_missing_mirrors=False):
    mirrors = mirrors or {}
    allowed = {module_file(name) + suffix for name in names for suffix in SIDE}
    for path in build.rglob('*'):
        if path.is_file() and ('.olean' in path.name or path.name.endswith(('.ir', '.ir.sig'))):
            relative = path.relative_to(build).as_posix()
            if relative not in allowed | mirrors.keys() or path.is_symlink() or not path.resolve().is_relative_to(build):
                raise ValueError(f'Unlisted/shadowing Lean artifact in generated build: {relative}')
            if relative in mirrors and (digest(path) != mirrors[relative]['sha256']
                                         or path.stat().st_size != mirrors[relative]['bytes']):
                raise ValueError(f'Pinned same-package mirror changed: {relative}')
    if not allow_missing_mirrors:
        for relative, expected in mirrors.items():
            target = confined(build, relative)
            if (not target.is_file() or target.stat().st_size != expected['bytes']
                    or digest(target) != expected['sha256']):
                raise ValueError(f'Pinned same-package mirror missing or changed: {relative}')


def package_mirrors(roots, lock, names):
    """Lean resolves a package directory before looking for its individual file.

    Mirror exact pinned same-package bytes into the generated build. This is
    necessary when new and external modules share a top-level namespace. No
    unlisted or modified base byte is thereby allowed into the build directory.
    """
    packages = {name.split('.')[0] for name in names}
    mirrors, origins, selected_modules = {}, {}, set()
    for label, root in roots.items():
        prefix = label + '/'
        for key, data in lock['files'].items():
            if not key.startswith(prefix) or not key.endswith('.olean'):
                continue
            relative = key[len(prefix):]
            if not any(relative.startswith(package + '/') or relative == package + '.olean'
                       for package in packages):
                continue
            if relative in selected_modules:
                continue
            selected_modules.add(relative)
            # One module, one first-hit origin. Never fill missing private/server
            # or IR parts from a later root with another version of the module.
            relatives = [relative + suffix for suffix in SIDE]
            relatives += [relative.removesuffix('.olean') + suffix for suffix in ('.ir', '.ir.sig')]
            for part in relatives:
                if prefix + part in lock['files']:
                    mirrors[part] = lock['files'][prefix + part]
                    origins[part] = confined(root, part)
    return mirrors, origins


def roots_from_args(values):
    roots = {}
    for value in values:
        label, separator, location = value.partition('=')
        if not separator or not re.fullmatch(r'[A-Za-z0-9_-]+', label) or label in roots:
            raise ValueError('Use unique --base-root LABEL=PATH arguments')
        root = Path(location).resolve()
        if not root.is_dir():
            raise NotADirectoryError(root)
        roots[label] = root
    if not roots:
        raise ValueError('At least one explicit base root is required')
    return roots


def base_snapshot(roots):
    files = {}
    for label, root in roots.items():
        for p in sorted(root.rglob('*')):
            if not p.is_file() or not ('.olean' in p.name or p.name.endswith(('.ir', '.ir.sig'))
                                       or p.suffix in ('.dll', '.so', '.dylib')):
                continue
            relative = p.relative_to(root).as_posix()
            if p.is_symlink() or not p.resolve().is_relative_to(root):
                raise ValueError(f'External library link outside lock: {p}')
            files[label + '/' + relative] = {'sha256': digest(p), 'bytes': p.stat().st_size}
    if not files:
        raise ValueError('Empty external library lock')
    return files


def lean_identity(executable):
    resolved = Path(shutil.which(executable) or executable).resolve()
    version = subprocess.check_output([str(resolved), '--version'], text=True).strip()
    runtime = {p.name: digest(p) for p in sorted(resolved.parent.iterdir())
               if p.is_file() and p.suffix in ('.dll', '.so', '.dylib')}
    return resolved, {'sha256': digest(resolved), 'version': version, 'adjacent_runtime': runtime}


def validate_manifest(m):
    if m.get('schema') != SCHEMA:
        raise ValueError('Wrong production manifest schema')
    if not re.fullmatch(r'[A-Za-z0-9_]+', m['key']):
        raise ValueError('Invalid shard key')
    if (type(m['sign']) is not int or m['sign'] not in (-1, 1)
            or type(m['start']) is not int or type(m['count']) is not int
            or m['start'] < 0 or m['count'] <= 0
            or m['start'] + m['count'] > m['total_path_steps']
            or m['total_path_steps'] != 4000 or m['orders'] != {'state': 42, 'matrix': 22}):
        raise ValueError('Invalid signed interval or polynomial orders')
    if int(m['mesh']) <= 0 or int(m['step']['num']) <= 0 or int(m['step']['den']) <= 0:
        raise ValueError('Invalid mesh or positive time step')
    modules = m['modules']
    names = [x['name'] for x in modules]
    if (not modules or len(set(names)) != len(names) or len(set(n.casefold() for n in names)) != len(names)
            or names[-1] != m['audit_module'] or m['root_module'] not in names
            or not m.get('audit_marker')):
        raise ValueError('Incomplete/duplicate module set or missing final audit')
    seen = set()
    for item in modules:
        name = item['name']
        module_file(name)
        if (not name.startswith('SolitonClassification.Rotating.')
                or item['source'] != name.replace('.', '/') + '.lean'
                or not SHA.fullmatch(item['sha256'])):
            raise ValueError(f'Invalid generated source identity: {name}')
        deps = item['imports']
        if len(set(deps)) != len(deps):
            raise ValueError('Duplicate explicit import')
        for dep in deps:
            module_file(dep)
            if dep in names and dep not in seen:
                raise ValueError(f'Not topologically ordered: {name} -> {dep}')
        seen.add(name)
    coverage = m['leaf_coverage']
    if sorted(x['global_step'] for x in coverage) != list(range(m['start'], m['start'] + m['count'])):
        raise ValueError('Missing, overlapping, or out-of-range finite leaves')
    for item in coverage:
        if any(item[field] not in seen for field in ('state_module', 'matrix_module', 'header_module')):
            raise ValueError('Coverage references an absent module')
    by_name = {item['name']: item for item in modules}
    reachable, pending = set(), [m['audit_module']]
    while pending:
        name = pending.pop()
        if name not in reachable:
            reachable.add(name)
            pending.extend(dep for dep in by_name[name]['imports'] if dep in by_name)
    if reachable != set(names):
        raise ValueError('Some generated modules are outside the fresh audit import closure')
    attachments = m.get('attachments', [])
    attachment_names = []
    for item in attachments:
        source = item['source']
        p = PurePosixPath(source)
        if (not re.fullmatch(r'[A-Za-z0-9_/-]+\.json', source) or p.is_absolute()
                or p.as_posix() != source or p.parts[0] in ('logs', 'checked_oleans')
                or source in ('manifest.json', 'compile_report.json', 'base_lock.json')
                or not SHA.fullmatch(item['sha256'])):
            raise ValueError('Invalid checkpoint attachment identity')
        attachment_names.append(source.casefold())
    if len(set(attachment_names)) != len(attachment_names):
        raise ValueError('Duplicate checkpoint attachment')
    return modules


def header_imports(source):
    # The generator emits one import per line. Remove nested Lean comments;
    # Lean --deps independently checks the actual resolved dependencies below.
    text = source.read_text(encoding='utf-8-sig')
    text = re.sub(r'--[^\n]*', '', text)
    while '/-' in text:
        shorter, count = re.subn(r'/-(?:(?!/-|-/)[\s\S])*?-/', '', text)
        if not count:
            raise ValueError('Malformed or nested-unclosed source comment')
        text = shorter
    result = []
    for line in text.splitlines():
        match = re.fullmatch(r'\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)\s*', line)
        if match:
            result.append(match.group(1))
    return result


def compile_shard(args):
    manifest_path = args.manifest.resolve()
    directory = manifest_path.parent
    report_path = directory / 'compile_report.json'
    old = json.loads(report_path.read_text()) if args.resume_verified and report_path.is_file() else {}
    report = {'schema': REPORT_SCHEMA, 'status': 'running', 'shard_kernel_checked': False, 'modules': []}
    atomic_json(report_path, report)
    try:
        m = json.loads(manifest_path.read_text(encoding='utf-8-sig'))
        modules = validate_manifest(m)
        attachments = {item['source']: item['sha256'] for item in m.get('attachments', [])}
        if any(digest(confined(directory, name)) != expected for name, expected in attachments.items()):
            raise ValueError('Checkpoint attachment changed before compilation')
        roots = roots_from_args(args.base_root)
        build = args.build_root.resolve()
        if any(build.is_relative_to(r) or r.is_relative_to(build) for r in roots.values()):
            raise ValueError('Generated output and pinned base libraries must be disjoint')
        build.mkdir(parents=True, exist_ok=True)
        names = {x['name'] for x in modules}
        if any((root / module_file(name)).exists() for root in roots.values() for name in names):
            raise ValueError('Generated module collides with a pinned external module')
        lean, identity = lean_identity(args.lean)
        automatic_lib = Path(subprocess.check_output([str(lean), '--print-libdir'], text=True).strip()).resolve()
        if not any(automatic_lib.is_relative_to(root) for root in roots.values()):
            raise ValueError('The complete automatic Lean standard library must be inside the base lock')
        lock = json.loads(args.base_lock.read_text())
        if (lock.get('schema') != 'rotating.production-base.v1'
                or lock['lean'] != identity or list(roots) != lock['root_order']
                or base_snapshot(roots) != lock['files']):
            raise ValueError('External library/toolchain fingerprint mismatch')
        mirrors, mirror_origins = package_mirrors(roots, lock, names)
        validate_output_tree(build, names, mirrors, allow_missing_mirrors=True)
        for relative, expected in mirrors.items():
            target = confined(build, relative)
            if not target.exists():
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(mirror_origins[relative], target)
            if digest(target) != expected['sha256']:
                raise ValueError(f'Same-package mirror copy differs from base lock: {relative}')
        validate_output_tree(build, names, mirrors)
        lock_hash = digest(args.base_lock)
        shutil.copyfile(args.base_lock, directory / 'base_lock.json') if args.base_lock.resolve() != directory / 'base_lock.json' else None
        env = os.environ.copy()
        search = [build, *roots.values()]
        env['LEAN_PATH'] = os.pathsep.join(map(str, search))
        env['LC_ALL'] = 'C'
        report.update(key=m['key'], manifest_sha256=digest(manifest_path), base_lock_sha256=lock_hash,
                      lean=identity, compiler_sha256=digest(__file__), modules=[],
                      attachment_sha256=attachments,
                      base_mirrors=mirrors,
                      meaning='Actual finite shard checks; no full shooting root asserted.')
        old_records = {r['name']: r for r in old.get('modules', [])}
        compatible = (old.get('manifest_sha256') == report['manifest_sha256']
                      and old.get('base_lock_sha256') == lock_hash and old.get('lean') == identity
                      and old.get('compiler_sha256') == report['compiler_sha256'])
        produced = {}

        def imports_for(item, source):
            validate_output_tree(build, names, mirrors)
            if header_imports(source) != item['imports']:
                raise ValueError(f'Header imports disagree with manifest: {item["name"]}')
            # Lean's own parser/search path is authoritative, including implicit Init.
            raw = subprocess.check_output([str(lean), '--deps', str(source)], cwd=directory,
                                          env=env, text=True, encoding='utf-8')
            actual = {Path(line.strip()).resolve() for line in raw.splitlines() if line.strip()}
            expected = {}
            for dep in ['Init', *item['imports']]:
                rel = module_file(dep)
                path = next((r / rel for r in search if (r / rel).is_file()), None)
                if path is None:
                    raise FileNotFoundError(f'Unresolved dependency {dep}')
                if dep in names:
                    if path.resolve() != (build / rel).resolve() or dep not in produced:
                        raise ValueError(f'Generated dependency is shadowed or unchecked: {dep}')
                    if bundle(path) != produced[dep]['artifacts']:
                        raise ValueError(f'Generated dependency changed: {dep}')
                else:
                    if path.resolve().is_relative_to(build):
                        expected_bundle = {suffix: mirrors[rel + suffix] for suffix in SIDE if rel + suffix in mirrors}
                        if bundle(path) != expected_bundle:
                            raise ValueError(f'Unpinned or changed mirrored dependency: {dep}')
                    else:
                        label, root = next(((label, root) for label, root in roots.items()
                                            if path.resolve().is_relative_to(root)), (None, None))
                        if root is None:
                            raise ValueError(f'Unpinned dependency: {dep}')
                        for suffix, data in bundle(path).items():
                            key = label + '/' + Path(str(path) + suffix).relative_to(root).as_posix()
                            if lock['files'].get(key) != data:
                                raise ValueError(f'Changed external import: {dep}{suffix}')
                expected[dep] = {'artifacts': bundle(path)}
            expected_paths = {next(r / module_file(dep) for r in search
                                   if (r / module_file(dep)).is_file()).resolve() for dep in expected}
            if actual != expected_paths:
                raise ValueError(f'Lean --deps differs from manifest/Init for {item["name"]}: {actual ^ expected_paths}')
            return expected

        for item in modules:
            name = item['name']
            source = confined(directory, item['source'])
            if digest(source) != item['sha256']:
                raise ValueError(f'Source changed: {name}')
            deps = imports_for(item, source)
            output = confined(build, module_file(name))
            output.parent.mkdir(parents=True, exist_ok=True)
            log = confined(directory, 'logs/' + name.replace('.', '_') + '.log')
            log.parent.mkdir(parents=True, exist_ok=True)
            prior = old_records.get(name, {}) if compatible else {}
            reusable = (args.resume_verified and name != m['audit_module']
                        and prior.get('exit_code') == 0 and prior.get('source_sha256') == item['sha256']
                        and prior.get('imports_before') == deps == prior.get('imports_after')
                        and output.is_file() and bundle(output) == prior.get('artifacts')
                        and log.is_file() and digest(log) == prior.get('log_sha256'))
            if reusable:
                record = dict(prior, reused_verified=True)
            else:
                start = time.monotonic()
                with tempfile.TemporaryDirectory(prefix='lean-', dir=directory) as tmp:
                    temporary = Path(tmp) / 'result.olean'
                    flags = subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0
                    with log.open('wb') as stream:
                        process = subprocess.Popen([str(lean), '-M', str(args.memory_mb), '-j', '1',
                                                    '-o', str(temporary), str(source)], cwd=directory,
                                                   env=env, stdout=stream, stderr=subprocess.STDOUT,
                                                   creationflags=flags)
                        try:
                            code = process.wait(timeout=args.seconds)
                        except subprocess.TimeoutExpired:
                            process.terminate()
                            try:
                                process.wait(timeout=10)
                            except subprocess.TimeoutExpired:
                                process.kill()
                                process.wait()
                            raise RuntimeError(f'Owned Lean child exceeded time budget: {name}')
                    record = dict(name=name, source_sha256=item['sha256'], exit_code=code,
                                  log=log.relative_to(directory).as_posix(), log_sha256=digest(log),
                                  wall_seconds=time.monotonic() - start, reused_verified=False,
                                  imports_before=deps)
                    if code != 0:
                        report['modules'].append(record)
                        raise RuntimeError(f'Lean failed, exit {code}: {name}; see {log}')
                    record['imports_after'] = imports_for(item, source)
                    contents = log.read_text(encoding='utf-8', errors='replace')
                    record['audit_message_seen'] = m['audit_marker'] in contents
                    if name == m['audit_module'] and not record['audit_message_seen']:
                        raise RuntimeError('Fresh final audit did not report its required marker')
                    if digest(source) != item['sha256'] or record['imports_after'] != deps:
                        raise ValueError('Source or imported artifacts changed during compilation')
                    record['artifacts'] = bundle(temporary)
                    for suffix in SIDE:
                        target = Path(str(output) + suffix)
                        if suffix in record['artifacts']:
                            Path(str(temporary) + suffix).replace(target)
                        elif target.exists():
                            # Exact stale generated sidecar, never a library or recursive path.
                            target.unlink()
            record['checked_artifacts'] = {}
            for suffix, data in record['artifacts'].items():
                relative = 'checked_oleans/' + module_file(name) + suffix
                target = confined(directory, relative)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(Path(str(output) + suffix), target)
                if digest(target) != data['sha256']:
                    raise ValueError('Artifact copy changed')
                record['checked_artifacts'][suffix] = relative
            produced[name] = record
            report['modules'].append(record)
            atomic_json(report_path, report)
            print(f'MODULE {name} EXIT 0 REUSED {reusable}', flush=True)
        if base_snapshot(roots) != lock['files'] or digest(manifest_path) != report['manifest_sha256']:
            raise ValueError('Base libraries or manifest changed during the run')
        validate_output_tree(build, names, mirrors)
        if (lean_identity(str(lean))[1] != identity or digest(__file__) != report['compiler_sha256']
                or digest(args.base_lock) != lock_hash or digest(directory / 'base_lock.json') != lock_hash):
            raise ValueError('Toolchain, compiler, or base lock changed during the run')
        if any(digest(confined(directory, name)) != expected for name, expected in attachments.items()):
            raise ValueError('Checkpoint attachment changed during compilation')
        for item in modules:
            record = produced[item['name']]
            if (digest(confined(directory, item['source'])) != item['sha256']
                    or digest(confined(directory, record['log'])) != record['log_sha256']
                    or bundle(confined(build, module_file(item['name']))) != record['artifacts']):
                raise ValueError('A completed module changed before the final checkpoint')
            for suffix, relative in record['checked_artifacts'].items():
                target = confined(directory, relative)
                if digest(target) != record['artifacts'][suffix]['sha256']:
                    raise ValueError('A staged checked artifact changed before final checkpoint')
        report.update(status='checked', shard_kernel_checked=True)
        atomic_json(report_path, report)
        print(f'SHARD_KERNEL_CHECKED=true {m["key"]}', flush=True)
    except BaseException as error:
        report.update(status='failed', shard_kernel_checked=False, failure=repr(error))
        atomic_json(report_path, report)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    lock = sub.add_parser('lock-base')
    lock.add_argument('--output', type=Path, required=True)
    run = sub.add_parser('compile')
    run.add_argument('--manifest', type=Path, required=True)
    run.add_argument('--build-root', type=Path, required=True)
    run.add_argument('--base-lock', type=Path, required=True)
    run.add_argument('--resume-verified', action='store_true')
    run.add_argument('--memory-mb', type=int, default=4096)
    run.add_argument('--seconds', type=int, default=600)
    for command in (lock, run):
        command.add_argument('--lean', default='lean')
        command.add_argument('--base-root', action='append', required=True)
    args = parser.parse_args()
    if args.mode == 'lock-base':
        roots = roots_from_args(args.base_root)
        _, identity = lean_identity(args.lean)
        atomic_json(args.output, {'schema': 'rotating.production-base.v1', 'lean': identity,
                                 'root_order': list(roots), 'files': base_snapshot(roots)})
        print(f'BASE_LOCK {digest(args.output)}', flush=True)
    else:
        if args.memory_mb <= 0 or args.seconds <= 0:
            raise ValueError('Positive resource limits required')
        compile_shard(args)


if __name__ == '__main__':
    main()
