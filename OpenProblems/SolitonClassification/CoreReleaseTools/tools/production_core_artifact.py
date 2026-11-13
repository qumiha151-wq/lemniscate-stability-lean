"""Exact relocatable transport of a pinned Lean core, not a theorem checker.

Only locked non-stdlib artifacts travel. The receiving machine must independently
match the original actual compiler and complete stdlib bytes. Original absolute
paths are provenance only. Existing files/directories are never overwritten.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import io
import json
import os
import platform
import re
import stat
import subprocess
import tarfile
import tempfile
import time

import production_compile_shard as compiler
import production_artifact as artifact

SCHEMA = 'rotating.production-core-artifact.v1'
HEADER = 'core-metadata.json'
LOCK = 'metadata/base_lock.json'
ARGS = 'metadata/source_base_args.json'
INVENTORY = 'metadata/source_inventory.json'
MAX_MEMBERS = 200_000
MAX_EXPANDED = 8 * 1024**3
MAX_METADATA = 64 * 1024**2
LABEL = re.compile(r'[A-Za-z0-9_-]+\Z')
REVISION = re.compile(r'[0-9a-f]{40}\Z')


def hash_bytes(data):
    return hashlib.sha256(data).hexdigest()


def strict_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError('Duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(data.decode('utf-8-sig'), object_pairs_hook=pairs)


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=True, sort_keys=True, indent=2) + '\n').encode()


def path_name(name):
    if not isinstance(name, str):
        raise ValueError('Non-string archive path')
    p = PurePosixPath(name)
    if (not name or not re.fullmatch(r'[A-Za-z0-9_./-]+', name)
            or p.is_absolute() or any(x in ('.', '..') for x in p.parts)
            or p.as_posix() != name):
        raise ValueError('Noncanonical archive path: ' + name)
    return name


def plain_path(value, kind=None, must_exist=True):
    """Reject links/reparse points in every existing lexical path component."""
    p = Path(os.path.abspath(os.fspath(value)))
    parts = [*reversed(p.parents), p]
    for i, part in enumerate(parts):
        if not os.path.lexists(part):
            continue
        s = part.lstat()
        if stat.S_ISLNK(s.st_mode) or getattr(s, 'st_file_attributes', 0) & 0x400:
            raise ValueError('Link/reparse path component: ' + str(part))
        if i < len(parts)-1 and not stat.S_ISDIR(s.st_mode):
            raise ValueError('Nondirectory path component: ' + str(part))
    if must_exist and not p.exists():
        raise FileNotFoundError(p)
    if p.exists() and kind == 'file' and not stat.S_ISREG(p.stat().st_mode):
        raise ValueError('Not a regular file: ' + str(p))
    if p.exists() and kind == 'dir' and not p.is_dir():
        raise ValueError('Not a directory: ' + str(p))
    return p


def fresh_path(value):
    p = plain_path(value, must_exist=False)
    if os.path.lexists(p):
        raise ValueError('Destination already exists: ' + str(p))
    return p


def write_new(path, data):
    path = fresh_path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(data)


def frozen_tools():
    return {name: compiler.digest(path) for name, path in (
        ('core_tool', __file__), ('compiler', compiler.__file__), ('artifact', artifact.__file__))}


def validate_record(record):
    if (not isinstance(record, dict) or set(record) != {'bytes', 'sha256'}
            or type(record['bytes']) is not int or record['bytes'] < 0
            or not isinstance(record['sha256'], str)
            or not compiler.SHA.fullmatch(record['sha256'])):
        raise ValueError('Malformed file digest record')


def validate_lock(lock):
    if (not isinstance(lock, dict) or set(lock) != {'schema', 'root_order', 'files', 'lean'}
            or lock['schema'] != 'rotating.production-base.v1'):
        raise ValueError('Wrong core base lock schema')
    labels = lock['root_order']
    if (not isinstance(labels, list) or any(not isinstance(x, str) or not LABEL.fullmatch(x) for x in labels)
            or len({x.casefold() for x in labels}) != len(labels)
            or 'generic' not in labels or 'stdlib' not in labels):
        raise ValueError('Invalid base root order')
    if not isinstance(lock['files'], dict) or not lock['files']:
        raise ValueError('Empty/malformed base lock')
    folded = set()
    for name, record in lock['files'].items():
        path_name(name)
        label, sep, relative = name.partition('/')
        if not sep or not relative or label not in labels or name.casefold() in folded:
            raise ValueError('Duplicate or unknown locked root/path')
        folded.add(name.casefold())
        validate_record(record)
    lean = lock['lean']
    if (not isinstance(lean, dict) or set(lean) != {'sha256', 'version', 'adjacent_runtime'}
            or not compiler.SHA.fullmatch(lean['sha256']) or not isinstance(lean['version'], str)
            or not isinstance(lean['adjacent_runtime'], dict)):
        raise ValueError('Malformed compiler identity')
    for name, sha in lean['adjacent_runtime'].items():
        # Adjacent runtime names include libc++.dll on Windows. They are compared
        # as identity keys, never used as archive members or extracted paths.
        if (not isinstance(name, str) or not re.fullmatch(r'[A-Za-z0-9_.+-]+', name)
                or name in ('.', '..') or not compiler.SHA.fullmatch(sha)):
            raise ValueError('Malformed adjacent runtime identity')
    if not any(n.startswith('stdlib/') for n in lock['files']):
        raise ValueError('No stdlib identity in lock')


def parse_source_args(raw, labels):
    common = strict_json(raw)
    if not isinstance(common, list) or not all(isinstance(x, str) for x in common):
        raise ValueError('Base args must be a JSON array of strings')
    # Do not accept abbreviated, reordered, repeated --lean or unknown flags.
    if len(common) != 2 + 2*len(labels) or common[0] != '--lean':
        raise ValueError('Malformed captured base args')
    locations = {}
    for i, label in enumerate(labels):
        flag, value = common[2+2*i:4+2*i]
        found, sep, location = value.partition('=')
        if flag != '--base-root' or not sep or found != label or not location:
            raise ValueError('Captured root order differs from lock')
        locations[label] = location
    if not common[1]:
        raise ValueError('Missing compiler path')
    return common[1], locations


def actual_lean(executable):
    # A shim may select the toolchain, but identity is always the real prefix binary.
    prefix = plain_path(subprocess.check_output(
        [str(executable), '--print-prefix'], text=True).strip(), 'dir')
    candidate = plain_path(prefix/'bin'/('lean.exe' if os.name == 'nt' else 'lean'), 'file')
    lean, identity = compiler.lean_identity(str(candidate))
    if plain_path(subprocess.check_output([str(lean), '--print-prefix'], text=True).strip(), 'dir') != prefix:
        raise ValueError('Compiler prefix mismatch')
    return lean, prefix, identity


def checked_roots(locations):
    roots = {label: plain_path(value, 'dir') for label, value in locations.items()}
    values = list(roots.values())
    for i, root in enumerate(values):
        for other in values[:i]:
            if root == other or root.is_relative_to(other) or other.is_relative_to(root):
                raise ValueError('Overlapping logical library roots')
    for label, root in roots.items():
        # This also rejects links which do not happen to have a locked extension.
        for p in root.rglob('*'):
            s = p.lstat()
            if (stat.S_ISLNK(s.st_mode) or getattr(s, 'st_file_attributes', 0) & 0x400
                    or not (stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode))):
                raise ValueError('Nonregular library tree entry: ' + str(p))
        if label != 'generic' and ((root/'SolitonClassification').exists()
                                  or (root/'SolitonClassification.olean').exists()):
            raise ValueError('Competing project namespace in core')
    return roots


def disjoint(path, roots):
    if any(path == root or path.is_relative_to(root) or root.is_relative_to(path)
           for root in roots.values()):
        raise ValueError('Output overlaps a source/toolchain library root')


def derived_payload(lock, metadata):
    return {**{name: {'bytes': len(data), 'sha256': hash_bytes(data)} for name, data in metadata.items()},
            **{'roots/'+name: record for name, record in lock['files'].items()
               if not name.startswith('stdlib/')}}


def check_header(header, expected_revision, max_members, max_expanded, max_metadata):
    fields = {'schema', 'revision', 'root_order', 'files', 'lean', 'platform', 'machine',
              'producer_tools', 'base_lock_sha256', 'source_base_args_sha256',
              'source_inventory_sha256', 'full_certificate_proved'}
    if (not isinstance(header, dict) or set(header) != fields or header['schema'] != SCHEMA
            or not isinstance(header['revision'], str) or not REVISION.fullmatch(header['revision'])
            or header['revision'] != expected_revision or header['full_certificate_proved'] is not False):
        raise ValueError('Wrong core archive identity')
    files = header['files']
    if not isinstance(files, dict) or len(files)+1 > max_members:
        raise ValueError('Core member count exceeds limit')
    folded = set()
    for name, record in files.items():
        path_name(name)
        if name == HEADER or name.casefold() in folded:
            raise ValueError('Duplicate/casefold core member')
        folded.add(name.casefold())
        validate_record(record)
    if LOCK not in files or ARGS not in files or sum(x['bytes'] for x in files.values()) > max_expanded:
        raise ValueError('Missing metadata or payload budget exceeded')
    names = {name for name in files if name.startswith('metadata/')}
    if names not in ({LOCK, ARGS}, {LOCK, ARGS, INVENTORY}):
        raise ValueError('Unexpected metadata set')
    if any(not name.startswith('roots/') and name not in names for name in files):
        raise ValueError('Unexpected core path prefix')
    if sum(files[n]['bytes'] for n in names) > max_metadata:
        raise ValueError('Core metadata exceeds limit')
    if header['producer_tools'] != frozen_tools():
        raise ValueError('Core transport implementation differs')
    return files, names


def valid_member(member, name, expected_size):
    if (member.name != name or path_name(member.name) != name or not member.isfile()
            or member.type not in (tarfile.REGTYPE, tarfile.AREGTYPE) or member.sparse is not None
            or member.size != expected_size or set(member.pax_headers)-{'path'}):
        raise ValueError('Invalid or reordered core TAR member: ' + member.name)


def bounded_tarinfo(max_members, max_metadata):
    # tarfile reads PAX extension data before yielding its logical member. Bound
    # that read as well, rather than allowing an 8 GiB declared PAX allocation.
    raw_members = [0]
    extension_bytes = [0]
    class BoundedTarInfo(tarfile.TarInfo):
        def _proc_member(self, tar):
            raw_members[0] += 1
            if raw_members[0] > max_members or self.size < 0:
                raise ValueError('Raw TAR member limit exceeded')
            if self.type == tarfile.XHDTYPE:
                extension_bytes[0] += self.size
                if extension_bytes[0] > max_metadata:
                    raise ValueError('PAX metadata limit exceeded')
            elif self.type not in (tarfile.REGTYPE, tarfile.AREGTYPE):
                raise ValueError('Nonregular/unsupported raw TAR entry')
            return super()._proc_member(tar)
    return BoundedTarInfo


def copy_member(tar, member, record, target=None):
    digest = hashlib.sha256()
    size = 0
    incoming = tar.extractfile(member)
    if incoming is None:
        raise ValueError('Missing regular TAR stream')
    outgoing = None
    try:
        if target is not None:
            target = fresh_path(target)
            target.parent.mkdir(parents=True, exist_ok=True)
            outgoing = target.open('xb')
        while True:
            chunk = incoming.read(1024*1024)
            if not chunk:
                break
            digest.update(chunk)
            size += len(chunk)
            if size > record['bytes']:
                raise ValueError('TAR payload larger than recorded')
            if outgoing is not None:
                outgoing.write(chunk)
    finally:
        incoming.close()
        if outgoing is not None:
            outgoing.close()
    if size != record['bytes'] or digest.hexdigest() != record['sha256']:
        raise ValueError('Core payload byte mismatch: ' + member.name)


def read_archive(archive, revision, output=None, max_members=MAX_MEMBERS,
                 max_expanded=MAX_EXPANDED, max_metadata=MAX_METADATA,
                 metadata_only=False, xz_checked=False):
    """Stream once after full XZ/footer validation; no trusted TAR extraction."""
    if not xz_checked:
        artifact.validate_xz(archive, max_expanded)
    with tarfile.open(archive, 'r|xz', tarinfo=bounded_tarinfo(max_members, max_metadata)) as tar:
        entries = iter(tar)
        first = next(entries, None)
        if first is None or first.size < 0 or first.size > max_metadata:
            raise ValueError('Missing/oversized core header')
        valid_member(first, HEADER, first.size)
        header_bytes = tar.extractfile(first).read(max_metadata+1)
        if len(header_bytes) != first.size:
            raise ValueError('Incomplete core header')
        header = strict_json(header_bytes)
        records, metadata_names = check_header(header, revision, max_members, max_expanded, max_metadata)
        if len(header_bytes)+sum(records[n]['bytes'] for n in metadata_names) > max_metadata:
            raise ValueError('Combined core metadata limit exceeded')
        metadata = {}
        for name in [LOCK, ARGS, *([INVENTORY] if INVENTORY in metadata_names else [])]:
            member = next(entries, None)
            if member is None:
                raise ValueError('Missing core metadata')
            valid_member(member, name, records[name]['bytes'])
            data = tar.extractfile(member).read(records[name]['bytes']+1)
            if len(data) != records[name]['bytes'] or hash_bytes(data) != records[name]['sha256']:
                raise ValueError('Core metadata bytes differ')
            metadata[name] = data
        lock = strict_json(metadata[LOCK])
        validate_lock(lock)
        parse_source_args(metadata[ARGS], lock['root_order'])
        if (header['root_order'] != lock['root_order'] or header['lean'] != lock['lean']
                or header['base_lock_sha256'] != hash_bytes(metadata[LOCK])
                or header['source_base_args_sha256'] != hash_bytes(metadata[ARGS])
                or header['source_inventory_sha256'] != (hash_bytes(metadata[INVENTORY]) if INVENTORY in metadata else None)
                or records != derived_payload(lock, metadata)):
            raise ValueError('Core header disagrees with original base lock/metadata')
        if metadata_only:
            if output is not None:
                raise ValueError('Metadata preflight cannot extract files')
            return header, metadata, lock, hash_bytes(header_bytes)
        if output is not None:
            for name, data in metadata.items():
                write_new(output/name, data)
            write_new(output/HEADER, header_bytes)
            for label in lock['root_order']:
                if label != 'stdlib':
                    (output/'roots'/label).mkdir(parents=True, exist_ok=False)
        for name in sorted(n for n in records if n.startswith('roots/')):
            member = next(entries, None)
            if member is None:
                raise ValueError('Missing core payload')
            valid_member(member, name, records[name]['bytes'])
            copy_member(tar, member, records[name], output/name if output is not None else None)
        if next(entries, None) is not None:
            raise ValueError('Extra core TAR member')
        while True:
            tail = tar.fileobj.read(1024*1024)
            if not tail:
                break
            if any(tail):
                raise ValueError('Nonzero content after TAR end marker')
    return header, metadata, lock, hash_bytes(header_bytes)


class CheckedReader:
    def __init__(self, path):
        self.stream = plain_path(path, 'file').open('rb')
        self.hash = hashlib.sha256()
        self.size = 0

    def read(self, length=-1):
        chunk = self.stream.read(length)
        self.hash.update(chunk)
        self.size += len(chunk)
        return chunk

    def close(self, expected):
        extra = self.stream.read(1)
        self.stream.close()
        if extra or self.size != expected['bytes'] or self.hash.hexdigest() != expected['sha256']:
            raise ValueError('Source changed while packing')


def pack(args):
    started = time.perf_counter()
    tools_before = frozen_tools()
    revision = args.revision
    if not REVISION.fullmatch(revision):
        raise ValueError('A full 40-hex Git revision is required')
    lock_path, args_path = plain_path(args.base_lock, 'file'), plain_path(args.base_args, 'file')
    metadata = {LOCK: lock_path.read_bytes(), ARGS: args_path.read_bytes()}
    inventory_path = plain_path(args.source_inventory, 'file') if args.source_inventory else None
    if inventory_path is not None:
        metadata[INVENTORY] = inventory_path.read_bytes()
    if sum(map(len, metadata.values())) > args.max_metadata:
        raise ValueError('Metadata input exceeds limit')
    lock = strict_json(metadata[LOCK])
    validate_lock(lock)
    executable, locations = parse_source_args(metadata[ARGS], lock['root_order'])
    roots = checked_roots(locations)
    lean, prefix, identity = actual_lean(executable)
    if (roots['stdlib'] != prefix/'lib'/'lean' or identity != lock['lean']
            or compiler.base_snapshot(roots) != lock['files']):
        raise ValueError('Source core differs from its pinned compiler/base lock')
    archive = fresh_path(args.archive)
    index_path = fresh_path(str(archive)+'.index.json')
    disjoint(archive, roots)
    archive.parent.mkdir(parents=True, exist_ok=True)
    records = derived_payload(lock, metadata)
    header = {'schema': SCHEMA, 'revision': revision, 'root_order': lock['root_order'],
              'files': records, 'lean': identity, 'platform': platform.system(),
              'machine': platform.machine(), 'producer_tools': tools_before,
              'base_lock_sha256': hash_bytes(metadata[LOCK]),
              'source_base_args_sha256': hash_bytes(metadata[ARGS]),
              'source_inventory_sha256': hash_bytes(metadata[INVENTORY]) if INVENTORY in metadata else None,
              'full_certificate_proved': False}
    check_header(header, revision, args.max_members, args.max_expanded, args.max_metadata)
    head = json_bytes(header)
    if len(head)+sum(map(len, metadata.values())) > args.max_metadata:
        raise ValueError('Combined metadata limit exceeded')
    with tempfile.NamedTemporaryFile(dir=archive.parent, prefix='.core-', delete=False) as stream:
        temporary = Path(stream.name)
    try:
        with tarfile.open(temporary, 'w:xz', preset=6, format=tarfile.PAX_FORMAT) as tar:
            for name, data in [(HEADER, head), *metadata.items()]:
                info = tarfile.TarInfo(name)
                info.size, info.mode, info.mtime = len(data), 0o644, 0
                tar.addfile(info, io.BytesIO(data))
            for name in sorted(n for n in records if n.startswith('roots/')):
                label, relative = name.removeprefix('roots/').split('/', 1)
                info = tarfile.TarInfo(name)
                info.size, info.mode, info.mtime = records[name]['bytes'], 0o644, 0
                reader = CheckedReader(roots[label]/relative)
                try:
                    tar.addfile(info, reader)
                finally:
                    reader.close(records[name])
        actual_header, actual_metadata, _, head_hash = read_archive(temporary, revision, max_members=args.max_members,
            max_expanded=args.max_expanded, max_metadata=args.max_metadata)
        if actual_header != header or actual_metadata != metadata or head_hash != hash_bytes(head):
            raise ValueError('Archived metadata changed')
        if (compiler.base_snapshot(roots) != lock['files'] or actual_lean(str(lean))[2] != identity
                or lock_path.read_bytes() != metadata[LOCK] or args_path.read_bytes() != metadata[ARGS]
                or (inventory_path is not None and inventory_path.read_bytes() != metadata[INVENTORY])
                or frozen_tools() != tools_before):
            raise ValueError('Core source/compiler/tools changed during packing')
        # Exclusive regular-file creation is portable even where hard links are
        # disabled. An interrupted copy has no checked index and cannot match the
        # pinned expected hash. Existing archives are never replaced.
        packed_hash = compiler.digest(temporary)
        with temporary.open('rb') as incoming, archive.open('xb') as outgoing:
            while chunk := incoming.read(1024*1024):
                outgoing.write(chunk)
        if compiler.digest(archive) != packed_hash:
            raise ValueError('Archive publication bytes changed')
        receipt = {'schema': 'rotating.production-core-pack.v1', 'status': 'checked',
                   'archive_sha256': compiler.digest(archive), 'archive_bytes': archive.stat().st_size,
                   'revision': revision, 'header_sha256': hash_bytes(head),
                   'base_lock_sha256': header['base_lock_sha256'],
                   'source_base_args_sha256': header['source_base_args_sha256'],
                   'source_inventory_sha256': header['source_inventory_sha256'],
                   'payload_files': len(records), 'payload_bytes': sum(r['bytes'] for r in records.values()),
                   'nonstdlib_files': sum(n.startswith('roots/') for n in records),
                   'wall_seconds': time.perf_counter()-started, 'full_certificate_proved': False}
        write_new(index_path, json_bytes(receipt))
        print(json.dumps(receipt), flush=True)
    finally:
        if temporary.exists():
            temporary.unlink()


def restore(args):
    started = time.perf_counter()
    tools_before = frozen_tools()
    archive = plain_path(args.archive, 'file')
    if not compiler.SHA.fullmatch(args.sha256) or compiler.digest(archive) != args.sha256:
        raise ValueError('Core archive hash mismatch')
    if not REVISION.fullmatch(args.revision):
        raise ValueError('A full 40-hex Git revision is required')
    output = fresh_path(args.output)
    lean, prefix, identity = actual_lean(args.lean)
    stdlib = plain_path(prefix/'lib'/'lean', 'dir')
    disjoint(output, {'stdlib': stdlib})
    # Validate the single XZ stream once, then inspect its bounded metadata without
    # dereferencing archived paths. The extraction pass still hashes every payload.
    artifact.validate_xz(archive, args.max_expanded)
    header, metadata, lock, head_hash = read_archive(archive, args.revision, max_members=args.max_members,
        max_expanded=args.max_expanded, max_metadata=args.max_metadata,
        metadata_only=True, xz_checked=True)
    expected_stdlib = {n: r for n, r in lock['files'].items() if n.startswith('stdlib/')}
    if (identity != lock['lean'] or header['platform'] != platform.system()
            or header['machine'] != platform.machine()
            or compiler.base_snapshot({'stdlib': stdlib}) != expected_stdlib):
        raise ValueError('Receiving compiler/runtime/stdlib differs from captured core')
    output.mkdir(parents=True, exist_ok=False)
    again, again_metadata, again_lock, again_hash = read_archive(archive, args.revision, output,
        args.max_members, args.max_expanded, args.max_metadata, xz_checked=True)
    if again != header or again_metadata != metadata or again_lock != lock or again_hash != head_hash:
        raise ValueError('Core archive changed during restore')
    locations = {label: stdlib if label == 'stdlib' else output/'roots'/label for label in lock['root_order']}
    roots = checked_roots(locations)
    if compiler.base_snapshot(roots) != lock['files']:
        raise ValueError('Restored complete base snapshot differs')
    common = ['--lean', str(lean)]
    for label, root in roots.items():
        common += ['--base-root', label+'='+str(root)]
    write_new(output/'base_lock.json', metadata[LOCK])
    write_new(output/'base_args.json', json_bytes(common))
    # A second complete snapshot closes mutation during output/argument assembly.
    if (compiler.base_snapshot(roots) != lock['files'] or actual_lean(str(lean))[2] != identity
            or compiler.digest(archive) != args.sha256 or frozen_tools() != tools_before):
        raise ValueError('Restored core/compiler/archive/tools changed')
    receipt = {'schema': 'rotating.production-core-restore.v1', 'status': 'checked',
               'revision': args.revision, 'archive_sha256': args.sha256,
               'header_sha256': head_hash,
               'base_lock_sha256': compiler.digest(output/'base_lock.json'),
               'source_base_args_sha256': header['source_base_args_sha256'],
               'restored_base_args_sha256': compiler.digest(output/'base_args.json'),
               'source_inventory_sha256': header['source_inventory_sha256'],
               'root_order': list(roots), 'roots': {n: str(p) for n, p in roots.items()},
               'lean': identity, 'producer_tools': tools_before,
               'locked_files': len(lock['files']), 'wall_seconds': time.perf_counter()-started,
               'stdlib_before_after_checked': True, 'complete_restored_base_twice_checked': True,
               'lean_import_checked': False, 'full_certificate_proved': False}
    write_new(output/'restore_receipt.json', json_bytes(receipt))
    print(json.dumps(receipt), flush=True)


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest='command', required=True)
    p = commands.add_parser('pack')
    p.add_argument('--base-lock', type=Path, required=True)
    p.add_argument('--base-args', type=Path, required=True)
    p.add_argument('--source-inventory', type=Path)
    p.add_argument('--archive', type=Path, required=True)
    r = commands.add_parser('restore')
    r.add_argument('--archive', type=Path, required=True)
    r.add_argument('--output', type=Path, required=True)
    r.add_argument('--sha256', required=True)
    r.add_argument('--lean', required=True)
    for sub in (p, r):
        sub.add_argument('--revision', required=True)
        sub.add_argument('--max-members', type=int, default=MAX_MEMBERS)
        sub.add_argument('--max-expanded', type=int, default=MAX_EXPANDED)
        sub.add_argument('--max-metadata', type=int, default=MAX_METADATA)
    args = parser.parse_args()
    if any(getattr(args, n) <= 0 for n in ('max_members', 'max_expanded', 'max_metadata')):
        raise ValueError('Positive resource limits required')
    (pack if args.command == 'pack' else restore)(args)


if __name__ == '__main__':
    main()
