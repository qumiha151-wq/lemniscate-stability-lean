"""Hash-checked transport of a complete finite shard and its actual build evidence.

Unpacking verifies provenance, not Lean logic. A fresh downstream Lean import
and transitive axiom audit are still required. No archive is a shooting proof.
"""
from pathlib import Path
import argparse
import hashlib
import io
import json
import lzma
import tarfile
import tempfile
from production_compile_shard import (
    SCHEMA, REPORT_SCHEMA, SIDE, atomic_json, confined, digest, module_file,
    validate_manifest,
)

HEADER = 'rotating-archive.json'


def validate_xz(path, expanded_limit):
    """Require a complete single XZ stream, including footer/checksum.

    tarfile can stop at TAR EOF without reading a truncated XZ footer.
    Bound both decoder memory and streamed output; do not materialize the tar.
    """
    decoder = lzma.LZMADecompressor(format=lzma.FORMAT_XZ, memlimit=256 * 1024 * 1024)
    total = 0
    try:
        with Path(path).open('rb') as stream:
            while True:
                chunk = stream.read(1024 * 1024) if decoder.needs_input else b''
                if not chunk and decoder.needs_input:
                    raise ValueError('Truncated XZ stream: missing complete footer')
                total += len(decoder.decompress(chunk, max_length=1024 * 1024))
                if total > expanded_limit:
                    raise ValueError('XZ stream exceeds expanded-size budget')
                if decoder.eof:
                    if decoder.unused_data or stream.read(1):
                        raise ValueError('Trailing/concatenated XZ data is forbidden')
                    return
    except lzma.LZMAError as error:
        raise ValueError(f'Invalid XZ container: {error}') from error


def sha(data):
    return hashlib.sha256(data).hexdigest()


def validate_bundle(read):
    manifest_bytes = read('manifest.json')
    report_bytes = read('compile_report.json')
    lock_bytes = read('base_lock.json')
    m, r, lock = map(json.loads, (manifest_bytes, report_bytes, lock_bytes))
    modules = validate_manifest(m)
    if (r.get('schema') != REPORT_SCHEMA or r.get('status') != 'checked'
            or r.get('shard_kernel_checked') is not True or r.get('key') != m['key']
            or r.get('manifest_sha256') != sha(manifest_bytes)
            or r.get('base_lock_sha256') != sha(lock_bytes)
            or lock.get('schema') != 'rotating.production-base.v1' or lock['lean'] != r.get('lean')):
        raise ValueError('No matching completed kernel-build report and base lock')
    names = [item['name'] for item in modules]
    if [item['name'] for item in r['modules']] != names:
        raise ValueError('Incomplete or reordered build evidence')
    evidence = {item['name']: item for item in r['modules']}
    required = {'manifest.json', 'compile_report.json', 'base_lock.json'}
    attachments = {item['source']: item['sha256'] for item in m.get('attachments', [])}
    if r.get('attachment_sha256', {}) != attachments:
        raise ValueError('Checkpoint attachments differ from the build report')
    for name, expected in attachments.items():
        if sha(read(name)) != expected:
            raise ValueError(f'Checkpoint attachment bytes changed: {name}')
        required.add(name)
    external = {}
    for item in modules:
        name = item['name']
        record = evidence[name]
        if (record.get('exit_code') != 0 or record.get('source_sha256') != item['sha256']
                or record.get('imports_before') != record.get('imports_after')
                or set(record['imports_before']) != set(['Init', *item['imports']])):
            raise ValueError(f'Failed or inconsistent module evidence: {name}')
        if sha(read(item['source'])) != item['sha256'] or sha(read(record['log'])) != record['log_sha256']:
            raise ValueError(f'Source or log bytes changed: {name}')
        if '' not in record['artifacts'] or set(record['artifacts']) != set(record['checked_artifacts']):
            raise ValueError('Incomplete olean/sidecar set')
        for suffix, expected in record['artifacts'].items():
            if suffix not in SIDE:
                raise ValueError('Unknown olean sidecar')
            relative = 'checked_oleans/' + module_file(name) + suffix
            if record['checked_artifacts'][suffix] != relative:
                raise ValueError('Noncanonical checked artifact path')
            data = read(relative)
            if sha(data) != expected['sha256'] or len(data) != expected['bytes']:
                raise ValueError(f'Changed compiled artifact: {relative}')
            required.add(relative)
        for dep, expected in record['imports_before'].items():
            if dep in evidence:
                if expected['artifacts'] != evidence[dep]['artifacts']:
                    raise ValueError(f'Mixed generated versions: {name} -> {dep}')
            else:
                if dep in external and external[dep] != expected:
                    raise ValueError(f'Mixed external import versions: {dep}')
                # The same first-hit resolution as the compiler, independently
                # matched to the pinned base lock's labels and file hashes.
                relative = module_file(dep)
                label = next((label for label in lock['root_order']
                              if label + '/' + relative in lock['files']), None)
                if label is None:
                    raise ValueError(f'External dependency absent from lock: {dep}')
                locked = {suffix: lock['files'][label + '/' + relative + suffix]
                          for suffix in SIDE if label + '/' + relative + suffix in lock['files']}
                if expected['artifacts'] != locked:
                    raise ValueError(f'External import disagrees with base lock: {dep}')
                external[dep] = expected
        required.update((item['source'], record['log']))
    audit = evidence[m['audit_module']]
    if (audit.get('reused_verified') is not False or audit.get('audit_message_seen') is not True
            or m['audit_marker'].encode() not in read(audit['log'])):
        raise ValueError('Missing actual fresh final audit')
    return m, r, required, external


def pack(manifest_path, archive, revision):
    root = manifest_path.resolve().parent
    if manifest_path.name != 'manifest.json':
        raise ValueError('Canonical manifest.json filename required')
    read = lambda name: confined(root, name).read_bytes()
    m, r, files, external = validate_bundle(read)
    records = []
    archive = archive.resolve()
    archive.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=archive.parent, prefix='.rotating-', delete=False) as stream:
        temporary = Path(stream.name)
    try:
        with tarfile.open(temporary, 'w:xz', preset=6) as tar:
            for name in sorted(files):
                data = read(name)
                info = tarfile.TarInfo(name)
                info.size, info.mode, info.mtime = len(data), 0o644, 0
                tar.addfile(info, io.BytesIO(data))
                records.append({'path': name, 'bytes': len(data), 'sha256': sha(data)})
            metadata = {'schema': 'rotating.production-artifact.v1', 'revision': revision,
                        'key': m['key'], 'sign': m['sign'], 'start': m['start'], 'count': m['count'],
                        'manifest_sha256': sha(read('manifest.json')),
                        'report_sha256': sha(read('compile_report.json')),
                        'base_lock_sha256': sha(read('base_lock.json')),
                        'external_imports': external, 'files': records,
                        'full_certificate_proved': False}
            data = json.dumps(metadata, sort_keys=True).encode()
            info = tarfile.TarInfo(HEADER)
            info.size, info.mode, info.mtime = len(data), 0o644, 0
            tar.addfile(info, io.BytesIO(data))
        # Validate the bytes actually archived, closing the packer's read/write
        # race with a source or log changing after the initial preflight.
        validate_xz(temporary, sum(x['bytes'] for x in records) + 16 * 1024 * 1024)
        with tarfile.open(temporary, 'r:xz') as check:
            archived_read = lambda name: check.extractfile(name).read()
            cm, cr, needed, ce = validate_bundle(archived_read)
            if (needed != files or ce != external
                    or sha(archived_read('manifest.json')) != metadata['manifest_sha256']
                    or sha(archived_read('compile_report.json')) != metadata['report_sha256']
                    or sha(archived_read('base_lock.json')) != metadata['base_lock_sha256']):
                raise ValueError('Bundle changed while packing')
        temporary.replace(archive)
    finally:
        if temporary.exists():
            temporary.unlink()
    result = dict(archive_sha256=digest(archive), bytes=archive.stat().st_size,
                  unpacked_bytes=sum(x['bytes'] for x in records), files=len(records),
                  key=m['key'], revision=revision)
    atomic_json(Path(str(archive) + '.index.json'), result)
    print(json.dumps(result), flush=True)


def unpack(archive, output, revision, max_bytes):
    root = output.resolve()
    # Never overwrite a partly reviewed or unrelated directory.
    if root.exists() and any(root.iterdir()):
        raise ValueError('Unpack destination must be new or empty')
    root.mkdir(parents=True, exist_ok=True)
    validate_xz(archive, max_bytes + 16 * 1024 * 1024)
    with tarfile.open(archive, 'r:xz') as tar:
        members = []
        for member in tar:
            members.append(member)
            if len(members) > 10000:
                raise ValueError('Too many members for a single finite shard')
        names = [x.name for x in members]
        if (len(names) != len(set(x.casefold() for x in names)) or HEADER not in names
                or any(x.type not in (tarfile.REGTYPE, tarfile.AREGTYPE) for x in members)):
            raise ValueError('Duplicate paths, missing metadata, or nonregular archive member')
        if any(x.size < 0 for x in members) or sum(x.size for x in members) > max_bytes:
            raise ValueError('Archive exceeds configured expanded-size limit')
        for name in names:
            confined(root, name)
        if tar.getmember(HEADER).size > 16 * 1024 * 1024:
            raise ValueError('Archive metadata too large')
        metadata = json.load(tar.extractfile(HEADER))
        if metadata.get('schema') != 'rotating.production-artifact.v1' or metadata.get('revision') != revision:
            raise ValueError('Wrong schema or pinned revision')
        records = metadata['files']
        expected = {x['path'] for x in records}
        if len(expected) != len(records) or set(names) != expected | {HEADER}:
            raise ValueError('Manifest differs from archive members')
        # Stream to a private staging area. Validate the entire bundle before
        # making any of its source or compiled files visible at the destination.
        with tempfile.TemporaryDirectory(prefix='rotating-unpack-', dir=root.parent) as tmp:
            stage = Path(tmp)
            for record in records:
                name = record['path']
                member = tar.getmember(name)
                if member.size != record['bytes']:
                    raise ValueError('Changed member length')
                target = confined(stage, name)
                target.parent.mkdir(parents=True, exist_ok=True)
                with tar.extractfile(member) as source, target.open('wb') as stream:
                    while chunk := source.read(1024 * 1024):
                        stream.write(chunk)
                if digest(target) != record['sha256']:
                    raise ValueError(f'Changed member bytes: {name}')
            read = lambda name: confined(stage, name).read_bytes()
            m, r, required, external = validate_bundle(read)
            if (required != expected or (m['key'], m['sign'], m['start'], m['count']) !=
                    (metadata['key'], metadata['sign'], metadata['start'], metadata['count'])
                    or sha(read('manifest.json')) != metadata['manifest_sha256']
                    or sha(read('compile_report.json')) != metadata['report_sha256']
                    or sha(read('base_lock.json')) != metadata['base_lock_sha256']
                    or external != metadata['external_imports']):
                raise ValueError('Artifact provenance differs from validated contents')
            for name in sorted(required):
                target = confined(root, name)
                target.parent.mkdir(parents=True, exist_ok=True)
                confined(stage, name).replace(target)
    result = dict(status='transport_verified', archive_sha256=digest(archive), revision=revision,
                  key=m['key'], reimport_audit_passed=False, full_certificate_proved=False)
    atomic_json(root / 'unpack_report.json', result)
    print(json.dumps(result), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    make = sub.add_parser('pack')
    make.add_argument('--manifest', type=Path, required=True)
    restore = sub.add_parser('unpack')
    restore.add_argument('--output-root', type=Path, required=True)
    restore.add_argument('--max-unpacked-mb', type=int, default=1024)
    for command in (make, restore):
        command.add_argument('--archive', type=Path, required=True)
        command.add_argument('--revision', required=True)
    args = parser.parse_args()
    if not args.revision:
        raise ValueError('A pinned revision is required')
    if args.mode == 'pack':
        pack(args.manifest, args.archive, args.revision)
    else:
        if args.max_unpacked_mb <= 0:
            raise ValueError('Positive expanded-size limit required')
        unpack(args.archive, args.output_root, args.revision, args.max_unpacked_mb * 1024 * 1024)


if __name__ == '__main__':
    main()
