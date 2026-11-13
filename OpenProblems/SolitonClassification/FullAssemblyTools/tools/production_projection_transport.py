"""Bounded compact transport of a separately pinned public projection.

This format is deliberately different from a complete checked shard archive.
It never substitutes public files for the original source/private proof bundle.
"""
from pathlib import Path
import argparse, hashlib, io, json, tarfile
import production_public_projection as projection
import production_core_artifact as core

compiler = projection.compiler
require = projection.require
SCHEMA = 'rotating.public-projection-transport.v1'
HEADER = 'projection-transport.json'
MAX_EXPANDED = 16*1024*1024
MAX_HEADER = 64*1024
MAX_MEMBERS = 512


def helpers():
    return {**projection.helpers(), Path(__file__).name: compiler.digest(__file__),
            Path(core.__file__).name: compiler.digest(core.__file__)}


def records_for(directory, receipt):
    result = dict(receipt['files'])
    for name in ['projection.json', 'projection.sha256']:
        path = directory/name
        result[name] = {'bytes':path.stat().st_size, 'sha256':compiler.digest(path)}
    return result


def header_check(header, args):
    require(set(header) == {'schema','revision','key','plan_sha256','base_lock_sha256',
        'full_archive_sha256','receipt_sha256','files','helper_sha256'}, 'Wrong transport header fields')
    require(header['schema'] == SCHEMA and header['revision'] == args.revision
        and header['key'] == args.key and header['plan_sha256'] == args.plan_sha256
        and header['base_lock_sha256'] == args.base_lock_sha256
        and header['full_archive_sha256'] == args.archive_sha256
        and header['receipt_sha256'] == args.receipt_sha256
        and header['helper_sha256'] == helpers(), 'Transport external binding differs')
    records = header['files']
    require(isinstance(records, dict) and len(records)*2+1 <= MAX_MEMBERS, 'Too many transport members')
    folded = set()
    for name, record in records.items():
        core.path_name(name)
        require(name.casefold() not in folded, 'Case-fold duplicate member')
        folded.add(name.casefold())
        core.validate_record(record)
    require({'projection.json','projection.sha256'} <= set(records)
        and records['projection.json']['bytes'] <= projection.RECEIPT_LIMIT
        and records['projection.json']['sha256'] == args.receipt_sha256
        and records['projection.sha256']['bytes'] in (65,66)
        and sum(r['bytes'] for r in records.values()) <= MAX_EXPANDED, 'Transport payload limits/binding differ')
    return records


def read_transport(archive, args, output=None):
    projection.artifact.validate_xz(archive, MAX_EXPANDED)
    with tarfile.open(archive, 'r|xz', tarinfo=core.bounded_tarinfo(MAX_MEMBERS, MAX_HEADER)) as tar:
        entries = iter(tar)
        member = next(entries, None)
        require(member is not None and 0 <= member.size <= MAX_HEADER, 'Missing/oversized transport header')
        core.valid_member(member, HEADER, member.size)
        raw = tar.extractfile(member).read(MAX_HEADER+1)
        require(len(raw) == member.size, 'Truncated transport header')
        header = core.strict_json(raw)
        records = header_check(header, args)
        order = ['projection.json','projection.sha256',
                 *sorted(set(records)-{'projection.json','projection.sha256'})]
        for name in order:
            member = next(entries, None)
            require(member is not None, 'Missing transport payload')
            core.valid_member(member, name, records[name]['bytes'])
            core.copy_member(tar, member, records[name], output/name if output is not None else None)
        require(next(entries, None) is None, 'Extra/duplicate transport member')
        while True:
            tail = tar.fileobj.read(1024*1024)
            if not tail:
                break
            require(not any(tail), 'Nonzero data after TAR end')
    return header


def pack(args):
    directory = core.plain_path(args.projection, 'dir')
    archive = core.fresh_path(args.archive)
    require(not archive.is_relative_to(directory), 'Transport output overlaps projection')
    before = helpers()
    receipt = projection.verify_projection(directory, args, args.receipt_sha256)
    records = records_for(directory, receipt)
    header = {'schema':SCHEMA, 'revision':args.revision, 'key':args.key,
        'plan_sha256':args.plan_sha256, 'base_lock_sha256':args.base_lock_sha256,
        'full_archive_sha256':args.archive_sha256, 'receipt_sha256':args.receipt_sha256,
        'files':records, 'helper_sha256':before}
    header_check(header, args)
    raw = core.json_bytes(header)
    require(len(raw) <= MAX_HEADER, 'Transport header too large')
    archive.parent.mkdir(parents=True, exist_ok=True)
    with archive.open('xb') as output, tarfile.open(fileobj=output, mode='w:xz', preset=6) as tar:
        info = tarfile.TarInfo(HEADER)
        info.size, info.mode, info.mtime = len(raw), 0o644, 0
        tar.addfile(info, io.BytesIO(raw))
        for name in ['projection.json','projection.sha256',
                     *sorted(set(records)-{'projection.json','projection.sha256'})]:
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.mtime = records[name]['bytes'], 0o644, 0
            reader = core.CheckedReader(directory/name)
            try:
                tar.addfile(info, reader)
            finally:
                reader.close(records[name])
    # Validate even locally generated containers; no successful receipt on failure.
    read_transport(archive, args)
    projection.verify_projection(directory, args, args.receipt_sha256)
    require(records_for(directory, receipt) == records and helpers() == before,
            'Projection or implementation changed while packing')
    result = {'schema':SCHEMA, 'status':'packed', 'archive_sha256':compiler.digest(archive),
        'archive_bytes':archive.stat().st_size, 'receipt_sha256':args.receipt_sha256,
        'key':args.key, 'actual_lean_import_checked':False, 'full_certificate_proved':False}
    print(json.dumps(result), flush=True)
    return result


def unpack(args):
    archive = core.plain_path(args.archive, 'file')
    require(compiler.SHA.fullmatch(args.transport_sha256)
        and compiler.digest(archive) == args.transport_sha256, 'Wrong compact transport digest')
    output = core.fresh_path(args.output)
    require(not archive.is_relative_to(output), 'Output overlaps input transport')
    before = helpers()
    output.mkdir(parents=True, exist_ok=False)
    header = read_transport(archive, args, output)
    receipt = projection.verify_projection(output, args, args.receipt_sha256)
    require(header['files'] == records_for(output, receipt), 'Header has extra/missing projection payload')
    require(compiler.digest(archive) == args.transport_sha256 and helpers() == before,
            'Transport or implementation changed during unpack')
    return receipt


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', choices=['pack','unpack'])
    for name in ['plan','archive']:
        p.add_argument('--'+name, type=Path, required=True)
    for name in ['plan-sha256','revision','key','archive-sha256','base-lock-sha256','receipt-sha256']:
        p.add_argument('--'+name, required=True)
    p.add_argument('--projection', type=Path)
    p.add_argument('--output', type=Path)
    p.add_argument('--transport-sha256')
    p.add_argument('--durable-record-sha256')
    p.add_argument('--require-durable', action='store_true')
    p.add_argument('--max-public-mb', type=int, default=4)
    p.add_argument('--max-metadata-mb', type=int, default=8)
    a = p.parse_args()
    if a.mode == 'pack':
        require(a.projection is not None, 'Pack requires projection')
        pack(a)
    else:
        require(a.output is not None and a.transport_sha256 is not None, 'Unpack requires output/digest')
        r = unpack(a)
        print(json.dumps({'status':'unpacked_and_verified', 'key':r['key'],
                          'actual_lean_import_checked':False, 'full_certificate_proved':False}))


if __name__ == '__main__':
    main()
