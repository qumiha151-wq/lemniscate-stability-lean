"""Versioned one-shard public projection after full checked-archive validation.

This is byte/provenance validation, not a Lean execution. Complete original
archives are retained. An externally pinned release record is distinguished
from local tests; this offline tool never claims it contacted a remote host.
"""
from pathlib import Path
import argparse, hashlib, json, re, shutil
import production_compile_shard as compiler
import production_artifact as artifact
import plan_production_grid as planner
import stage_public_archives as stages

SCHEMA = 'rotating.public-projection.v1'
REPOSITORY = 'qumiha151-wq/lemniscate-stability-lean'
PREFIX = 'SolitonClassification.Rotating.'
RECEIPT_LIMIT = 1024*1024


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(path):
    return json.loads(Path(path).read_bytes())


def require(ok, message):
    if not ok:
        raise ValueError(message)


def helpers():
    return {Path(p).name: compiler.digest(p) for p in [__file__, compiler.__file__, artifact.__file__,
        planner.__file__, planner.arithmetic.__file__, planner.reference.__file__, stages.__file__]}


def bound_plan(path, expected_sha, revision, key):
    require(compiler.SHA.fullmatch(expected_sha) is not None, 'Invalid pinned plan digest')
    raw = Path(path).read_bytes()
    require(sha(raw) == expected_sha, 'Pinned full plan changed')
    plan = json.loads(raw)
    planner.validate_plan(plan, Path(path).resolve().parent)
    require(re.fullmatch('[0-9a-f]{40}', revision) is not None and plan['revision'] == revision,
            'Wrong source revision')
    require(plan['candidate_id'] == 'nonzero_rotation_minus56_over57'
            and plan['steps_per_sign'] == 4000 and plan['shard_size'] == 32
            and len(plan['jobs']) == 250 and plan['orders'] == {'state': 42, 'matrix': 22}
            and plan['mesh'] == str(10**60), 'Not the fixed complete production plan')
    require([(j['sign'], j['start']) for j in plan['jobs']] ==
            [(s, start) for s in (1, -1) for start in range(0, 4000, 32)], 'Wrong canonical coverage')
    found = [j for j in plan['jobs'] if j['key'] == key]
    require(len(found) == 1, 'Missing or duplicate shard key')
    return raw, plan, found[0]


def durable_record(raw, expected_sha, revision, archive_sha, archive_bytes):
    """Validate a publisher record's binding, never independently attest its origin."""
    require(expected_sha and compiler.SHA.fullmatch(expected_sha) and sha(raw) == expected_sha,
            'Unpinned durable publication record')
    record = json.loads(raw)
    require(record.get('schema') == 'rotating.durable-release-record.v1'
            and record.get('kind') == 'publisher_verified_release_asset'
            and record.get('status') == 'remote_verified'
            and record.get('repository') == REPOSITORY and record.get('revision') == revision,
            'Not a pinned publisher-verified release record')
    release, asset, verification = record['release'], record['asset'], record['verification']
    require(type(release['id']) is int and release['id'] > 0
            and type(asset['id']) is int and asset['id'] > 0
            and re.fullmatch('[A-Za-z0-9_.-]+', release['tag'])
            and re.fullmatch('[A-Za-z0-9_.-]+', asset['name']), 'Invalid release/asset identity')
    expected_url = 'https://github.com/'+REPOSITORY+'/releases/download/'+release['tag']+'/'+asset['name']
    require(asset['browser_download_url'] == expected_url and asset['state'] == 'uploaded'
            and asset['size'] == archive_bytes and asset['digest'] == 'sha256:'+archive_sha,
            'Release asset differs from the complete original archive')
    require(verification['method'] == 'GitHub REST metadata plus full redownload'
            and verification['redownload_sha256'] == archive_sha
            and verification['redownload_bytes'] == archive_bytes
            and compiler.SHA.fullmatch(verification['asset_api_sha256'])
            and compiler.SHA.fullmatch(verification['release_api_sha256'])
            and re.fullmatch(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z', verification['verified_at']),
            'Missing bound publisher redownload evidence')
    return {'kind': 'pinned_publisher_release_record', 'record_sha256': expected_sha,
            'repository': REPOSITORY, 'release_id': release['id'], 'asset_id': asset['id'],
            'remote_storage_checked_here': False,
            'meaning': 'Externally pinned publisher evidence; no network validation by this projection.'}


def check_bundle_bindings(manifest, report, endpoint_raw, plan, job, plan_path, base_sha):
    compiler.validate_manifest(manifest)
    require(report.get('schema') == compiler.REPORT_SCHEMA and report.get('status') == 'checked'
            and report.get('shard_kernel_checked') is True and report['key'] == job['key']
            and report['base_lock_sha256'] == base_sha
            and report['compiler_sha256'] == compiler.digest(compiler.__file__), 'Wrong checked compiler/core report')
    for field in ['key', 'sign', 'start', 'count', 'input_node_sha256']:
        require(manifest[field] == job[field], 'Wrong job/checkpoint binding: '+field)
    for field in ['candidate_id', 'candidate_hash', 'orders', 'mesh', 'step']:
        require(manifest[field] == plan[field], 'Wrong candidate binding: '+field)
    source_fingerprints = {('generator' if k == 'shard_generator' else k): v
                          for k, v in plan['source_fingerprints'].items() if k != 'planner'}
    require(manifest['source_fingerprints'] == source_fingerprints
            and manifest['generator_sha256'] == source_fingerprints['generator']['sha256'],
            'Wrong generated-source provenance')
    names, root = stages.expected_modules(job['key'])
    require([m['name'] for m in manifest['modules']] == names
            and [m['name'] for m in report['modules']] == names
            and manifest['module_system'] is True and manifest['root_module'] == root
            and manifest['checked_constant'] == root+'.certificate'
            and manifest['audit_module'] == names[-1], 'Missing/duplicate/reordered module interface')
    require(manifest['reset_bounds'] == {n: {'num': '1', 'den': str(10**55)} for n in ('state', 'matrix')}
            and manifest['audit_marker'] == 'Production_'+job['key']+'_audit'
            and manifest['output_node'] == 'output_node.json', 'Wrong fixed reset/audit/output interface')
    coverage = [{'global_step': job['start']+i, 'state_module': PREFIX+f'{job["key"]}L{i:04d}',
                 'matrix_module': PREFIX+f'{job["key"]}L{i:04d}',
                 'header_module': PREFIX+f'{job["key"]}B{i//8:02d}Nodes'} for i in range(32)]
    require(manifest['leaf_coverage'] == coverage, 'Wrong numerical leaf coverage')
    require(manifest['attachments'] == [{'source': 'output_node.json', 'sha256': sha(endpoint_raw)}]
            and report['attachment_sha256'] == {'output_node.json': sha(endpoint_raw)},
            'Wrong archived endpoint attachment')
    endpoint_path = compiler.confined(Path(plan_path).resolve().parent, job['output_node'])
    require(compiler.digest(endpoint_path) == job['output_node_sha256']
            and json.loads(endpoint_raw) == load(endpoint_path), 'Archived endpoint differs from full plan')
    require(all(r['exit_code'] == 0 for r in report['modules']), 'A module did not actually succeed')
    audit = report['modules'][-1]
    require(audit['reused_verified'] is False and audit['audit_message_seen'] is True,
            'Missing fresh final shard audit')
    return names, root


def verify_projection(directory, args, receipt_sha):
    directory = Path(directory).resolve()
    require((directory/'projection.json').stat().st_size <= RECEIPT_LIMIT,
            'Receipt size budget exceeded')
    receipt_raw = (directory/'projection.json').read_bytes()
    require(compiler.SHA.fullmatch(receipt_sha) and sha(receipt_raw) == receipt_sha,
            'Projection receipt differs from external pinned digest')
    require((directory/'projection.sha256').read_text().strip() == receipt_sha, 'Adjacent receipt digest differs')
    r = json.loads(receipt_raw)
    _, plan, job = bound_plan(args.plan, args.plan_sha256, args.revision, args.key)
    require(r['schema'] == SCHEMA and r['status'] == 'projected'
            and r['revision'] == args.revision and r['plan_sha256'] == args.plan_sha256
            and r['full_archive_sha256'] == args.archive_sha256
            and r['base_lock_sha256'] == args.base_lock_sha256
            and (r['key'], r['sign'], r['start'], r['count']) ==
                (job['key'], job['sign'], job['start'], 32), 'Projection external binding differs')
    require(r['actual_lean_import_checked'] is False and r['full_certificate_proved'] is False
            and r['complete_250_archives_checked'] is False
            and r['external_library_snapshot_checked'] is False
            and r['complete_original_archive_validated'] is True
            and r['original_archive_retained_in_place'] is True, 'Projection overstates verification')
    require(type(r['full_archive_bytes']) is int and r['full_archive_bytes'] > 0,
            'Invalid original archive size')
    for field in ['candidate_id', 'candidate_hash', 'orders', 'mesh', 'step']:
        require(r[field] == plan[field], 'Receipt candidate binding differs: '+field)
    require(r['input_node_sha256'] == job['input_node_sha256']
            and r['plan_output_node_sha256'] == job['output_node_sha256'],
            'Receipt checkpoint binding differs')
    require(r['helper_sha256'] == helpers(), 'Projection implementation differs')
    files = r['files']
    metadata_bytes = sum(v['bytes'] for n, v in files.items() if n.startswith('metadata/'))
    require(metadata_bytes == r['metadata_bytes']
            and metadata_bytes <= args.max_metadata_mb*1024*1024, 'Metadata size budget exceeded')
    actual = set()
    for path in directory.rglob('*'):
        require(not path.is_symlink() and not (hasattr(path, 'is_junction') and path.is_junction())
                and path.resolve().is_relative_to(directory), 'Projection link or escape')
        if path.is_file():
            actual.add(path.relative_to(directory).as_posix())
    require(actual == set(files)|{'projection.json', 'projection.sha256'}, 'Missing/extra projection member')
    for name, record in files.items():
        path = compiler.confined(directory, name)
        require(path.stat().st_size == record['bytes'] and compiler.digest(path) == record['sha256'],
                'Projection file bytes changed: '+name)
    mraw, craw, eraw = [(directory/'metadata'/name).read_bytes()
                       for name in ['manifest.json', 'compile_report.json', 'output_node.json']]
    m, report = json.loads(mraw), json.loads(craw)
    require(sha(eraw) == r['archive_output_node_sha256'], 'Receipt archived checkpoint differs')
    names, root = check_bundle_bindings(m, report, eraw, plan, job, args.plan, args.base_lock_sha256)
    require(r['modules'] == names and r['root_module'] == root and r['checked_constant'] == root+'.certificate'
            and sha(mraw) == r['manifest_sha256'] == report['manifest_sha256']
            and sha(craw) == r['compile_report_sha256'], 'Projection source/report differs')
    public_files = {name for name in files if name.startswith('public/')}
    require(public_files == {'public/'+compiler.module_file(n) for n in names}, 'Wrong public-only module set')
    expected_metadata = {'metadata/'+n for n in ['manifest.json', 'compile_report.json', 'output_node.json']}
    expected_metadata.update('metadata/'+row['log'] for row in report['modules'])
    if r['durable_binding']['kind'] != 'local_test':
        expected_metadata.add('metadata/durable_record.json')
    require(set(files) == public_files | expected_metadata, 'Extra/duplicate metadata member')
    for module in report['modules']:
        record = files['public/'+compiler.module_file(module['name'])]
        require(record == module['artifacts'][''], 'Projected primary differs from complete archive evidence')
        log = (directory/'metadata'/module['log']).read_bytes()
        require(sha(log) == module['log_sha256'], 'Projected log differs from source report')
    durable = r['durable_binding']
    if durable['kind'] == 'local_test':
        require(not args.require_durable and durable['remote_storage_checked_here'] is False
                and 'metadata/durable_record.json' not in files, 'Actual durable publisher binding is required')
    else:
        result = durable_record((directory/'metadata/durable_record.json').read_bytes(),
            args.durable_record_sha256, args.revision, args.archive_sha256, r['full_archive_bytes'])
        require(durable == result, 'Durable record identity changed')
    require(sum(files[n]['bytes'] for n in public_files) == r['public_bytes']
            and r['public_bytes'] <= args.max_public_mb*1024*1024, 'Wrong public byte count/budget')
    return r


def project(args):
    plan_raw, plan, job = bound_plan(args.plan, args.plan_sha256, args.revision, args.key)
    archive = args.archive.resolve()
    require(not args.archive.is_symlink() and archive.is_file()
            and compiler.digest(archive) == args.archive_sha256, 'Complete original archive hash differs')
    archive_bytes = archive.stat().st_size
    output = args.output.resolve()
    require(not output.exists() and not args.output.is_symlink(), 'Projection output must be new')
    require(not archive.is_relative_to(output) and not output.is_relative_to(archive.parent),
            'Projection must be outside the original archive directory')
    for path in [args.output, *args.output.parents]:
        require(not path.is_symlink() and not (hasattr(path, 'is_junction') and path.is_junction()),
                'Output path link/junction forbidden')
    frozen_helpers = helpers()
    durable_raw = args.durable_record.read_bytes() if args.durable_record else None
    if durable_raw is None:
        require(not args.require_durable and args.durable_record_sha256 is None,
                'A real pinned publisher record is required for durable mode')
        durable = {'kind': 'local_test', 'remote_storage_checked_here': False}
    else:
        durable = durable_record(durable_raw, args.durable_record_sha256, args.revision,
                                  args.archive_sha256, archive_bytes)
    output.mkdir(parents=True, exist_ok=False)
    args.owned_output = output
    stage = output/'_full_validation_stage'
    files = {}

    def copy(name, data):
        require(name not in files, 'Duplicate output member')
        target = compiler.confined(output, name)
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as stream:
            stream.write(data)
        files[name] = {'sha256': sha(data), 'bytes': len(data)}

    try:
        artifact.unpack(archive, stage, args.revision, args.max_unpacked_mb*1024*1024)
        read = lambda name: compiler.confined(stage, name).read_bytes()
        manifest, report, _, _ = artifact.validate_bundle(read)
        require(sha(read('base_lock.json')) == args.base_lock_sha256,
                'Full archive belongs to another exact core')
        names, root = check_bundle_bindings(manifest, report, read('output_node.json'),
                                           plan, job, args.plan, args.base_lock_sha256)
        for name in ['manifest.json', 'compile_report.json', 'output_node.json']:
            copy('metadata/'+name, read(name))
        if durable_raw is not None:
            copy('metadata/durable_record.json', durable_raw)
        for row in report['modules']:
            copy('public/'+compiler.module_file(row['name']), read(row['checked_artifacts']['']))
            copy('metadata/'+row['log'], read(row['log']))
        public_bytes = sum(r['bytes'] for n, r in files.items() if n.startswith('public/'))
        require(public_bytes <= args.max_public_mb*1024*1024, 'Public interface budget exceeded')
        metadata_bytes = sum(r['bytes'] for n, r in files.items() if n.startswith('metadata/'))
        require(metadata_bytes <= args.max_metadata_mb*1024*1024, 'Metadata size budget exceeded')
        receipt = {'schema': SCHEMA, 'status': 'projected', 'revision': args.revision,
                   'key': args.key, 'sign': job['sign'], 'start': job['start'], 'count': 32,
                   'candidate_id': plan['candidate_id'], 'candidate_hash': plan['candidate_hash'],
                   'orders': plan['orders'], 'mesh': plan['mesh'],
                   'step': plan['step'], 'plan_sha256': args.plan_sha256,
                   'full_archive_sha256': args.archive_sha256, 'full_archive_bytes': archive_bytes,
                   'base_lock_sha256': args.base_lock_sha256,
                   'manifest_sha256': sha(read('manifest.json')),
                   'compile_report_sha256': sha(read('compile_report.json')),
                   'input_node_sha256': job['input_node_sha256'],
                   'plan_output_node_sha256': job['output_node_sha256'],
                   'archive_output_node_sha256': sha(read('output_node.json')),
                   'root_module': root, 'checked_constant': root+'.certificate', 'modules': names,
                   'durable_binding': durable, 'files': files, 'public_bytes': public_bytes,
                   'metadata_bytes': metadata_bytes,
                   'helper_sha256': frozen_helpers, 'complete_original_archive_validated': True,
                   'original_archive_retained_in_place': True, 'actual_lean_import_checked': False,
                   'external_library_snapshot_checked': False, 'complete_250_archives_checked': False,
                   'full_certificate_proved': False}
    finally:
        if stage.exists():
            target, parent = stage.resolve(), output.resolve()
            require(target != parent and target.is_relative_to(parent)
                    and target.name == '_full_validation_stage', 'Unsafe owned scratch cleanup')
            shutil.rmtree(target)
    require(compiler.digest(archive) == args.archive_sha256 and args.plan.read_bytes() == plan_raw
            and helpers() == frozen_helpers, 'Archive/plan/tool changed during projection')
    if durable_raw is not None:
        require(args.durable_record.read_bytes() == durable_raw, 'Publisher record changed')
    bound_plan(args.plan, args.plan_sha256, args.revision, args.key)
    raw = (json.dumps(receipt, sort_keys=True, indent=2)+'\n').encode()
    require(len(raw) <= RECEIPT_LIMIT, 'Receipt size budget exceeded')
    (output/'projection.json').write_bytes(raw)
    (output/'projection.sha256').write_text(sha(raw)+'\n', encoding='ascii')
    verify_projection(output, args, sha(raw))
    print(json.dumps({'status': 'projected', 'key': args.key, 'receipt_sha256': sha(raw),
                      'public_bytes': public_bytes, 'durable_binding_kind': durable['kind'],
                      'actual_lean_import_checked': False, 'full_certificate_proved': False}), flush=True)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('mode', choices=['project', 'verify'])
    for name in ['plan', 'output']:
        p.add_argument('--'+name, type=Path, required=True)
    for name in ['plan-sha256', 'revision', 'key', 'archive-sha256', 'base-lock-sha256']:
        p.add_argument('--'+name, required=True)
    p.add_argument('--archive', type=Path)
    p.add_argument('--receipt-sha256')
    p.add_argument('--durable-record', type=Path)
    p.add_argument('--durable-record-sha256')
    p.add_argument('--require-durable', action='store_true')
    p.add_argument('--max-unpacked-mb', type=int, default=512)
    p.add_argument('--max-public-mb', type=int, default=4)
    p.add_argument('--max-metadata-mb', type=int, default=8)
    a = p.parse_args()
    require(a.max_unpacked_mb > 0 and a.max_public_mb > 0 and a.max_metadata_mb > 0,
            'Positive resource bounds required')
    require(compiler.SHA.fullmatch(a.archive_sha256) and compiler.SHA.fullmatch(a.base_lock_sha256),
            'Invalid external archive/core digest')
    if a.mode == 'project':
        require(a.archive is not None, 'Project requires the complete original archive')
        try:
            project(a)
        except BaseException as error:
            if hasattr(a, 'owned_output'):
                compiler.atomic_json(a.owned_output/'failure.json', {'status': 'failed', 'error': repr(error)})
            raise
    else:
        require(a.receipt_sha256 is not None, 'Verify requires an external pinned receipt digest')
        verify_projection(a.output, a, a.receipt_sha256)
        print('PUBLIC_PROJECTION_VERIFIED=true')


if __name__ == '__main__':
    main()
