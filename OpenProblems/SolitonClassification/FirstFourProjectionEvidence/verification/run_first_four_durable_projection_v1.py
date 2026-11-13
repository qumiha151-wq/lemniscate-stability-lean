"""One actual, offline, four-shard durable projection/transport/pilot exercise.

Invokes frozen byte-only CLIs. No network, Lean, full-mode input, or overwrite.
The command ledger retains the exact argv arrays, logs and actual wall times.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve()
FORMAL = HERE.parents[1]
WORK = FORMAL.parent
PIPE = FORMAL / 'pipeline'
sys.path.insert(0, str(PIPE))
import production_projection_merge as merger

KEYS = ['RP0000', 'RP3968', 'RM0000', 'RM3968']
SOURCE = 'cff971bcac7ac2d83aba04596ce09e44fda1ac29'
PUB = '68dccd983c01e9a3222646c826c40c7efcdf035c'
PLAN_SHA = 'a62ef654ec4f2fd01d55b6dae19c28483dba137c424c3068a372c514b89559c1'
BASE_SHA = 'dcf9b162c42c30f387803fc9f395fcb1183f0e8179f5b46004782ba4bbf1f10d'
PINNED = {
    'production_public_projection.py': 'b206b8a43a3e1b9a47a31ab33b038ca2ac351a461b810d9265f183019c56708d',
    'production_projection_transport.py': '784bf78a8cf0d0be458553f4ed82eb9b096d36681fcda2622e152fd92f5adf34',
    'production_projection_merge.py': 'b0508cb0168b01077f2d90bc341daeca756cb6c3b43aec3c7ebbf2013c5f5625',
}
PLAN = FORMAL / 'production_pipeline_package_v1/plan/plan.json'
BASE = WORK / 'first_production_v3_publication/first_three_downloads/RP0000/restored/base_lock.json'
RECORDS = WORK / 'first_four_release_execution_publication/downloaded_evidence/unpacked/publication/journal/records'
OUT = FORMAL / 'first_four_durable_projection_v1'

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def read(path):
    return json.loads(Path(path).read_bytes())

def write_new(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x', encoding='utf-8', newline='\n') as f:
        f.write(json.dumps(obj, indent=2, sort_keys=True) + '\n')

def tree(path):
    return {p.relative_to(path).as_posix(): {'bytes': p.stat().st_size, 'sha256': sha(p)}
            for p in path.rglob('*') if p.is_file()}

assert not OUT.exists(), 'New exercise output required; do not overwrite/retry in place.'
for name, digest in PINNED.items():
    assert sha(PIPE / name) == digest
assert sha(PLAN) == PLAN_SHA and sha(BASE) == BASE_SHA
review_path = HERE.with_name('FirstFourActualReleaseIndependentReplay.json')
assert sha(review_path) == '595037fa02fa86c1b6eb858c12b8028cae5bf6a32dfe58b8869f9785d12081ef'
review = read(review_path)
assert review['status'] == 'checked' and [r['key'] for r in review['records']] == KEYS
plan = read(PLAN)
jobs = {j['key']: j for j in plan['jobs']}
frozen_helpers = merger.helpers()
input_pins = {str(PLAN): PLAN_SHA, str(BASE): BASE_SHA, str(HERE): sha(HERE), str(review_path): sha(review_path)}
for row in review['records']:
    input_pins[row['original_archive']] = row['archive_sha256']
    input_pins[str(RECORDS / (row['key'] + '.json'))] = row['record_sha256']
for path, digest in input_pins.items():
    assert sha(path) == digest
free = shutil.disk_usage(OUT.parent).free
assert free >= 2 * 1024**3 + 512 * 1024**2 + 256 * 1024**2
OUT.mkdir()
(OUT / 'logs').mkdir()
write_new(OUT / 'input_pins.json', {
    'publication_revision': PUB, 'publication_inventory_sha256': 'df6b38b12afbde0e18e916dff2349b61f8ddda2aa1623b3d075163df46d1ccb7',
    'publication_remote_verification_performed_here': False,
    'source_revision': SOURCE, 'input_sha256': input_pins, 'helper_sha256': frozen_helpers,
    'disk_free_before': free, 'mode': 'pilot', 'keys': KEYS,
    'new_network_calls': 0, 'new_Lean_calls': 0, 'full_certificate_proved': False})
commands = []
started = time.perf_counter()

def call(name, *args):
    index = len(commands)
    argv = [sys.executable, '-B', str(PIPE / name), *map(str, args)]
    row = {'index': index, 'argv': argv, 'stdout': f'logs/{index:02d}.stdout.txt',
           'stderr': f'logs/{index:02d}.stderr.txt'}
    write_new(OUT / 'logs' / f'{index:02d}.argv.json', argv)
    t = time.perf_counter()
    with (OUT / row['stdout']).open('xb') as out, (OUT / row['stderr']).open('xb') as err:
        result = subprocess.run(argv, stdout=out, stderr=err, timeout=180, check=False)
    row.update(returncode=result.returncode, wall_seconds=time.perf_counter() - t,
               stdout_sha256=sha(OUT / row['stdout']), stderr_sha256=sha(OUT / row['stderr']))
    commands.append(row)
    write_new(OUT / 'logs' / f'{index:02d}.result.json', row)
    print(json.dumps({'command': index, 'tool': name, 'mode': args[0] if args else None,
                      'returncode': result.returncode, 'wall_seconds': row['wall_seconds']}), flush=True)
    if result.returncode != 0:
        raise RuntimeError(f'Frozen CLI failed; see retained logs/{index:02d}.stderr.txt')

rows = []
try:
    for item in review['records']:
        key = item['key']
        projection = OUT / 'projections' / key
        transport = OUT / 'transports' / (key + '.public.tar.xz')
        unpacked = OUT / 'unpacked' / key
        common = ['--plan', PLAN, '--plan-sha256', PLAN_SHA, '--revision', SOURCE, '--key', key,
                  '--archive-sha256', item['archive_sha256'], '--base-lock-sha256', BASE_SHA]
        durable = ['--durable-record-sha256', item['record_sha256'], '--require-durable']
        caps = ['--max-public-mb', '4', '--max-metadata-mb', '8']
        call('production_public_projection.py', 'project', *common,
             '--archive', item['original_archive'], '--output', projection,
             '--durable-record', RECORDS / (key + '.json'), *durable,
             '--max-unpacked-mb', '512', *caps)
        receipt_path = projection / 'projection.json'
        receipt_sha = sha(receipt_path)
        receipt = read(receipt_path)
        assert receipt['durable_binding']['kind'] == 'pinned_publisher_release_record'
        assert receipt['durable_binding']['record_sha256'] == item['record_sha256']
        assert receipt['actual_lean_import_checked'] is False and receipt['complete_250_archives_checked'] is False
        call('production_public_projection.py', 'verify', *common, '--output', projection,
             '--receipt-sha256', receipt_sha, *durable, *caps)
        call('production_projection_transport.py', 'pack', *common, '--projection', projection,
             '--archive', transport, '--receipt-sha256', receipt_sha, *durable, *caps)
        transport_sha = sha(transport)
        call('production_projection_transport.py', 'unpack', *common, '--archive', transport,
             '--output', unpacked, '--transport-sha256', transport_sha,
             '--receipt-sha256', receipt_sha, *durable, *caps)
        assert tree(projection) == tree(unpacked), 'Independent unpack differs from original projection.'
        assert len(list((projection / 'public').rglob('*.olean'))) == 47
        row = {field: jobs[key][field] for field in ('key', 'sign', 'start', 'count', 'input_node_sha256', 'output_node_sha256')}
        row.update(full_archive_sha256=item['archive_sha256'], full_archive_bytes=item['archive_bytes'],
                   receipt_sha256=receipt_sha, durable_record_sha256=item['record_sha256'],
                   transport_file=transport.name, transport_sha256=transport_sha,
                   transport_bytes=transport.stat().st_size, public_bytes=receipt['public_bytes'],
                   metadata_bytes=receipt['metadata_bytes'], receipt_bytes=receipt_path.stat().st_size)
        rows.append(row)
    ledger = {'schema': merger.SCHEMA, 'mode': 'pilot', 'source_revision': SOURCE,
              'publication_revision': PUB, 'plan_sha256': PLAN_SHA, 'base_lock_sha256': BASE_SHA,
              **{field: plan[field] for field in ('candidate_id', 'candidate_hash', 'orders', 'mesh', 'step')},
              'jobs': rows, 'projection_helper_sha256': merger.p.helpers(),
              'transport_helper_sha256': merger.transport.helpers()}
    merger.validate_ledger(ledger, plan, 'pilot')
    write_new(OUT / 'ledger.json', ledger)
    ledger_sha = sha(OUT / 'ledger.json')
    call('production_projection_merge.py', '--ledger', OUT / 'ledger.json', '--plan', PLAN,
         '--base-lock', BASE, '--archive-root', OUT / 'transports', '--output', OUT / 'merged',
         '--ledger-sha256', ledger_sha, '--plan-sha256', PLAN_SHA, '--base-lock-sha256', BASE_SHA,
         '--revision', SOURCE, '--mode', 'pilot', '--reserve-bytes', str(2 * 1024**3))
    merged = read(OUT / 'merged/merge_receipt.json')
    assert merged['mode'] == 'pilot' and len(merged['modules']) == 188
    for flag in ('all_250_projections_validated', 'actual_lean_import_checked',
                 'external_library_snapshot_checked', 'inter_shard_seams_proved', 'full_certificate_proved',
                 'original_archives_deleted'):
        assert merged[flag] is False
    files = tree(OUT / 'merged')
    assert set(files) == set(merged['files']) | {'merge_receipt.json', 'merge_receipt.sha256'}
    assert {n: files[n] for n in merged['files']} == merged['files']
    for item in review['records']:
        p = OUT / 'merged/evidence' / item['key'] / 'metadata/durable_record.json'
        assert sha(p) == item['record_sha256']
        rec = read(p)
        assert rec['test_fixture'] is False and rec['release']['draft'] is False
        assert rec['release']['id'] == 443812088 and rec['release']['published_at']
    for path, digest in input_pins.items():
        assert sha(path) == digest
    assert merger.helpers() == frozen_helpers
    report = {'schema': 'rotating.first-four-durable-projection-exercise.v1', 'status': 'checked',
              'publication_revision': PUB, 'source_revision': SOURCE, 'mode': 'pilot',
              'ledger_sha256': ledger_sha, 'merge_receipt_sha256': sha(OUT / 'merged/merge_receipt.json'),
              'input_pins_sha256': sha(OUT / 'input_pins.json'), 'jobs': rows, 'commands': commands,
              'full_original_archive_validation_replayed': True,
              'independent_unpack_files_exact': True, 'all_four_durable_records_required_and_checked': True,
              'originals_retained_and_rehashed': True, 'helper_closure_unchanged': True,
              'merged_primary_modules': 188, 'wall_seconds': time.perf_counter() - started,
              'disk_free_after': shutil.disk_usage(OUT).free,
              'new_Lean_calls': 0, 'new_network_calls': 0, 'new_GitHub_writes': 0,
              'windows_byte_only_staging': True, 'Linux_olean_import_here': False,
              'all250_checked': False, 'full_certificate_proved': False}
    write_new(OUT / 'report.json', report)
    print(json.dumps({'status': 'checked', 'report_sha256': sha(OUT / 'report.json'),
                      'ledger_sha256': ledger_sha, 'merge_receipt_sha256': report['merge_receipt_sha256'],
                      'wall_seconds': report['wall_seconds'], 'modules': 188}), flush=True)
except BaseException as error:
    write_new(OUT / 'failure.json', {'status': 'failed', 'error': str(error), 'commands': commands,
                                   'new_Lean_calls': 0, 'full_certificate_proved': False})
    raise
