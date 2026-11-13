"""Separate terminal check of the actual four-shard offline exercise.

Rehash every retained argv/result/stdout/stderr, all receipts/outputs, tools,
original inputs and independent unpacks; do not rerun a frozen CLI or Lean.
"""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve()
FORMAL = HERE.parents[1]
ROOT = FORMAL / 'first_four_durable_projection_v1'
sys.path.insert(0, str(FORMAL / 'pipeline'))
import production_projection_merge as merger

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def read(p):
    return json.loads(Path(p).read_bytes())

def tree(path):
    return {p.relative_to(path).as_posix(): {'bytes': p.stat().st_size, 'sha256': sha(p)}
            for p in path.rglob('*') if p.is_file()}

def write_new(path, obj):
    with path.open('x', encoding='utf-8', newline='\n') as f:
        f.write(json.dumps(obj, sort_keys=True, indent=2) + '\n')

assert sha(ROOT / 'report.json') == 'fc407d79793f58507afea955bf1872ae32545e7f5da48aa8585a34457db84fae'
assert sha(ROOT / 'ledger.json') == '3a5bcd8afa315695fe9d7762ff3108419c019e432e53c03c703c5890f1e71878'
assert sha(ROOT / 'merged/merge_receipt.json') == '6bc2b941ef3b9d1173173ed1b2cb4d9c6d39832150e2257aac803e6ec1ed4373'
report, ledger = read(ROOT / 'report.json'), read(ROOT / 'ledger.json')
assert report['status'] == 'checked' and report['mode'] == ledger['mode'] == 'pilot'
assert report['publication_revision'] == ledger['publication_revision'] == '68dccd983c01e9a3222646c826c40c7efcdf035c'
pins = read(ROOT / 'input_pins.json')
assert report['input_pins_sha256'] == sha(ROOT / 'input_pins.json')
for path, digest in pins['input_sha256'].items():
    assert sha(path) == digest
assert pins['helper_sha256'] == merger.helpers()

expected_logs = set()
assert len(report['commands']) == 17
for i, row in enumerate(report['commands']):
    assert row['index'] == i and row['returncode'] == 0 and row['wall_seconds'] > 0
    argv, result = ROOT / 'logs' / f'{i:02d}.argv.json', ROOT / 'logs' / f'{i:02d}.result.json'
    assert read(argv) == row['argv'] and read(result) == row
    assert sha(ROOT / row['stdout']) == row['stdout_sha256']
    assert sha(ROOT / row['stderr']) == row['stderr_sha256']
    assert (ROOT / row['stderr']).stat().st_size == 0
    assert row['argv'][1] == '-B'
    if i < 16:
        assert '--require-durable' in row['argv']
    else:
        assert row['argv'][row['argv'].index('--mode') + 1] == 'pilot'
    expected_logs.update({f'{i:02d}.argv.json', f'{i:02d}.result.json', f'{i:02d}.stdout.txt', f'{i:02d}.stderr.txt'})
assert {p.name for p in (ROOT / 'logs').iterdir()} == expected_logs

expected_public = {}
for row in ledger['jobs']:
    key = row['key']
    projected, unpacked = ROOT / 'projections' / key, ROOT / 'unpacked' / key
    assert tree(projected) == tree(unpacked)
    receipt = read(projected / 'projection.json')
    assert sha(projected / 'projection.json') == row['receipt_sha256']
    assert (projected / 'projection.sha256').read_text().strip() == row['receipt_sha256']
    assert receipt['complete_original_archive_validated'] is True
    assert receipt['durable_binding']['record_sha256'] == row['durable_record_sha256']
    assert receipt['actual_lean_import_checked'] is False and receipt['complete_250_archives_checked'] is False
    files = tree(projected)
    assert set(files) == set(receipt['files']) | {'projection.json', 'projection.sha256'}
    assert {n: files[n] for n in receipt['files']} == receipt['files']
    assert sha(ROOT / 'transports' / row['transport_file']) == row['transport_sha256']
    assert (ROOT / 'transports' / row['transport_file']).stat().st_size == row['transport_bytes']
    rec = read(projected / 'metadata/durable_record.json')
    assert sha(projected / 'metadata/durable_record.json') == row['durable_record_sha256']
    assert rec['status'] == 'remote_verified' and rec['test_fixture'] is False
    assert rec['release']['id'] == 443812088 and rec['release']['draft'] is False
    assert rec['release']['published_at'] == '2026-11-13T04:23:05Z'
    for name, value in receipt['files'].items():
        if name.startswith('public/'):
            assert name not in expected_public and name.endswith('.olean')
            expected_public[name] = value
        else:
            target = ROOT / 'merged/evidence' / key / name
            assert sha(target) == value['sha256'] and target.stat().st_size == value['bytes']

merged = read(ROOT / 'merged/merge_receipt.json')
assert len(expected_public) == len(merged['modules']) == 188
assert {'public/' + n: v for n, v in tree(ROOT / 'merged/public').items()} == expected_public
merged_files = tree(ROOT / 'merged')
assert set(merged_files) == set(merged['files']) | {'merge_receipt.json', 'merge_receipt.sha256'}
assert {n: merged_files[n] for n in merged['files']} == merged['files']
for field in ['all_250_projections_validated', 'actual_lean_import_checked', 'external_library_snapshot_checked',
              'inter_shard_seams_proved', 'full_certificate_proved', 'original_archives_deleted']:
    assert merged[field] is False
assert not any(p.name.endswith(('.olean.private', '.olean.server', '.ir', '.ir.sig'))
               for p in (ROOT / 'merged/public').rglob('*'))

# The manifest is an external pin for all existing exercise files. It does not
# self-reference itself or this postcheck result, which are separately hashed.
inventory = {'schema': 'rotating.first-four-durable-exercise-files.v1', 'files': tree(ROOT),
             'scope': 'four real durable projections; pilot byte-only merge',
             'new_Lean_calls': 0, 'full_certificate_proved': False}
write_new(ROOT / 'CheckedFilesManifest.json', inventory)
result = {'schema': 'rotating.first-four-durable-postcheck.v1', 'status': 'checked',
          'script_sha256': sha(HERE), 'commands_rehashed': 17, 'original_inputs_rehashed': len(pins['input_sha256']),
          'inventory_sha256': sha(ROOT / 'CheckedFilesManifest.json'),
          'inventory_files': len(inventory['files']), 'inventory_bytes': sum(v['bytes'] for v in inventory['files'].values()),
          'merged_primary_modules': 188, 'all_four_actual_durable_bindings_checked': True,
          'all_projection_unpacked_files_identical': True, 'all_originals_retained': True,
          'log_argv_results_and_bytes_checked': True, 'all_helper_hashes_unchanged': True,
          'new_Lean_calls': 0, 'new_network_calls': 0, 'full250_checked': False,
          'full_certificate_proved': False}
write_new(ROOT / 'TerminalPostcheck.json', result)
print(json.dumps({'status': 'checked', 'manifest_sha256': result['inventory_sha256'],
                  'postcheck_sha256': sha(ROOT / 'TerminalPostcheck.json'),
                  'files': result['inventory_files'], 'bytes': result['inventory_bytes']}))
