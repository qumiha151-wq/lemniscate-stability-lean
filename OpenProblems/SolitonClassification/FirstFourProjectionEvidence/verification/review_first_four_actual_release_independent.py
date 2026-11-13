"""Read-only independent replay of the downloaded first-four publication evidence.

No network, subprocess, Lean, archive extraction or publisher entrypoint calls.
Only the named new review JSON is written; original evidence is never changed.
"""
from pathlib import Path
import hashlib
import json
import re
import sys
import zipfile

HERE = Path(__file__).resolve()
WORK = HERE.parents[2]
PIPE = WORK / 'rotating_formal/pipeline'
sys.path.insert(0, str(PIPE))
import production_release_url_protocol as protocol
import production_public_projection as projection

R = WORK / 'first_four_release_execution_publication'
D = R / 'downloaded_evidence/unpacked'
KEYS = ['RP0000', 'RP3968', 'RM0000', 'RM3968']
SOURCE = 'cff971bcac7ac2d83aba04596ce09e44fda1ac29'
PLAN = 'a62ef654ec4f2fd01d55b6dae19c28483dba137c424c3068a372c514b89559c1'
BASE = 'dcf9b162c42c30f387803fc9f395fcb1183f0e8179f5b46004782ba4bbf1f10d'
REQ = '43825fd353fc7fe02c244b30393f4f4221e9d18799950bc73c72adcc4c1b7cef'
REC = dict(zip(KEYS, [
    '92ae696c5c11fc8097253534778747500a775e534522d61e86c40b6a14e4e910',
    '4830497e721f832848aa615bffaeafd0a19b0c9446a672ec746862dd30a5953c',
    '70d343fa118e6b96ca07a9a35421417849ccec3a732f42afb2e4340daaf5ce4b',
    '5cbc08318f2a272e4b957dcbdd0cae1212cdac17eb0ab36e6364ead2ff4c5e13']))

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def read(p):
    return json.loads(Path(p).read_bytes())

def file_pin(p, digest, size=None):
    assert Path(p).is_file() and not Path(p).is_symlink()
    assert sha(p) == digest
    if size is not None:
        assert Path(p).stat().st_size == size

def chain(root, expected):
    events = []
    previous = None
    raw_names = set()
    for p in sorted(root.glob('*.json')):
        if not re.fullmatch(r'\d{5}_(?!raw_response).*\.json', p.name):
            continue
        e = read(p)
        assert e['schema'] == 'rotating.release-journal-event.v1'
        assert e['sequence'] == len(events) and e['previous_sha256'] == previous
        assert p.name == f"{len(events):05d}_{e['event']}.json"
        if e['event'] == 'api_response':
            r = e['data']
            assert r['file'] == f"{len(events):05d}_raw_response.json"
            file_pin(root / r['file'], r['sha256'], r['bytes'])
            raw_names.add(r['file'])
        previous = sha(p)
        events.append(e)
    assert len(events) == expected
    assert {p.name for p in root.glob('*_raw_response.json')} == raw_names
    return events

zip_path = R / 'downloaded_evidence/evidence.zip'
file_pin(zip_path, 'b691f0ae337d109e522b6b5a0a6c8fac08dad9a7fed2d43e04f6d4f14401d029', 238825)
download = read(R / 'downloaded_evidence/download_verification.json')
assert len(download['files']) == 245
assert {p.relative_to(D).as_posix() for p in D.rglob('*') if p.is_file()} == set(download['files'])
with zipfile.ZipFile(zip_path) as z:
    names = [i.filename for i in z.infolist() if not i.is_dir()]
    assert len(names) == len(set(names)) == 245 and set(names) == set(download['files'])
    for name in names:
        raw = z.read(name)
        pin = download['files'][name]
        assert len(raw) == pin['bytes'] and hashlib.sha256(raw).hexdigest() == pin['sha256']
        assert (D / name).read_bytes() == raw

file_pin(D / 'evidence/approved_envelope.json', REQ)
env = read(D / 'evidence/approved_envelope.json')
q = env['original_request']
assert q['source_revision'] == SOURCE and q['plan_sha256'] == PLAN and q['base_lock_sha256'] == BASE
assert q['scope'] == 'partial' and q['test_fixture'] is False
assert [j['key'] for j in q['jobs']] == KEYS
assert read(D / 'publication/original_request.json') == q
file_pin(D / 'evidence/plan.json', PLAN)
file_pin(D / 'evidence/package_inventory.json', '5f41beeb146219268f552449db11282e82958494eb4f1f147be15082a36c096d')
package = WORK / 'shard_release_tools_v2_publication/package'
inventory = read(D / 'evidence/package_inventory.json')
for relative, pin in inventory['files'].items():
    file_pin(package / relative, pin['sha256'], pin['bytes'])
for name, digest in env['helper_sha256'].items():
    p = PIPE.parent / 'performance/reference.py' if name == 'reference.py' else PIPE / name
    file_pin(p, digest)
file_pin(PIPE / 'production_shard_release_publisher_v2.py', env['publisher_sha256'])

events = {}
for rel, count in [('origin_journal', 8), ('download_journal', 16), ('publication/journal', 101)]:
    events[rel] = chain(D / rel, count)
for rel in ('origin_journal', 'download_journal'):
    assert not any(e['event'] == 'mutation_intent' for e in events[rel])
origin_raw = [read(p) for p in (D / 'origin_journal').glob('*_raw_response.json')]
run_rows = [x for x in origin_raw if x.get('id') == 43354529340]
assert len(run_rows) == 4
assert all(x['status'] == 'completed' and x['conclusion'] == 'success'
           and x['head_sha'] == 'cef10f7ef398d1526c03c66f5ef84a71e697b3cb' for x in run_rows)
for job in q['jobs']:
    a = next(x for x in origin_raw if x.get('id') == job['origin_artifact_id'])
    assert a['expired'] is False and a['size_in_bytes'] == job['origin_artifact_zip_bytes']
    assert a['workflow_run']['id'] == 43354529340

je = events['publication/journal']
assert je[0]['event'] == 'started' and je[-1]['event'] == 'finished'
intents = [e['data'] for e in je if e['event'] == 'mutation_intent']
assert [i['method'] for i in intents] == ['POST'] * 6 + ['PATCH']
api = '/repos/qumiha151-wq/lemniscate-stability-lean'
assert intents[0]['endpoint'] == api + '/git/refs'
assert intents[0]['payload'] == {'ref': 'refs/tags/' + q['tag'], 'sha': SOURCE}
assert intents[1]['endpoint'] == api + '/releases'
assert intents[1]['payload']['draft'] is True and intents[1]['payload']['target_commitish'] == SOURCE
assert intents[-1]['endpoint'] == api + '/releases/443812088' and intents[-1]['payload'] == {'draft': False}
for job, i in zip(q['jobs'], intents[2:6]):
    assert i['endpoint'] == api + '/releases/443812088/assets'
    assert i['upload_name'] == job['asset_name'] and i['bytes'] == job['archive_bytes']

journal = D / 'publication/journal'
summary = read(journal / 'summary.json')
assert je[-1]['data']['summary_sha256'] == sha(journal / 'summary.json')
assert summary['publisher']['journal_previous_sha256'] == je[-1]['previous_sha256']
assert summary['status'] == 'remote_verified' and summary['test_fixture'] is False
assert summary['actual_http_writes'] == 7 and summary['full_certificate_proved'] is False
assert summary['publisher']['actions'] == read(D / 'evidence/publisher_identity.json')
assert summary['publisher']['actions']['run_id'] == 43364989743
assert summary['publisher']['actions']['tool_revision'] == q['publisher_revision']
assert summary['publisher']['script_sha256'] == env['publisher_sha256']
assert summary['publisher']['request_sha256'] == REQ
raws = {sha(p): read(p) for p in journal.glob('*_raw_response.json')}
published = read(R / 'observed_release.json')
identity = protocol.validate_release(published, 443812088, q['tag'], SOURCE, draft=False)
assert len(published['assets']) == 4 and published['published_at'] == '2026-11-13T04:23:05Z'
assert published.get('immutable') is False
preflight = read(D / 'publication/preflight/dry_run_plan.json')
downloads = read(D / 'evidence/downloads.json')
assert preflight['helper_sha256'] == q['helper_sha256']
assert preflight['request_sha256'] == sha(D / 'publication/original_request.json')
rows = []
for job, pre, dl, sr in zip(q['jobs'], preflight['archives'], downloads, summary['records']):
    key = job['key']
    assert key == pre['key'] == dl['key'] == sr['key']
    assert pre['complete_original_archive_validated'] is True and pre['original_retained'] is True
    for field in ('archive_sha256', 'archive_bytes', 'origin_artifact_id', 'origin_artifact_zip_sha256', 'origin_artifact_zip_bytes'):
        assert pre[field] == job[field]
    assert dl['actual_network_download'] is True and dl['new_Lean_calls'] == 0
    assert dl['zip_sha256'] == job['origin_artifact_zip_sha256'] and dl['zip_bytes'] == job['origin_artifact_zip_bytes']
    assert dl['archive_sha256'] == job['archive_sha256'] and dl['archive_bytes'] == job['archive_bytes']
    record_path = journal / 'records' / (key + '.json')
    file_pin(record_path, REC[key], sr['record_bytes'])
    rec = read(record_path)
    projection.durable_record(record_path.read_bytes(), REC[key], SOURCE, job['archive_sha256'], job['archive_bytes'])
    assert rec['test_fixture'] is False and rec['release']['draft'] is False
    assert rec['publisher'] == summary['publisher'] and rec['key'] == key
    assert rec['base_lock_sha256'] == BASE and rec['plan_sha256'] == PLAN
    asset = next(x for x in published['assets'] if x['id'] == rec['asset']['id'])
    assert protocol.validate_asset(asset, identity, rec['asset']['id'], job['asset_name'], job['archive_sha256'], job['archive_bytes']) == rec['asset']
    a = raws[rec['verification']['asset_api_sha256']]
    assert protocol.validate_asset(a, identity, rec['asset']['id'], job['asset_name'], job['archive_sha256'], job['archive_bytes']) == rec['asset']
    assert protocol.validate_release(raws[rec['verification']['release_api_sha256']], 443812088, q['tag'], SOURCE, draft=False) == identity
    folder = WORK / 'first_production_v3_publication' / ('fourth_download' if key == 'RM3968' else 'first_three_downloads')
    local_zip = folder / (key + '.zip')
    local_archive = folder / key / dl['member']
    file_pin(local_zip, job['origin_artifact_zip_sha256'], job['origin_artifact_zip_bytes'])
    file_pin(local_archive, job['archive_sha256'], job['archive_bytes'])
    local_manifest = folder / key / 'job/generated/manifest.json'
    local_report = folder / key / 'job/generated/compile_report.json'
    file_pin(local_manifest, pre['manifest_sha256'])
    file_pin(local_report, pre['compile_report_sha256'])
    rows.append({'key': key, 'record_sha256': REC[key], 'asset_id': rec['asset']['id'],
                 'original_archive': str(local_archive), 'archive_sha256': sha(local_archive),
                 'archive_bytes': local_archive.stat().st_size, 'original_zip_sha256': sha(local_zip),
                 'compile_report_sha256': sha(local_report), 'manifest_sha256': sha(local_manifest)})
run = read(R / 'observed_run.json')
assert run['id'] == 43364989743 and run['status'] == 'completed' and run['conclusion'] == 'success'
assert run['head_sha'] == summary['publisher']['actions']['workflow_revision']
result = {'schema': 'rotating.first-four-actual-independent-review.v1', 'status': 'checked',
          'script_sha256': sha(HERE), 'evidence_zip_sha256': sha(zip_path), 'exact_evidence_files': 245,
          'journal_counts': {k: len(v) for k, v in events.items()},
          'actual_mutation_intents': 7, 'release_id': 443812088, 'run_id': 43364989743,
          'package_source_files_checked': len(inventory['files']), 'records': rows,
          'independent_local_original_zip_and_tar_hashes_checked': True,
          'full_archive_preflight_reports_and_local_manifest_report_hashes_checked': True,
          'complete_archive_validation_rerun_in_this_review': False,
          'eight_full_remote_downloads_inferred_from_successful_frozen_control_flow': True,
          'new_remote_downloads': 0, 'new_GitHub_writes': 0, 'new_Lean_calls': 0,
          'release_immutable_observed': False, 'full250_checked': False, 'full_certificate_proved': False}
out = HERE.with_name('FirstFourActualReleaseIndependentReplay.json')
assert not out.exists()
out.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'status': 'checked', 'report': str(out), 'report_sha256': sha(out), 'records': len(rows)}))
