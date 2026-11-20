"""Preserve twelve original Actions ZIPs, with a release-side byte readback."""
from hashlib import file_digest
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import os
import subprocess


HERE = Path(__file__).resolve().parent
ORIGINS = json.loads((HERE / 'origins.json').read_bytes())
REPO = ORIGINS['repository']
TAG = ORIGINS['tag']
TARGET = ORIGINS['target']
API = 'repos/' + REPO + '/'
RECEIPT = 'rotating-proof-asset-receipt.json'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    with path.open('rb') as file:
        return file_digest(file, 'sha256').hexdigest()


def gh(*args, output=None, missing=False):
    result = subprocess.run(['gh', *args], stdout=output if output else subprocess.PIPE,
                            stderr=subprocess.PIPE, check=False)
    if result.returncode:
        message = result.stderr.decode(errors='replace')
        if missing and '(HTTP 404)' in message:
            return None
        raise RuntimeError(message)
    return result.stdout


def api(path, missing=False):
    raw = gh('api', API + path, missing=missing)
    return None if raw is None else json.loads(raw)


def download(path, destination):
    headers = ['-H', 'Accept: application/octet-stream'] if path.startswith('releases/assets/') else []
    with destination.open('wb') as out:
        gh('api', '--allow-escape-sequences', *headers, API + path, output=out)


def origins():
    rows = ORIGINS['assets']
    require(len(rows) == len({r['asset_name'] for r in rows}) == len({r['artifact_id'] for r in rows}) == 12,
            'Expected twelve unique originals')
    for row in rows:
        require(Path(row['asset_name']).name == row['asset_name'] and row['asset_name'].endswith('.zip'),
                'Invalid asset name')
    return rows


def verify_bytes(path, row):
    require(path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], path.name + ' differs')


def checked_origin(row, runs, previous):
    run_id = row['run_id']
    if run_id not in runs:
        runs[run_id] = api('actions/runs/' + str(run_id))
    run = runs[run_id]
    require((run['id'], run['head_sha'], run['path'], run['run_attempt'], run['status'], run['conclusion']) ==
            (run_id, row['head_sha'], row['workflow'], row['run_attempt'], 'completed', 'success'), 'Origin run differs')
    job = api('actions/jobs/' + str(row['job_id']))
    require((job['id'], job['run_id'], job['name'], job['head_sha'], job['status'], job['conclusion']) ==
            (row['job_id'], run_id, row['job_name'], row['head_sha'], 'completed', 'success'), 'Origin job differs')
    meta = api('actions/artifacts/' + str(row['artifact_id']), missing=previous)
    if meta is None:
        require(previous, 'Missing original Actions artifact')
        return
    require((meta['id'], meta['name'], meta['size_in_bytes'], meta['digest'],
             meta['workflow_run']['id'], meta['workflow_run']['head_sha']) ==
            (row['artifact_id'], row['artifact_name'], row['bytes'], 'sha256:' + row['sha256'],
             run_id, row['head_sha']), 'Origin artifact differs')
    if previous:
        return
    require(not meta['expired'], 'Original artifact has expired')
    log = gh('api', '--allow-escape-sequences', API + 'actions/jobs/' + str(job['id']) + '/logs').decode('utf-8-sig')
    require(row['sha256'] in log and
            any('successfully finalized' in line and ('Artifact ID ' + str(meta['id'])) in line
                for line in log.splitlines()), 'Producer log does not bind the uploaded artifact')


def tag_identity(required):
    ref = api('git/ref/tags/' + TAG, missing=not required)
    if ref is None:
        return
    obj = ref['object']
    while obj['type'] == 'tag':
        obj = api('git/tags/' + obj['sha'])['object']
    require(obj['type'] == 'commit' and obj['sha'] == TARGET, 'Existing tag targets another commit')


def release():
    obj = api('releases/tags/' + TAG, missing=True)
    if obj is not None:
        require(obj['tag_name'] == TAG and not obj['draft'] and not obj['prerelease'], 'Unexpected release metadata')
        tag_identity(True)
    return obj


def assets_by_name(release_id):
    all_assets = []
    page = 1
    while True:
        part = api('releases/' + str(release_id) + '/assets?per_page=100&page=' + str(page))
        all_assets.extend(part)
        if len(part) < 100:
            break
        page += 1
    result = {a['name']: a for a in all_assets}
    require(len(result) == len(all_assets), 'Duplicate release asset name')
    return result


def save_once(release_id, row, local, readback):
    name = row['asset_name']
    asset = assets_by_name(release_id).get(name)
    if asset is None:
        verify_bytes(local, row)
        gh('release', 'upload', TAG, str(local), '--repo', REPO)
        asset = assets_by_name(release_id)[name]
    detail = api('releases/assets/' + str(asset['id']))
    require(detail['name'] == name and detail['state'] == 'uploaded' and detail['size'] == row['bytes'],
            'Release asset identity differs: ' + name)
    require(detail.get('digest') in (None, 'sha256:' + row['sha256']), 'Release API digest differs: ' + name)
    download('releases/assets/' + str(detail['id']), readback)
    verify_bytes(readback, row)
    print('Verified release download', name, detail['id'], row['sha256'], flush=True)
    return {'name': name, 'id': detail['id'], 'bytes': row['bytes'], 'sha256': row['sha256'],
            'browser_download_url': detail['browser_download_url']}


def main():
    require(os.environ.get('GITHUB_REPOSITORY') == REPO, 'Unexpected repository')
    rows = origins()
    with TemporaryDirectory() as directory:
        temp = Path(directory)
        tag_identity(False)
        current = release()
        existing = assets_by_name(current['id']) if current else {}
        runs = {}
        for row in rows:
            previous = row['asset_name'] in existing
            checked_origin(row, runs, previous)
            if not previous:
                local = temp / row['asset_name']
                download('actions/artifacts/' + str(row['artifact_id']) + '/zip', local)
                verify_bytes(local, row)
        if current is None:
            gh('release', 'create', TAG, '--target', TARGET, '--title', 'Closed rotating elastic-flow profiles',
               '--notes-file', str(HERE / 'ReleaseNotes.md'), '--latest=false', '--repo', REPO)
            current = release()
            require(current is not None, 'Published release missing')
        readback = temp / 'readback'
        verified = []
        for row in rows:
            saved = save_once(current['id'], row, temp / row['asset_name'], readback)
            verified.append({**saved, 'source_artifact_id': row['artifact_id'], 'producer_job_id': row['job_id']})
        receipt = {'schema': 'rotating.verified-release-assets.v1', 'repository': REPO,
                   'tag': TAG, 'target_commit': TARGET, 'release_id': current['id'],
                   'release_url': current['html_url'], 'origins_sha256': sha(HERE / 'origins.json'),
                   'assets': verified}
        result = temp / RECEIPT
        result.write_bytes((json.dumps(receipt, indent=2, sort_keys=True) + '\n').encode('utf-8'))
        record = {'asset_name': RECEIPT, 'bytes': result.stat().st_size, 'sha256': sha(result)}
        last = save_once(current['id'], record, result, readback)
        require(release()['id'] == current['id'], 'Release changed during publication')
        output = Path(os.environ['RUNNER_TEMP']) / 'rotating-release-readback.json'
        output.write_bytes((json.dumps({'release': receipt, 'receipt_asset': last}, indent=2) + '\n').encode())


if __name__ == '__main__':
    main()
