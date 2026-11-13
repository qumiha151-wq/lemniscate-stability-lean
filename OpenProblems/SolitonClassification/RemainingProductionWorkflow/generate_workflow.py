"""Render the remaining 246 shards only after actual first-five success.

No network, Lean, numeric generation, workflow installation or GitHub mutation.
Reuses the byte-pinned V3 workflow constructor; all proof tools remain unchanged.
"""
from pathlib import Path
import argparse, ast, copy, hashlib, importlib.util, json, re

REPO = 'qumiha151-wq/lemniscate-stability-lean'
FIRST_RUN = 43354529340
FIRST_REVISION = 'cef10f7ef398d1526c03c66f5ef84a71e697b3cb'
BASIS_GENERATOR = '4acffcc6a6724368c29a24b18856ab923c07f8d93ce2e7d88cd542e67cdfd6c8'
BASIS_REPORT = 'de481db49ce80e4c48639aab30458725d78204b81afeb37e22f7d832bcbc21fb'
FIRST_KEYS = ('RP0000', 'RP3968', 'RM0000', 'RM3968')
EXPECTED_NAMES = {key + ' on one exact restored core' for key in (*FIRST_KEYS, 'final48')}
MAX_PARALLEL = 12


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_bytes(), object_pairs_hook=unique_pairs)


def load_basis(path):
    require(digest(path) == BASIS_GENERATOR, 'Frozen V3 generator changed')
    spec = importlib.util.spec_from_file_location('first_production_basis_v3', path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def validate_first(run, jobs):
    require(run['id'] == FIRST_RUN and run['head_sha'] == FIRST_REVISION
            and run['repository']['full_name'] == REPO
            and run['status'] == 'completed' and run['conclusion'] == 'success',
            'Actual first-five run is not successfully completed')
    require(type(run['run_attempt']) is int and run['run_attempt'] >= 1,
            'Invalid first-five run attempt')
    rows = jobs['jobs']
    require(jobs['total_count'] == len(rows) == 5
            and {j['name'] for j in rows} == EXPECTED_NAMES
            and len({j['id'] for j in rows}) == 5, 'Missing/duplicate first-five jobs')
    for row in rows:
        require(row['run_id'] == FIRST_RUN and row['head_sha'] == FIRST_REVISION
                and row['status'] == 'completed' and row['conclusion'] == 'success',
                'First-five job not checked successfully')
        steps = {s['name']: s for s in row['steps']}
        required = ['Fresh private audit and Arctan import from the restored core',
                    'Check actual completion and retain the conditional scope',
                    'Recheck all pinned source bytes and absence of fallback cache']
        if row['name'].startswith('final48 '):
            required += ['Actually compile final48 and fresh conditional2205 audit on Linux']
        else:
            required += ['Actually compile all 47 modules and pack the complete checked shard',
                         'Actually import the validated complete bundle using public project inputs only']
        require(all(name in steps and steps[name]['status'] == 'completed'
                    and steps[name]['conclusion'] == 'success' for name in required),
                'Missing actual compile/import completion step')
    return {'run_id': FIRST_RUN, 'head_sha': FIRST_REVISION, 'run_attempt': run['run_attempt'],
            'jobs': {row['name']: row['id'] for row in rows}}


FIRST_CHECK = r'''import json, os, urllib.request
from pathlib import Path
p=json.loads(os.environ['FIRST_PINS'])
def get(suffix):
    req=urllib.request.Request('https://api.github.com/repos/qumiha151-wq/lemniscate-stability-lean'+suffix,
        headers={'Authorization':'Bearer '+os.environ['GH_TOKEN'],
                 'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28'})
    with urllib.request.urlopen(req,timeout=60) as response: return json.load(response)
run=get('/actions/runs/'+str(p['run_id']))
jobs=get('/actions/runs/'+str(p['run_id'])+'/jobs?per_page=100')
assert run['id']==p['run_id'] and run['head_sha']==p['head_sha']
assert run['repository']['full_name']=='qumiha151-wq/lemniscate-stability-lean'
assert run['status']=='completed' and run['conclusion']=='success'
assert run['run_attempt']==p['run_attempt']
assert jobs['total_count']==len(jobs['jobs'])==5
assert {j['name']:j['id'] for j in jobs['jobs']}==p['jobs']
assert all(j['run_id']==p['run_id'] and j['head_sha']==p['head_sha']
           and j['status']=='completed' and j['conclusion']=='success' for j in jobs['jobs'])
out=Path(os.environ['WORK'])/'evidence'
(out/'successful-first-run.json').write_text(json.dumps(run,indent=2)+'\n')
(out/'successful-first-jobs.json').write_text(json.dumps(jobs,indent=2)+'\n')
'''


def render(basis, pins, first, plan, filename):
    require(plan['revision'] == basis.SOURCE and plan['revision_kind'] == 'git', 'Wrong source plan')
    keys = [job['key'] for job in plan['jobs']]
    canonical = ['R' + sign + f'{start:04d}' for sign in ('P', 'M') for start in range(0, 4000, 32)]
    require(keys == canonical, 'Expected canonical full250 source plan')
    remaining = [key for key in keys if key not in FIRST_KEYS]
    require(len(remaining) == 246 and not set(remaining).intersection(FIRST_KEYS), 'Incorrect remaining coverage')
    updated = copy.deepcopy(pins)
    updated['max_parallel'] = MAX_PARALLEL
    doc = basis.workflow(updated, filename)
    doc['name'] = 'Rotating remaining 246 exact-core shards'
    doc['concurrency']['group'] = 'rotating-remaining-production-${{ github.ref }}'
    job = doc['jobs']['checked']
    job['strategy']['max-parallel'] = MAX_PARALLEL
    job['strategy']['matrix']['include'] = [{'kind': 'shard', 'key': key, 'timeout': 120} for key in remaining]
    job['env']['FIRST_PINS'] = json.dumps(first, separators=(',', ':'))
    steps = job['steps']
    steps[0]['run'] = steps[0]['run'].replace('rotating-first-production', 'rotating-remaining-production')
    steps.insert(4, basis.run_step('Require the actual successful first four shards and final48',
                                  basis.py(FIRST_CHECK), env={'GH_TOKEN': '${{ github.token }}'}))
    # Each successful full archive already contains sources, all artifact layers,
    # original logs and reports. Do not upload the expanded duplicate again.
    upload = steps[-1]
    require(upload['uses'] == 'actions/upload-artifact@v4', 'Unexpected basis final step')
    upload['name'] = 'Retain complete original archive and review evidence for 30 days'
    upload['with']['name'] = 'rotating-remaining-${{ matrix.key }}-${{ github.run_id }}-${{ github.run_attempt }}'
    lines = upload['with']['path'].splitlines()
    upload['with']['path'] = '\n'.join(line for line in lines
                                     if not line.endswith('/job/generated') and not line.endswith('/final48'))
    steps.append({'name': 'Retain expanded diagnostics when a job fails',
                  'if': 'failure()', 'uses': 'actions/upload-artifact@v4',
                  'with': {'name': 'rotating-failed-${{ matrix.key }}-${{ github.run_id }}-${{ github.run_attempt }}',
                           'path': '${{ env.WORK }}/job/generated', 'if-no-files-found': 'warn',
                           'compression-level': 1, 'retention-days': 30}})
    # Remove the conditional final48 compiler step; its actual successful run is
    # required above and is not duplicated in this matrix.
    job['steps'] = [step for step in steps if step.get('if') != "matrix.kind == 'final48'"]
    basis.validate_contexts(doc)
    basis.validate_toolchain_usage(doc)
    require(doc['permissions'] == {'contents': 'read', 'actions': 'read'}, 'Mutation permission in numerical jobs')
    require(job['runs-on'] == 'ubuntu-24.04', 'Only the standard public Linux runner is allowed')
    return doc


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('basis-generator', 'basis-report', 'first-run', 'first-jobs', 'plan', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    for name in ('first-run-sha256', 'first-jobs-sha256'):
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--workflow-filename', default='rotating-remaining-production.yml')
    args = parser.parse_args()
    require(not args.output.exists() and '.github' not in args.output.parts, 'Require a fresh review directory')
    for path in [args.output, *args.output.parents]:
        require(not path.is_symlink() and not (hasattr(path, 'is_junction') and path.is_junction()), 'Linked output path')
    require(digest(args.basis_report) == BASIS_REPORT, 'Exact successful-core basis report changed')
    basis = load_basis(args.basis_generator)
    require(digest(args.plan) == basis.PLAN, 'Production source plan changed')
    require(digest(args.first_run) == args.first_run_sha256
            and digest(args.first_jobs) == args.first_jobs_sha256, 'Actual first-five evidence pin differs')
    first = validate_first(read_json(args.first_run), read_json(args.first_jobs))
    pins = read_json(args.basis_report)['pins']
    doc = render(basis, pins, first, read_json(args.plan), args.workflow_filename)
    args.output.mkdir(parents=True)
    target = args.output / args.workflow_filename
    target.write_text('\n'.join(basis.yaml_lines(doc)) + '\n', encoding='utf-8', newline='\n')
    report = {'schema': 'rotating.remaining-workflow-generation.v1', 'status': 'rendered_for_root_review',
              'generator_sha256': digest(__file__), 'basis_generator_sha256': BASIS_GENERATOR,
              'basis_report_sha256': BASIS_REPORT, 'workflow_sha256': digest(target),
              'first_run_sha256': args.first_run_sha256, 'first_jobs_sha256': args.first_jobs_sha256,
              'first_success': first, 'remaining_jobs': 246, 'max_parallel': MAX_PARALLEL,
              'workflow_installed': False, 'workflow_executed': False,
              'Lean_calls': 0, 'numeric_generation_calls': 0, 'full_certificate_proved': False}
    (args.output / 'generation_report.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
