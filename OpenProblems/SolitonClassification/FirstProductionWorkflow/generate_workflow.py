"""Render a review-only workflow after an observed successful core transfer.

No network, GitHub mutation, Lean call, numeric generation or workflow install.
The five supplied evidence JSON files must describe the actual successful run.
The live workflow checks the upstream GitHub identities again before download.
"""
from pathlib import Path
import argparse, hashlib, json, re

SOURCE = 'cff971bcac7ac2d83aba04596ce09e44fda1ac29'
TOOLS = 'ec3547c9456f47b5bf7c8b9d07ff07bf56ff24d9'
CORE_RUN = 43345535919
INVENTORY = '598bee6a58a1d0531944f229fd1a7a1c6522f2bfcb06e61a96ee7cc5e7ff4b57'
CORE_INVENTORY = '2c252cf849e22e027ca2630b836e5227b8ff8390cf45f36a6b467db64580c924'
PLAN = 'a62ef654ec4f2fd01d55b6dae19c28483dba137c424c3068a372c514b89559c1'
FINAL = '51e1abe4b94640773e1fe66f93cfc1ad58a57fafbd050a260eba53da0f61fd72'
GIB = 1024**3
KEYS = ('RP0000', 'RP3968', 'RM0000', 'RM3968')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def positive_integer(value, label):
    require(type(value) is int and value > 0, 'Invalid positive integer: ' + label)
    return value


def validate_evidence(evidence, repository, tool_revision):
    require(re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository) is not None,
            'Invalid repository')
    require(tool_revision == TOOLS and tool_revision != SOURCE, 'Wrong separate published tool revision')
    require(set(evidence) == {'run', 'artifact', 'index', 'restore', 'imports'}, 'Missing actual evidence')
    run, artifact, index, restore, imports = (evidence[k] for k in ('run', 'artifact', 'index', 'restore', 'imports'))
    require(run['id'] == CORE_RUN and run['head_sha'] == SOURCE
            and run['status'] == 'completed' and run['conclusion'] == 'success'
            and run['repository']['full_name'] == repository, 'Original core run has not actually succeeded')
    attempt = positive_integer(run['run_attempt'], 'core run attempt')
    artifact_id = positive_integer(artifact['id'], 'artifact id')
    require(artifact['expired'] is False
            and artifact['name'] == f'rotating-core-full-{CORE_RUN}-{attempt}'
            and artifact['workflow_run']['id'] == CORE_RUN
            and artifact['workflow_run']['head_sha'] == SOURCE, 'Wrong/expired upstream artifact')
    for record, schema in ((index, 'rotating.production-core-pack.v1'),
                           (restore, 'rotating.production-core-restore.v1'),
                           (imports, 'rotating.restored-core-import.v1')):
        require(record['schema'] == schema and record['status'] == 'checked'
                and record['revision'] == SOURCE and record['full_certificate_proved'] is False,
                'Missing actual checked core evidence: ' + schema)
        require(record['source_inventory_sha256'] == CORE_INVENTORY, 'Wrong core source inventory')
    for field in ('archive_sha256', 'base_lock_sha256'):
        value = index[field]
        require(re.fullmatch('[0-9a-f]{64}', value or '') is not None
                and restore[field] == imports[field] == value, 'Conflicting core digest: ' + field)
    require(restore['header_sha256'] == index['header_sha256']
            and restore['stdlib_before_after_checked'] is True
            and restore['complete_restored_base_twice_checked'] is True,
            'Incomplete actual restoration')
    require(imports['complete_base_before_after_checked'] is True
            and imports['actual_fresh_private_audit'] is True and imports['actual_arctan_import'] is True
            and imports['used_lake_or_mathlib_cache'] is False and imports['output_on_library_search_path'] is False
            and imports['numerical_leaves_checked'] == 0, 'Incomplete actual restored import check')
    rows = imports['modules']
    require([r['name'] for r in rows] == ['SolitonClassification.Rotating.ModuleFullGenericAudit', 'RestoredArctanProbe']
            and all(r['exit_code'] == 0 for r in rows)
            and rows[0]['declarations'] == 1704 and rows[0]['private_declarations'] == 331,
            'Missing actual generic1704/private331 and Arctan results')
    for field in ('archive_bytes', 'payload_bytes', 'payload_files'):
        positive_integer(index[field], field)
    zip_size = positive_integer(artifact['size_in_bytes'], 'actual GitHub artifact ZIP bytes')
    return {'schema': 'rotating.first-production-workflow-pins.v1', 'repository': repository,
        'core_run_id': CORE_RUN, 'core_run_attempt': attempt, 'core_source_revision': SOURCE,
        'tool_package_revision': tool_revision, 'tool_inventory_sha256': INVENTORY,
        'core_inventory_sha256': CORE_INVENTORY, 'plan_sha256': PLAN, 'final_manifest_sha256': FINAL,
        'core_artifact_id': artifact_id, 'core_artifact_name': artifact['name'],
        'core_archive_sha256': index['archive_sha256'], 'core_base_lock_sha256': index['base_lock_sha256'],
        'core_archive_bytes': index['archive_bytes'], 'core_payload_bytes': index['payload_bytes'],
        'core_artifact_zip_bytes': zip_size, 'headroom_bytes': 2*GIB,
        'shard_reserve_bytes': 8*GIB, 'final48_reserve_bytes': 2*GIB,
        'max_parallel': 4, 'retention_days': 30, 'full_certificate_proved': False}


API_CHECK = r'''import json, os, urllib.request
from pathlib import Path
p=json.loads(os.environ['PINS'])
token=os.environ['GH_TOKEN']
def get(suffix):
    request=urllib.request.Request('https://api.github.com/repos/'+p['repository']+suffix,
        headers={'Authorization':'Bearer '+token,'Accept':'application/vnd.github+json',
                 'X-GitHub-Api-Version':'2022-11-28'})
    with urllib.request.urlopen(request,timeout=60) as response: return json.load(response)
run=get('/actions/runs/'+str(p['core_run_id']))
artifact=get('/actions/artifacts/'+str(p['core_artifact_id']))
assert run['id']==p['core_run_id'] and run['head_sha']==p['core_source_revision']
assert run['status']=='completed' and run['conclusion']=='success'
assert run['run_attempt']==p['core_run_attempt'] and run['repository']['full_name']==p['repository']
assert artifact['id']==p['core_artifact_id'] and artifact['name']==p['core_artifact_name']
assert artifact['expired'] is False and artifact['workflow_run']['id']==p['core_run_id']
assert artifact['workflow_run']['head_sha']==p['core_source_revision']
assert artifact['size_in_bytes']==p['core_artifact_zip_bytes']
out=Path(os.environ['WORK'])/'evidence';out.mkdir(parents=True,exist_ok=True)
for name,value in [('github-core-run.json',run),('github-core-artifact.json',artifact),('pins.json',p)]:
    (out/name).write_text(json.dumps(value,indent=2)+'\n')
'''

DISK_CHECK = r'''import json, os, shutil
from pathlib import Path
p=json.loads(os.environ['PINS']);stage=os.environ['DISK_STAGE'];work=Path(os.environ['WORK'])
reserve=p['final48_reserve_bytes'] if os.environ['KIND']=='final48' else p['shard_reserve_bytes']
required=reserve+p['headroom_bytes']
if stage in ('before_download','after_download'): required+=p['core_payload_bytes']
if stage=='before_download': required+=p['core_archive_bytes']+p['core_artifact_zip_bytes']
free=shutil.disk_usage(work).free
row={'stage':stage,'actual_free_bytes':free,'required_free_bytes':required,
     'reserve_bytes':reserve,'reserve_is_policy_not_measurement':True,
     'core_archive_bytes':p['core_archive_bytes'],'core_payload_bytes':p['core_payload_bytes'],
     'core_artifact_zip_bytes':p['core_artifact_zip_bytes'],'sufficient':free>=required}
(work/'evidence'/('disk-'+stage+'.json')).write_text(json.dumps(row,indent=2)+'\n')
assert free>=required, 'Insufficient disk space for exact retained-core test'
'''

RECEIPT_CHECK = r'''import hashlib,json,os
from pathlib import Path
p=json.loads(os.environ['PINS']);r=Path(os.environ['WORK'])/'restored'
receipt=json.loads((r/'restore_receipt.json').read_bytes())
assert receipt['schema']=='rotating.production-core-restore.v1' and receipt['status']=='checked'
assert receipt['revision']==p['core_source_revision'] and receipt['archive_sha256']==p['core_archive_sha256']
assert receipt['base_lock_sha256']==p['core_base_lock_sha256']
assert receipt['source_inventory_sha256']==p['core_inventory_sha256']
assert receipt['stdlib_before_after_checked'] is True and receipt['complete_restored_base_twice_checked'] is True
assert hashlib.sha256((r/'base_lock.json').read_bytes()).hexdigest()==p['core_base_lock_sha256']
assert hashlib.sha256((r/'base_args.json').read_bytes()).hexdigest()==receipt['restored_base_args_sha256']
'''

DOWNLOAD_CHECK = r'''import hashlib,json,os
from pathlib import Path
p=json.loads(os.environ['PINS']);d=Path(os.environ['WORK'])/'download'
assert {f.name for f in d.iterdir()}=={'core.tar.xz','core.tar.xz.index.json'}
archive=d/'core.tar.xz';index=json.loads((d/'core.tar.xz.index.json').read_bytes())
assert archive.stat().st_size==p['core_archive_bytes']
assert index['schema']=='rotating.production-core-pack.v1' and index['status']=='checked'
assert index['revision']==p['core_source_revision']
assert index['archive_sha256']==p['core_archive_sha256'] and index['base_lock_sha256']==p['core_base_lock_sha256']
assert index['payload_bytes']==p['core_payload_bytes'] and index['archive_bytes']==p['core_archive_bytes']
assert index['source_inventory_sha256']==p['core_inventory_sha256']
h=hashlib.sha256()
with archive.open('rb') as stream:
    for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
assert h.hexdigest()==p['core_archive_sha256']
'''

FINAL_REPORT_CHECK = r'''import json,os
from pathlib import Path
w=Path(os.environ['WORK']);p=json.loads(os.environ['PINS'])
if os.environ['KIND']=='shard':
    job=json.loads((w/'job/checked_job.json').read_bytes())
    report=json.loads((w/'job/generated/compile_report.json').read_bytes())
    consumer=json.loads((w/'public_consumer/public_consumer_report.json').read_bytes())
    assert job['kernel_checked'] is True and job['key']==os.environ['KEY']
    assert job['revision']==p['core_source_revision'] and job['plan_sha256']==p['plan_sha256']
    assert job['base_lock_sha256']==p['core_base_lock_sha256']
    assert report['status']=='checked' and report['shard_kernel_checked'] is True
    assert consumer['status']=='checked' and consumer['exit_code']==0 and consumer['public_only_consumer_checked'] is True
else:
    report=json.loads((w/'final48/compile_report.json').read_bytes())
    assert report['status']=='checked' and report['supplementary_modules_checked']==48
    assert report['conditional_geometry_audit_count']==2205 and report['full_certificate_proved'] is False
    assert report['base_lock_sha256']==p['core_base_lock_sha256']
    assert report['supplement_manifest_sha256']==p['final_manifest_sha256']
    assert report['core_inventory_sha256']==p['core_inventory_sha256']
    assert report['full_path_instances_checked'] is False
    assert report['fresh_public_only_audit_checked'] is True and report['private_project_input_files']==0
    assert report['extra_external_setup_modules']==[]
    rows=report['modules']
    assert len(rows)==48 and len({r['name'] for r in rows})==48
    assert all(r['exit_code']==0 and r['termination']=='completed' for r in rows)
    audit=report['fresh_audit']
    assert audit['name']=='SolitonClassification.Rotating.FinalSupplementFreshAudit'
    assert audit['exit_code']==0 and audit['termination']=='completed'
summary={'schema':'rotating.first-production-job.v1','kind':os.environ['KIND'],'key':os.environ['KEY'],
         'status':'checked','source_revision':p['core_source_revision'],
         'tool_package_revision':p['tool_package_revision'],'core_archive_sha256':p['core_archive_sha256'],
         'core_base_lock_sha256':p['core_base_lock_sha256'],'plan_sha256':p['plan_sha256'],
         'full_certificate_proved':False,'retention_days':30,'permanent_archive_claim':False}
(w/'evidence/job-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
'''


def py(script):
    return "python3 - <<'PY'\n" + script.rstrip() + "\nPY\n"


def run_step(name, script, **extra):
    return {'name': name, 'run': script, **extra}


def workflow(pins, filename):
    require(re.fullmatch(r'[a-z][a-z0-9-]*\.yml', filename) is not None, 'Unsafe workflow filename')
    steps = [
        run_step('Set the isolated output path using the runner shell environment',
                 'printf \'WORK=%s/rotating-first-production\\n\' "$RUNNER_TEMP" >> "$GITHUB_ENV"\n'),
        {'uses':'actions/checkout@v4','with':{'ref':SOURCE,'path':'core-source','persist-credentials':False}},
        {'uses':'actions/checkout@v4','with':{'ref':pins['tool_package_revision'],'path':'tool-source','persist-credentials':False}},
        run_step('Bind exact source and tool revisions; verify unchanged packages',
            'set -euo pipefail\n'
            'test "$(git -C "$GITHUB_WORKSPACE/core-source" rev-parse HEAD)" = "$CORE_REVISION"\n'
            'test "$(git -C "$GITHUB_WORKSPACE/tool-source" rev-parse HEAD)" = "$TOOL_REVISION"\n'
            'mkdir -p "$WORK/evidence"\n'
            'python3 -B "$TOOLS/verify_production_pipeline.py" --package "$PACKAGE" '
            '--inventory-sha256 "$PIPELINE_SHA" --core-project "$CORE_PROJECT"\n'),
        {'uses':'leanprover/lean-action@ba3fdfe5c4476c925da13bf11a005ddb47e47aee','with':{
            'lake-package-directory':'core-source/OpenProblems/SolitonClassification/ModuleProduction',
            'build':'false','test':'false','lint':'false','use-mathlib-cache':'false','use-github-cache':'false'}},
        run_step('Assert no fallback Lake tree; record installed Lean',
            'set -euo pipefail\ntest ! -e "$CORE_PROJECT/.lake"\nulimit -c 0\n'
            'lean --version | tee "$WORK/evidence/installed-lean.txt"\n'),
        run_step('Check the successful original run and exact unexpired artifact',py(API_CHECK),
                 env={'GH_TOKEN':'${{ github.token }}'}),
        run_step('Check actual-size disk budget before download',py(DISK_CHECK),env={'DISK_STAGE':'before_download'}),
        {'uses':'actions/download-artifact@v4','with':{
            'artifact-ids':str(pins['core_artifact_id']),'repository':pins['repository'],
            'run-id':str(CORE_RUN),'github-token':'${{ github.token }}',
            'merge-multiple':True,'path':'${{ env.WORK }}/download'}},
        run_step('Verify downloaded archive/index identities and actual sizes',py(DOWNLOAD_CHECK)),
        run_step('Check remaining disk before restoration',py(DISK_CHECK),env={'DISK_STAGE':'after_download'}),
        run_step('Restore the exact captured core into new paths',
            'python3 -B "$TOOLS/production_core_artifact.py" restore '
            '--archive "$WORK/download/core.tar.xz" --output "$WORK/restored" '
            '--sha256 "$CORE_SHA" --revision "$CORE_REVISION" --lean lean\n'),
        run_step('Match this job restoration receipt to all pinned identities',py(RECEIPT_CHECK)),
        run_step('Fresh private audit and Arctan import from the restored core',
            'python3 -B "$TOOLS/production_core_import_check.py" '
            '--restored "$WORK/restored" --project "$CORE_PROJECT" --output "$WORK/core_import" '
            '--revision "$CORE_REVISION" --archive-sha256 "$CORE_SHA" --base-lock-sha256 "$LOCK_SHA" '
            '--memory-mb 4096 --seconds 600\n'),
        run_step('Check reserved space before compilation',py(DISK_CHECK),env={'DISK_STAGE':'after_restore'}),
        run_step('Generate exact shard sources from the pinned untrusted plan',
            'python3 -B "$TOOLS/production_job.py" prepare '
            '--plan "$PACKAGE/plan/plan.json" --plan-sha256 "$PLAN_SHA" --revision "$CORE_REVISION" '
            '--key "$KEY" --seed "$PACKAGE/inputs/shooting_certificate.json" '
            '--candidate-source "$PACKAGE/inputs/CandidateInitial.original.lean" '
            '--template-root "$PACKAGE/inputs/templates" --output "$WORK/job"\n',
            **{'if':"matrix.kind == 'shard'"}),
        run_step('Actually compile all 47 modules and pack the complete checked shard',
            'python3 -B "$TOOLS/production_job.py" compile-pack '
            '--plan "$PACKAGE/plan/plan.json" --plan-sha256 "$PLAN_SHA" --revision "$CORE_REVISION" '
            '--key "$KEY" --seed "$PACKAGE/inputs/shooting_certificate.json" '
            '--candidate-source "$PACKAGE/inputs/CandidateInitial.original.lean" '
            '--template-root "$PACKAGE/inputs/templates" --output "$WORK/job" '
            '--base-lock "$WORK/restored/base_lock.json" --base-lock-sha256 "$LOCK_SHA" '
            '--base-args "$WORK/restored/base_args.json" --seconds 600 --memory-mb 4096\n',
            **{'if':"matrix.kind == 'shard'"}),
        run_step('Actually import the validated complete bundle using public project inputs only',
            'python3 -B "$TOOLS/production_public_consumer.py" --manifest "$WORK/job/generated/manifest.json" '
            '--base-args "$WORK/restored/base_args.json" --output "$WORK/public_consumer" '
            '--seconds 120 --memory-mb 4096\n',**{'if':"matrix.kind == 'shard'"}),
        run_step('Actually compile final48 and fresh conditional2205 audit on Linux',
            'python3 -B "$TOOLS/production_compile_final_supplement.py" '
            '--supplement-manifest "$FINAL_SOURCES/FinalSourcesManifest.json" '
            '--core-inventory "$CORE_PROJECT/ModuleProductionSourceInventory.json" '
            '--base-lock "$WORK/restored/base_lock.json" --base-args "$WORK/restored/base_args.json" '
            '--expected-base-lock-sha256 "$LOCK_SHA" --output "$WORK/final48" --seconds 600 --memory-mb 4096\n',
            **{'if':"matrix.kind == 'final48'"}),
        run_step('Check actual completion and retain the conditional scope',py(FINAL_REPORT_CHECK)),
        run_step('Recheck all pinned source bytes and absence of fallback cache',
            'set -euo pipefail\npython3 -B "$TOOLS/verify_production_pipeline.py" --package "$PACKAGE" '
            '--inventory-sha256 "$PIPELINE_SHA" --core-project "$CORE_PROJECT"\n'
            'test ! -e "$CORE_PROJECT/.lake"\n'
            'test "$(git -C "$GITHUB_WORKSPACE/core-source" rev-parse HEAD)" = "$CORE_REVISION"\n'
            'test "$(git -C "$GITHUB_WORKSPACE/tool-source" rev-parse HEAD)" = "$TOOL_REVISION"\n'),
        {'name':'Retain full original bundles and evidence for 30 days','if':'always()',
         'uses':'actions/upload-artifact@v4','with':{
             'name':'rotating-first4-${{ matrix.key }}-${{ github.run_id }}-${{ github.run_attempt }}',
             'path':'\n'.join('${{ env.WORK }}/'+s for s in (
                 'evidence','restored/restore_receipt.json','restored/base_args.json','restored/base_lock.json',
                 'restored/core-metadata.json','download/core.tar.xz.index.json','core_import',
                 'job/generated','job/*.json','job/*.tar.xz','public_consumer','final48')),
             'if-no-files-found':'warn','compression-level':0,'retention-days':30}}]
    result = {'name':'Rotating first four exact-core shards and final48',
        'on':{'workflow_dispatch':{},'push':{'branches':['research/remaining-open-problems'],
                                           'paths':['.github/workflows/'+filename]}},
        'permissions':{'contents':'read','actions':'read'},
        'concurrency':{'group':'rotating-first-production-${{ github.ref }}','cancel-in-progress':False},
        'jobs':{'checked':{'name':'${{ matrix.key }} on one exact restored core','runs-on':'ubuntu-24.04',
            'timeout-minutes':'${{ matrix.timeout }}',
            'strategy':{'fail-fast':False,'max-parallel':4,'matrix':{'include':
                [{'kind':'shard','key':key,'timeout':120} for key in KEYS]
                +[{'kind':'final48','key':'final48','timeout':90}]}},
            'defaults':{'run':{'shell':'bash'}},
            'env':{'PYTHONDONTWRITEBYTECODE':'1','CORE_REVISION':SOURCE,'TOOL_REVISION':pins['tool_package_revision'],
                'CORE_SHA':pins['core_archive_sha256'],'LOCK_SHA':pins['core_base_lock_sha256'],
                'PIPELINE_SHA':INVENTORY,'PLAN_SHA':PLAN,'KIND':'${{ matrix.kind }}','KEY':'${{ matrix.key }}',
                'CORE_PROJECT':'${{ github.workspace }}/core-source/OpenProblems/SolitonClassification/ModuleProduction',
                'PACKAGE':'${{ github.workspace }}/tool-source/OpenProblems/SolitonClassification/ProductionPipeline',
                'TOOLS':'${{ github.workspace }}/tool-source/OpenProblems/SolitonClassification/ProductionPipeline/tools',
                'FINAL_SOURCES':'${{ github.workspace }}/tool-source/OpenProblems/SolitonClassification/FinalSources',
                'PINS':json.dumps(pins,separators=(',',':'))},'steps':steps}}}
    validate_contexts(result)
    return result


def validate_contexts(document):
    for job in document['jobs'].values():
        for value in job.get('env', {}).values():
            require(not isinstance(value, str) or re.search(r'\$\{\{\s*runner(?:\.|\[)', value) is None,
                    'runner context is not available in jobs.<job>.env')


def yaml_lines(value, indent=0):
    pad = ' ' * indent
    if isinstance(value, dict):
        for key, child in value.items():
            label = json.dumps(key) + ':'
            if isinstance(child, (dict, list)) and child:
                yield pad + label
                yield from yaml_lines(child, indent+2)
            elif isinstance(child, str) and '\n' in child:
                yield pad + label + ' |'
                for line in child.rstrip('\n').split('\n'):
                    yield pad + '  ' + line
            else:
                yield pad + label + ' ' + json.dumps(child,ensure_ascii=False)
    elif isinstance(value, list):
        for child in value:
            if isinstance(child, (dict, list)) and child:
                yield pad + '-'
                yield from yaml_lines(child, indent+2)
            else:
                yield pad + '- ' + json.dumps(child,ensure_ascii=False)
    else:
        raise TypeError('Only structured workflow nodes belong here')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--tool-package-revision', required=True)
    for field in ('run','artifact','index','restore','imports'):
        parser.add_argument('--'+field, type=Path, required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--workflow-filename',default='rotating-first-production.yml')
    args = parser.parse_args()
    require(not args.output.exists() and '.github' not in args.output.parts,
            'Require a new isolated review directory outside .github')
    for path in [args.output,*args.output.parents]:
        require(not path.is_symlink() and not (hasattr(path,'is_junction') and path.is_junction()), 'Linked output path')
    evidence = {key:json.loads(getattr(args,key).read_bytes()) for key in ('run','artifact','index','restore','imports')}
    pins = validate_evidence(evidence,args.repository,args.tool_package_revision)
    document = workflow(pins,args.workflow_filename)
    text = '\n'.join(yaml_lines(document))+'\n'
    args.output.mkdir(parents=True,exist_ok=False)
    output = args.output/args.workflow_filename
    output.write_text(text,encoding='utf-8',newline='\n')
    report = {'schema':'rotating.first-production-workflow-generation.v1','status':'rendered_for_root_review',
        'generator_sha256':sha(Path(__file__)),'workflow_sha256':sha(output),'pins':pins,
        'evidence_sha256':{key:sha(getattr(args,key)) for key in evidence},
        'workflow_installed':False,'workflow_executed':False,'new_Lean_calls':0,'new_numeric_generation_calls':0,
        'full_certificate_proved':False}
    (args.output/'generation_report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'status':report['status'],'workflow_sha256':report['workflow_sha256'],
                      'workflow_executed':False}),flush=True)


if __name__=='__main__':
    main()
