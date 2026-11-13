"""Prepare a concrete pinned request and workflow; never execute publication here."""
from pathlib import Path
import ast,hashlib,importlib.util,json,sys
root=Path(__file__).resolve().parent
formal=root/'rotating_formal';sys.path.insert(0,str(formal/'pipeline'))
import production_core_release_request as adapter
P='d64ad3cf29e2eb285f3c3a25cd20f9a28a7aca57'
SOURCE='cff971bcac7ac2d83aba04596ce09e44fda1ac29'
PACKAGE_SHA='77222621d482e4f41e9f018af1366baa117cbd5c22ef33df9220912e347896c7'
WRITER_SHA='c063b963b402cdce9354caac5451b6bf686ea2297a962e049649e97db2826eed'
pkg=root/'core_release_tools_publication/package'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_bytes())
assert sha(pkg/'SourceInventory.json')==PACKAGE_SHA
pack,restore,imports=[read(pkg/'evidence'/(name+'.json')) for name in ('pack','restore','imports')]
artifacts=read(pkg/'evidence/core_artifacts.json')['artifacts']
q={'schema':adapter.SCHEMA,'repository':adapter.r.REPO,'test_fixture':False,'layer':'original-core',
   'source_revision':SOURCE,'publisher_revision':P,'publisher_sha256':WRITER_SHA,'helper_sha256':adapter.helpers(),
   'tag':'soliton-rotating-cff971bcac7a-core-20261113-01110125281c',
   'title':'Checked rotating-profile Lean core, 2026-11-13',
   'base_lock_sha256':pack['base_lock_sha256'],'source_inventory_sha256':pack['source_inventory_sha256'],
   'archive':{'file':'exact-core.tar.xz','sha256':pack['archive_sha256'],'bytes':pack['archive_bytes'],
              'asset_name':'SolitonClassification-exact-core-'+pack['archive_sha256'][:16]+'.tar.xz'},
   'evidence':{name:{'file':name+'.json','sha256':sha(pkg/'evidence'/(name+'.json')),
                     'bytes':(pkg/'evidence'/(name+'.json')).stat().st_size} for name in ('pack','restore','imports')},
   'origins':{}}
for key,aid in [('archive',14003699438),('producer_evidence',14004486679),('consumer_evidence',14004881037)]:
    item=next(row for row in artifacts if row['id']==aid)
    assert item['expired'] is False and item['workflow_run']['head_sha']==SOURCE
    q['origins'][key]={'origin_run_id':43345535919,'origin_head_sha':SOURCE,'origin_artifact_id':aid,
                      'origin_artifact_zip_sha256':item['digest'].removeprefix('sha256:'),
                      'origin_artifact_zip_bytes':item['size_in_bytes']}
adapter.validate_request(q,WRITER_SHA);adapter.check_evidence(q,pack,restore,imports)
out=root/'core_release_execution_review';out.mkdir(exist_ok=False)
request_bytes=adapter.core.json_bytes(q);(out/'request.json').write_bytes(request_bytes)
REQUEST_SHA=hashlib.sha256(request_bytes).hexdigest()

VERIFY=r'''import hashlib,json,os,subprocess,sys
from pathlib import Path
package=Path(os.environ['PACKAGE']);request=Path(os.environ['REQUEST'])
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert subprocess.check_output(['git','-C',str(package),'rev-parse','HEAD'],text=True).strip()==os.environ['TOOL_REVISION']
assert sha(package/'SourceInventory.json')==os.environ['PACKAGE_SHA']
inventory=json.loads((package/'SourceInventory.json').read_bytes())
actual={p.relative_to(package).as_posix() for p in package.rglob('*') if p.is_file()}
assert actual==set(inventory['files'])|{'SourceInventory.json'}
for name,wanted in inventory['files'].items():
    file=package/name
    assert not file.is_symlink() and file.stat().st_size==wanted['bytes'] and sha(file)==wanted['sha256']
assert sha(request)==os.environ['REQUEST_SHA']
sys.path.insert(0,str(package/'tools'))
import production_core_release_request as adapter
import production_core_release_publisher as writer
q=adapter.core.strict_json(request.read_bytes())
adapter.validate_request(q,sha(Path(writer.__file__)))
assert q['publisher_revision']==os.environ['TOOL_REVISION']
identity=writer.actions_context(q,os.environ,writer.checked_tool_revision())
reader=adapter.r.ReadOnlyReleaseHTTP(token=os.environ['GH_TOKEN'])
for origin in q['origins'].values():reader.verify_origin(origin)
work=Path(os.environ['WORK']);(work/'evidence').mkdir(parents=True,exist_ok=True)
(work/'evidence/approved_request.json').write_bytes(request.read_bytes())
(work/'evidence/publisher_identity.json').write_text(json.dumps(identity,indent=2)+'\n')
'''
DISK=r'''import json,os,shutil
from pathlib import Path
q=json.loads(Path(os.environ['REQUEST']).read_bytes());work=Path(os.environ['WORK'])
required=q['archive']['bytes']+q['origins']['archive']['origin_artifact_zip_bytes']+2*1024**3
free=shutil.disk_usage(work).free
(work/'evidence/disk.json').write_text(json.dumps({'actual_free_bytes':free,'required_free_bytes':required,
    'headroom_bytes':2*1024**3,'sufficient':free>=required},indent=2)+'\n')
assert free>=required
'''
PREPARE=r'''import hashlib,json,os,shutil
from pathlib import Path
q=json.loads(Path(os.environ['REQUEST']).read_bytes());work=Path(os.environ['WORK']);package=Path(os.environ['PACKAGE'])
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as stream:
        for b in iter(lambda:stream.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
d=work/'download'
assert {p.name for p in d.iterdir()}=={'core.tar.xz','core.tar.xz.index.json'}
archive=d/'core.tar.xz';assert archive.stat().st_size==q['archive']['bytes'] and sha(archive)==q['archive']['sha256']
assert sha(d/'core.tar.xz.index.json')==q['evidence']['pack']['sha256']
inputs=work/'inputs';inputs.mkdir()
for name,wanted in q['evidence'].items():
    src=package/'evidence'/wanted['file'];assert sha(src)==wanted['sha256'] and src.stat().st_size==wanted['bytes']
    shutil.copyfile(src,inputs/wanted['file'])
archive.rename(inputs/q['archive']['file'])
'''
POSTCHECK=r'''import hashlib,json,os
from pathlib import Path
work=Path(os.environ['WORK']);q=json.loads(Path(os.environ['REQUEST']).read_bytes())
result=json.loads((work/'journal/result.json').read_bytes())
assert result['schema']=='rotating.durable-core-release-record.v1'
assert result['status']=='remote_verified' and result['test_fixture'] is False
assert result['remote_durability_verified'] is True and result['actual_http_writes']==4
assert result['revision']==q['source_revision'] and result['release']['tag']==q['tag']
assert result['asset']['digest']=='sha256:'+q['archive']['sha256'] and result['asset']['size']==q['archive']['bytes']
assert result['verification']['redownload_sha256']==q['archive']['sha256']
assert result['verification']['redownload_bytes']==q['archive']['bytes']
assert result['publisher']['revision']==q['publisher_revision']
assert result['actual_lean_run_here'] is False and result['full_certificate_proved'] is False
'''
basis_path=formal/'pipeline/first_production_linux_design_v3/generate_workflow.py'
assert sha(basis_path)=='4acffcc6a6724368c29a24b18856ab923c07f8d93ce2e7d88cd542e67cdfd6c8'
spec=importlib.util.spec_from_file_location('basis',basis_path);basis=importlib.util.module_from_spec(spec);spec.loader.exec_module(basis)
def run(name,script,**kw):return {'name':name,'run':script,**kw}
doc={'name':'Publish exact checked rotating-profile core archive',
 'on':{'workflow_dispatch':{},'push':{'branches':['research/remaining-open-problems'],
 'paths':['.github/workflows/rotating-publish-core.yml']}},
 'permissions':{'contents':'write','actions':'read'},
 'concurrency':{'group':'rotating-core-publisher','cancel-in-progress':False},
 'jobs':{'publish':{'runs-on':'ubuntu-24.04','timeout-minutes':60,'defaults':{'run':{'shell':'bash'}},
 'env':{'PYTHONDONTWRITEBYTECODE':'1','TOOL_REVISION':P,'PACKAGE_SHA':PACKAGE_SHA,'REQUEST_SHA':REQUEST_SHA,
        'PACKAGE':'${{ github.workspace }}/tool-source/OpenProblems/SolitonClassification/CoreReleaseTools',
        'REQUEST':'${{ github.workspace }}/request-source/OpenProblems/SolitonClassification/CoreReleaseExecution/request.json'},
 'steps':[
 run('Set isolated publication paths','printf \'WORK=%s/rotating-core-publish\\n\' "$RUNNER_TEMP" >> "$GITHUB_ENV"\n'),
 {'uses':'actions/checkout@v4','with':{'ref':P,'path':'tool-source','persist-credentials':False}},
 {'uses':'actions/checkout@v4','with':{'ref':'${{ github.sha }}','path':'request-source','persist-credentials':False}},
 run('Validate exact tool checkout, request and successful upstream origins',basis.py(VERIFY),env={'GH_TOKEN':'${{ github.token }}'}),
 run('Check actual publication disk budget',basis.py(DISK)),
 {'uses':'actions/download-artifact@v4','with':{'artifact-ids':'14003699438','repository':adapter.r.REPO,
  'run-id':'43345535919','github-token':'${{ github.token }}','merge-multiple':True,'path':'${{ env.WORK }}/download'}},
 run('Rehash original archive and prepare its dedicated core request inputs',basis.py(PREPARE)),
 run('Publish the new core release with full draft and published redownload verification',
     'python3 -B "$PACKAGE/tools/production_core_release_publisher.py" --request "$REQUEST" '
     '--request-sha256 "$REQUEST_SHA" --input-root "$WORK/inputs" --output "$WORK/journal" --execute\n',
     env={'GH_TOKEN':'${{ github.token }}'}),
 run('Verify the actual durable core record and retain its limited scope',basis.py(POSTCHECK)),
 {'name':'Retain publication journal and approved inputs even on failure','if':'always()',
  'uses':'actions/upload-artifact@v4','with':{'name':'rotating-core-publication-${{ github.run_id }}-${{ github.run_attempt }}',
   'path':'${{ env.WORK }}/journal\n${{ env.WORK }}/evidence\n${{ env.WORK }}/inputs/*.json\n${{ env.WORK }}/download/*.json',
   'if-no-files-found':'warn','retention-days':30,'compression-level':1}}]}}}
for script in (VERIFY,DISK,PREPARE,POSTCHECK):ast.parse(script)
assert all('runner.' not in value for value in doc['jobs']['publish']['env'].values())
workflow=out/'rotating-publish-core.yml';workflow.write_text('\n'.join(basis.yaml_lines(doc))+'\n',encoding='utf-8',newline='\n')
report={'schema':'rotating.core-release-execution-preparation.v1','publisher_tool_revision':P,
 'request_sha256':REQUEST_SHA,'workflow_sha256':sha(workflow),'package_inventory_sha256':PACKAGE_SHA,
 'actual_request_validated_against_pinned_evidence':True,'embedded_Python_AST_count':4,
 'workflow_installed':False,'workflow_executed':False,'real_release_created':False,'full_certificate_proved':False}
(out/'preparation_report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report))
