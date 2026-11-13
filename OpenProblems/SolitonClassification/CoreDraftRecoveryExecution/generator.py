"""Prepare the concrete one-draft recovery request and workflow, without execution."""
from pathlib import Path
import ast,hashlib,importlib.util,json,sys
root=Path(__file__).resolve().parent;formal=root/'rotating_formal'
sys.path.insert(0,str(formal/'pipeline'))
import production_core_draft_recovery as writer
P='37fa090e1f51cb17d40f45706fb24879fd068d75'
TREE='412a0a04bbd8640f18aa98be1f0b96923738036b'
PACKAGE_SHA='821ecdd18ef62d557f2d6294f819a5f79c99486fd3694af7eb93e9e2e6214fb9'
package=root/'core_draft_recovery_tools_publication/package'
out=root/'core_draft_recovery_execution_review';out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
q=json.loads((formal/'performance/core_draft_recovery_wire_review_v3/actual_request.json').read_bytes())
q['publisher_revision']=P
request=out/'request.json';request.write_bytes(writer.core.json_bytes(q));REQUEST_SHA=sha(request)
assert sha(package/'SourceInventory.json')==PACKAGE_SHA
ctx=writer.prepare(request,REQUEST_SHA,package/'inputs')
assert q['release_id']==443789076 and q['asset_id']==742149339 and not q['test_fixture']
VERIFY=r'''import hashlib,json,os,sys
from pathlib import Path
package=Path(os.environ['PACKAGE']);request=Path(os.environ['REQUEST']);work=Path(os.environ['WORK'])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert os.environ['GITHUB_RUN_ATTEMPT']=='1'
assert sha(package/'SourceInventory.json')==os.environ['PACKAGE_SHA']
inventory=json.loads((package/'SourceInventory.json').read_bytes())
assert {p.relative_to(package).as_posix() for p in package.rglob('*') if p.is_file()}==set(inventory['files'])|{'SourceInventory.json'}
for name,pin in inventory['files'].items():
    p=package/name;assert not p.is_symlink() and p.stat().st_size==pin['bytes'] and sha(p)==pin['sha256']
assert sha(request)==os.environ['REQUEST_SHA']
sys.path.insert(0,str(package/'tools'))
import production_core_draft_recovery as writer
ctx=writer.prepare(request,os.environ['REQUEST_SHA'],package/'inputs')
assert ctx['request']['publisher_revision']==os.environ['TOOL_REVISION']
identity=writer.old.actions_context(ctx['request'],os.environ,writer.checked_tool_revision())
(work/'evidence').mkdir(parents=True)
(work/'evidence/approved_recovery_request.json').write_bytes(request.read_bytes())
(work/'evidence/tool_identity.json').write_text(json.dumps(identity,indent=2)+'\n')
(work/'evidence/source_inventory.json').write_bytes((package/'SourceInventory.json').read_bytes())
'''
POST=r'''import json,os
from pathlib import Path
work=Path(os.environ['WORK']);q=json.loads(Path(os.environ['REQUEST']).read_bytes())
o=json.loads((Path(os.environ['PACKAGE'])/'inputs/original_request.json').read_bytes())
r=json.loads((work/'journal/result.json').read_bytes())
assert r['schema']=='rotating.durable-core-release-record.v1' and r['status']=='remote_verified'
assert r['test_fixture'] is False and r['remote_durability_verified'] is True and r['actual_http_writes']==1
assert r['release']['id']==q['release_id'] and r['asset']['id']==q['asset_id']
assert r['release']['draft'] is False and r['release']['tag']==o['tag']
assert r['revision']==o['source_revision'] and r['asset']['digest']=='sha256:'+o['archive']['sha256']
assert r['verification']['redownload_sha256']==o['archive']['sha256']
assert r['verification']['redownload_bytes']==o['archive']['bytes']
assert r['verification']['draft_redownload']=={'sha256':o['archive']['sha256'],'bytes':o['archive']['bytes']}
assert r['publisher']['revision']==q['publisher_revision']
assert r['publisher']['request_sha256']==os.environ['REQUEST_SHA']
assert r['publisher']['actions']['workflow_revision']==os.environ['GITHUB_SHA']
assert r['recovery']['original_request_sha256']==q['original_request']['sha256']
assert r['recovery']['created_new_release_or_asset'] is False
assert r['actual_lean_run_here'] is False and r['full_certificate_proved'] is False
'''
basis_path=formal/'pipeline/first_production_linux_design_v3/generate_workflow.py'
assert sha(basis_path)=='4acffcc6a6724368c29a24b18856ab923c07f8d93ce2e7d88cd542e67cdfd6c8'
spec=importlib.util.spec_from_file_location('basis',basis_path);basis=importlib.util.module_from_spec(spec);spec.loader.exec_module(basis)
doc={'name':'Recover the verified existing rotating core draft',
    'on':{'workflow_dispatch':{},'push':{'branches':['research/remaining-open-problems'],
        'paths':['.github/workflows/rotating-recover-core-draft.yml']}},
    'permissions':{'contents':'write','actions':'read'},
    'concurrency':{'group':'rotating-core-publisher','cancel-in-progress':False},
    'jobs':{'recover':{'runs-on':'ubuntu-24.04','timeout-minutes':30,'defaults':{'run':{'shell':'bash'}},
        'env':{'PYTHONDONTWRITEBYTECODE':'1','TOOL_REVISION':P,'PACKAGE_SHA':PACKAGE_SHA,'REQUEST_SHA':REQUEST_SHA,
            'PACKAGE':'${{ github.workspace }}/tool-source/OpenProblems/SolitonClassification/CoreDraftRecoveryTools',
            'REQUEST':'${{ github.workspace }}/request-source/OpenProblems/SolitonClassification/CoreDraftRecoveryExecution/request.json'},
        'steps':[
            {'name':'Set isolated recovery output','run':'printf \'WORK=%s/rotating-core-draft-recovery\\n\' "$RUNNER_TEMP" >> "$GITHUB_ENV"\n'},
            {'uses':'actions/checkout@v4','with':{'ref':P,'path':'tool-source','persist-credentials':False}},
            {'uses':'actions/checkout@v4','with':{'ref':'${{ github.sha }}','path':'request-source','persist-credentials':False}},
            {'name':'Check frozen tools, original failed journal and exact existing draft request','run':basis.py(VERIFY)},
            {'name':'Verify existing draft bytes, publish once, and verify published bytes','run':
                'python3 -B "$PACKAGE/tools/production_core_draft_recovery.py" --request "$REQUEST" '
                '--request-sha256 "$REQUEST_SHA" --input-root "$PACKAGE/inputs" --output "$WORK/journal" --execute\n',
                'env':{'GH_TOKEN':'${{ github.token }}'}},
            {'name':'Check actual durable record and preserved proof scope','run':basis.py(POST)},
            {'name':'Retain recovery journal even after an ambiguous failure','if':'always()',
                'uses':'actions/upload-artifact@v4','with':{'name':'rotating-core-draft-recovery-${{ github.run_id }}-${{ github.run_attempt }}',
                    'path':'${{ env.WORK }}/journal\n${{ env.WORK }}/evidence',
                    'if-no-files-found':'warn','retention-days':30,'compression-level':1}}
        ]}}}
for script in (VERIFY,POST):ast.parse(script)
workflow=out/'rotating-recover-core-draft.yml'
workflow.write_text('\n'.join(basis.yaml_lines(doc))+'\n',encoding='utf-8',newline='\n')
report={'schema':'rotating.core-draft-recovery-execution-preparation.v1','publisher_tool_revision':P,
    'request_sha256':REQUEST_SHA,'workflow_sha256':sha(workflow),'package_inventory_sha256':PACKAGE_SHA,
    'actual_original_journal_request_and_core_report_preflight':True,'embedded_Python_AST_count':2,
    'only_planned_mutation':'PATCH /releases/443789076 with draft:false after complete download',
    'workflow_installed':False,'workflow_executed':False,'full_certificate_proved':False}
(out/'preparation_report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report))
