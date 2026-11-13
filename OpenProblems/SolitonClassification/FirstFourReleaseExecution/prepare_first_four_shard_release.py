"""Generate a pinned first-four release request/workflow locally; no network/write API."""
from pathlib import Path, PurePosixPath
import argparse, ast, hashlib, json, re
import production_shard_release_publisher_v2 as publisher

SOURCE='cff971bcac7ac2d83aba04596ce09e44fda1ac29'
ORIGIN='cef10f7ef398d1526c03c66f5ef84a71e697b3cb'
RUN=43354529340
PLAN_REVISION='ec3547c9456f47b5bf7c8b9d07ff07bf56ff24d9'
PLAN_SHA='a62ef654ec4f2fd01d55b6dae19c28483dba137c424c3068a372c514b89559c1'
PLAN_INVENTORY='598bee6a58a1d0531944f229fd1a7a1c6522f2bfcb06e61a96ee7cc5e7ff4b57'
BASE='dcf9b162c42c30f387803fc9f395fcb1183f0e8179f5b46004782ba4bbf1f10d'
WRITER='cba63be08c987643a1bbf86aeb5793171667b433dc2a4bbacd962817fdf90b38'
REPO='qumiha151-wq/lemniscate-stability-lean'
ROWS=[
 ('RP0000',14005794759,221772404,'7f83be6c3709989154504f14abd35e685fe1c7c18d55bc0e4fa5068a72a3c4c2',25183056,'4f6e00f119c104550034d0cd46db34c0bba14ab3840e20364e469fb6de857f95'),
 ('RP3968',14005579983,223139021,'eb6d2b019832ebfcba6200fa624831c3c416aea8d4f724e80527caa3c8a71679',25403856,'7cd4bec36e73cccc81d633951c4b2de5481edeb95d664401e99db32573103882'),
 ('RM0000',14006437764,221782739,'90c1617daf279ce7b5405091b855a6c3215c45907eaf4e93fbe3bcb2e219944d',25218772,'7b2a5adba142023ee60bdaa1bd2242f309b500e24bed7847371e69c062adcb8a'),
 ('RM3968',14006812342,223145640,'8157a47b7840ea09488c4ee271ee5d6ef2df6789a1c888d17f1449567b4a6c03',25449496,'2eb9ba93bf4c73bd42534ab0e141dc4c59c0a068c5059c05916ba169685822b1')]
require=publisher.require
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()


def archive_member(key):
    return 'job/rotating-'+SOURCE+'-'+key[1].lower()+'-'+key[2:]+'-0032.tar.xz'


def jobs():
    return [{'key':k,'archive':k+'.tar.xz','archive_sha256':h,'archive_bytes':n,
        'asset_name':'SolitonClassification-'+k+'-'+h[:16]+'.tar.xz',
        'origin_run_id':RUN,'origin_head_sha':ORIGIN,'origin_artifact_id':aid,
        'origin_artifact_zip_sha256':zh,'origin_artifact_zip_bytes':zn}
        for k,aid,zn,zh,n,h in ROWS]


def check_evidence(run,artifacts,receipts):
    require(run['id']==RUN and run['head_sha']==ORIGIN and run['run_attempt']==1
        and run['repository']['full_name']==REPO and run['status']=='completed'
        and run['conclusion']=='success','Original successful run differs')
    aa=artifacts['artifacts'];require(len({x['id'] for x in aa})==len(aa),'Duplicate artifact ids')
    rr=[x for receipt in receipts for x in receipt]
    require(len(rr)==4 and {x['key'] for x in rr}=={x[0] for x in ROWS},'Expected four local download receipts')
    for k,aid,zn,zh,n,h in ROWS:
        a=next((x for x in aa if x['id']==aid),None)
        require(a is not None and a['expired'] is False and a['size_in_bytes']==zn
            and a['digest']=='sha256:'+zh and a['workflow_run']['id']==RUN
            and a['workflow_run']['head_sha']==ORIGIN,'Original artifact metadata differs')
        r=next(x for x in rr if x['key']==k)
        require(r['artifact_id']==aid and r['zip_bytes']==zn and r['zip_sha256']==zh
            and r['files'][archive_member(k)]=={'bytes':n,'sha256':h},'Actual local ZIP/archive receipt differs')


def check_package(package,inventory_sha):
    package=publisher.core.plain_path(package,'dir')
    inventory=package/'SourceInventory.json'
    require(sha(inventory)==inventory_sha,'Wrong publisher package inventory')
    data=publisher.core.strict_json(inventory.read_bytes())
    require(data['schema']=='rotating.shard-release-tools-package.v2','Publisher package schema differs')
    expected=data['files'];actual=set()
    for path in package.rglob('*'):
        require(not path.is_symlink() and not (hasattr(path,'is_junction') and path.is_junction()),'Package link')
        if path.is_file():actual.add(path.relative_to(package).as_posix())
    require(actual==set(expected)|{'SourceInventory.json'},'Publisher package file set differs')
    for relative,wanted in expected.items():
        path=publisher.c.confined(package,relative)
        require(path.stat().st_size==wanted['bytes'] and sha(path)==wanted['sha256'],'Publisher package bytes differ')
    for name,h in publisher.helpers().items():
        relative=('performance/' if name=='reference.py' else 'tools/')+name
        require(expected[relative]['sha256']==h,'Package helper differs from frozen implementation')
    require(sha(Path(publisher.__file__))==WRITER,'Expected frozen v2 publisher')
    return data


def envelope(revision,plan):
    require(isinstance(revision,str) and re.fullmatch('[0-9a-f]{40}',revision),'Exact published tool P is required')
    q={'schema':publisher.r.SCHEMA,'test_fixture':False,'repository':REPO,'scope':'partial','layer':'original-data',
       'source_revision':SOURCE,'publisher_revision':revision,'plan_sha256':PLAN_SHA,'base_lock_sha256':BASE,
       'tag':'soliton-rotating-cff971bcac7a-original-first4-20261113',
       'title':'Four checked rotating-profile shard archives, 2026-11-13',
       'helper_sha256':publisher.r.helpers(),'jobs':jobs()}
    v={'schema':publisher.SCHEMA,'original_request':q,'publisher_sha256':WRITER,'helper_sha256':publisher.helpers()}
    publisher.validate_envelope(v,plan)
    return v


VERIFY=r'''from pathlib import Path
import hashlib,json,os,subprocess,sys
package=Path(os.environ['PACKAGE']);request=Path(os.environ['REQUEST']);plan_package=Path(os.environ['PLAN_PACKAGE'])
assert os.environ['GITHUB_RUN_ATTEMPT']=='1', 'No automatic publisher rerun'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def git(path):return subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
assert git(package)==os.environ['TOOL_REVISION'] and git(plan_package)==os.environ['PLAN_REVISION']
assert sha(package/'SourceInventory.json')==os.environ['PACKAGE_SHA']
inventory=json.loads((package/'SourceInventory.json').read_bytes())
actual=set()
for path in package.rglob('*'):
    assert not path.is_symlink() and not (hasattr(path,'is_junction') and path.is_junction())
    if path.is_file():actual.add(path.relative_to(package).as_posix())
assert actual==set(inventory['files'])|{'SourceInventory.json'}
for name,wanted in inventory['files'].items():
    f=package/name;assert f.stat().st_size==wanted['bytes'] and sha(f)==wanted['sha256']
assert sha(request)==os.environ['REQUEST_SHA']
subprocess.run([sys.executable,'-B',str(plan_package/'tools/verify_production_pipeline.py'),
    '--package',str(plan_package),'--inventory-sha256',os.environ['PLAN_INVENTORY']],check=True)
sys.path.insert(0,str(package/'tools'))
import production_shard_release_publisher_v2 as v
env=v.core.strict_json(request.read_bytes());q=env['original_request']
_,plan,_=v.p.bound_plan(plan_package/'plan/plan.json',os.environ['PLAN_SHA'],q['source_revision'],'RP0000')
v.validate_envelope(env,plan)
assert q['publisher_revision']==os.environ['TOOL_REVISION'] and q['plan_sha256']==os.environ['PLAN_SHA']
assert q['base_lock_sha256']==os.environ['BASE_SHA']
identity=v.w.actions_context(q,os.environ,v.checked_tool_revision())
work=Path(os.environ['WORK']);work.mkdir()
(work/'evidence').mkdir()
(work/'evidence/approved_envelope.json').write_bytes(request.read_bytes())
(work/'evidence/publisher_identity.json').write_text(json.dumps(identity,indent=2)+'\n')
(work/'evidence/package_inventory.json').write_bytes((package/'SourceInventory.json').read_bytes())
(work/'evidence/plan.json').write_bytes((plan_package/'plan/plan.json').read_bytes())
reader=v.w.ReleaseHTTP(v.w.Journal(work/'origin_journal'),token=os.environ['GH_TOKEN'])
for job in q['jobs']:reader.verify_origin(job)
'''

DOWNLOAD=r'''from pathlib import Path,PurePosixPath
from urllib.error import HTTPError
from urllib.parse import urlsplit
import hashlib,json,os,shutil,stat,sys,time,zipfile
sys.path.insert(0,str(Path(os.environ['PACKAGE'])/'tools'))
import production_shard_release_publisher_v2 as v
work=Path(os.environ['WORK']);q=json.loads(Path(os.environ['REQUEST']).read_bytes())['original_request']
assert q['scope']=='partial' and [j['key'] for j in q['jobs']]==['RP0000','RP3968','RM0000','RM3968']
required=sum(j['archive_bytes']+j['origin_artifact_zip_bytes'] for j in q['jobs'])+512*1024**2+2*1024**3
free=shutil.disk_usage(work).free
(work/'evidence/disk.json').write_text(json.dumps({'actual_free_bytes':free,'required_free_bytes':required})+'\n')
assert free>=required
zips=work/'zips';zips.mkdir();archives=work/'archives';archives.mkdir()
client=v.w.ReleaseHTTP(v.w.Journal(work/'download_journal'),token=os.environ['GH_TOKEN'])
receipts=[]
for job in q['jobs']:
    client.verify_origin(job)
    endpoint='https://api.github.com/repos/'+v.r.REPO+'/actions/artifacts/'+str(job['origin_artifact_id'])+'/zip'
    try:response=client.open(endpoint,'application/vnd.github+json')
    except HTTPError as error:
        assert error.code==302,'Unexpected Actions ZIP response'
        location=error.headers.get('Location','');error.close();u=urlsplit(location)
        assert u.scheme=='https' and u.port in (None,443) and not u.username and not u.password and not u.fragment
        assert u.hostname and (u.hostname.endswith('.blob.core.windows.net') or u.hostname=='productionresultssa0.blob.core.windows.net'
            or u.hostname.endswith('.actions.githubusercontent.com')),'Unexpected Actions ZIP redirect host'
        response=client.open(location,'application/octet-stream',authenticated=False)
    target=zips/(job['key']+'.zip');h=hashlib.sha256();count=0;deadline=time.monotonic()+1200
    with response,target.open('xb') as out:
        assert response.status==200
        while True:
            assert time.monotonic()<deadline
            block=response.read(min(1024**2,job['origin_artifact_zip_bytes']-count+1))
            if not block:break
            count+=len(block);assert count<=job['origin_artifact_zip_bytes'];h.update(block);out.write(block)
    assert count==job['origin_artifact_zip_bytes'] and h.hexdigest()==job['origin_artifact_zip_sha256']
    key=job['key'];member='job/rotating-'+q['source_revision']+'-'+key[1].lower()+'-'+key[2:]+'-0032.tar.xz'
    destination=archives/job['archive'];seen=set();expanded=0
    with zipfile.ZipFile(target) as z:
        infos=z.infolist();assert len(infos)<=5000
        for info in infos:
            raw=info.filename;canonical=raw.rstrip('/');path=PurePosixPath(raw)
            assert canonical and path.as_posix()==canonical and not path.is_absolute()
            assert '..' not in path.parts and '\\' not in canonical and ':' not in canonical
            assert canonical.casefold() not in seen;seen.add(canonical.casefold())
            mode=stat.S_IFMT(info.external_attr>>16);assert mode in (0,stat.S_IFREG,stat.S_IFDIR)
            assert info.file_size>=0;expanded+=info.file_size;assert expanded<=512*1024**2
        info=z.getinfo(member);assert not info.is_dir() and info.file_size==job['archive_bytes']
        h=hashlib.sha256();n=0
        with z.open(info) as source,destination.open('xb') as out:
            while block:=source.read(1024**2):
                n+=len(block);assert n<=job['archive_bytes'];h.update(block);out.write(block)
        assert n==job['archive_bytes'] and h.hexdigest()==job['archive_sha256']
    client.verify_origin(job)
    receipts.append({'key':key,'artifact_id':job['origin_artifact_id'],'zip_bytes':count,
        'zip_sha256':job['origin_artifact_zip_sha256'],'member':member,'archive_bytes':n,
        'archive_sha256':h.hexdigest(),'actual_network_download':True,'new_Lean_calls':0})
    (work/'evidence'/(key+'_download.json')).write_text(json.dumps(receipts[-1],indent=2)+'\n')
assert client.writes==0
(work/'evidence/downloads.json').write_text(json.dumps(receipts,indent=2)+'\n')
'''

POSTCHECK=r'''from pathlib import Path
import hashlib,json,os,sys
sys.path.insert(0,str(Path(os.environ['PACKAGE'])/'tools'))
import production_shard_release_publisher_v2 as v
work=Path(os.environ['WORK']);request=Path(os.environ['REQUEST'])
assert v.c.digest(request)==os.environ['REQUEST_SHA']
q=json.loads(request.read_bytes())['original_request'];pub=work/'publication';journal=pub/'journal'
s=json.loads((journal/'summary.json').read_bytes())
assert s['schema']=='rotating.shard-release-summary.v1' and s['status']=='remote_verified' and s['test_fixture'] is False
assert s['scope']=='partial' and s['source_revision']==q['source_revision'] and s['tag']==q['tag']
assert s['plan_sha256']==q['plan_sha256'] and s['base_lock_sha256']==q['base_lock_sha256']
assert s['request_sha256']==os.environ['REQUEST_SHA'] and s['actual_http_writes']==7
assert s['remote_durability_verified'] is True and s['full_certificate_proved'] is False
assert s['publisher']['revision']==q['publisher_revision'] and s['publisher']['script_sha256']==v.c.digest(v.__file__)
assert s['publisher']['actions']['workflow_revision']==os.environ['GITHUB_SHA']
assert s['publisher']['actions']['run_id']==int(os.environ['GITHUB_RUN_ID'])
assert [x['key'] for x in s['records']]==[j['key'] for j in q['jobs']]
assert {p.name for p in (journal/'records').iterdir()}=={j['key']+'.json' for j in q['jobs']}
for job,item in zip(q['jobs'],s['records']):
    raw=(journal/'records'/(job['key']+'.json')).read_bytes();record=json.loads(raw)
    assert len(raw)==item['record_bytes'] and hashlib.sha256(raw).hexdigest()==item['record_sha256']
    v.p.durable_record(raw,item['record_sha256'],q['source_revision'],job['archive_sha256'],job['archive_bytes'])
    assert record['key']==job['key'] and record['plan_sha256']==q['plan_sha256']
    assert record['base_lock_sha256']==q['base_lock_sha256'] and record['release']['id']==s['release_id']
    assert record['asset']['id']==item['asset_id'] and record['asset']['name']==job['asset_name']
    assert record['publisher']==s['publisher']
    assert item['archive_sha256']==job['archive_sha256'] and item['archive_bytes']==job['archive_bytes']
    assert v.c.digest(work/'archives'/job['archive'])==job['archive_sha256']
assert v.checked_tool_revision()==q['publisher_revision']
print(json.dumps({'status':'four_remote_records_verified','records':4,'actual_http_writes':7,'full_certificate_proved':False}))
'''


def py(script):return "python3 -B - <<'PY'\n"+script.rstrip()+"\nPY\n"


def workflow(revision,package_sha,request_sha,package_relative):
    require(re.fullmatch('OpenProblems/SolitonClassification/[A-Za-z0-9_]+',package_relative),'Unsafe package repository path')
    require(re.fullmatch('[0-9a-f]{40}',revision) and all(re.fullmatch('[0-9a-f]{64}',h) for h in (package_sha,request_sha)),
            'Invalid exact workflow pins')
    def run(name,script,**extra):return {'name':name,'run':script,**extra}
    return {'name':'Publish first four checked rotating-profile shard archives',
        'on':{'workflow_dispatch':{},'push':{'branches':['research/remaining-open-problems'],
            'paths':['.github/workflows/rotating-publish-first-four.yml']}},
        'permissions':{'contents':'write','actions':'read'},
        'concurrency':{'group':'rotating-original-shard-publisher','cancel-in-progress':False},
        'jobs':{'publish':{'runs-on':'ubuntu-24.04','timeout-minutes':60,'defaults':{'run':{'shell':'bash'}},
        'env':{'PYTHONDONTWRITEBYTECODE':'1','TOOL_REVISION':revision,'PACKAGE_SHA':package_sha,'REQUEST_SHA':request_sha,
            'PLAN_REVISION':PLAN_REVISION,'PLAN_INVENTORY':PLAN_INVENTORY,'PLAN_SHA':PLAN_SHA,'BASE_SHA':BASE,
            'PACKAGE':'${{ github.workspace }}/tool-source/'+package_relative,
            'PLAN_PACKAGE':'${{ github.workspace }}/plan-source/OpenProblems/SolitonClassification/ProductionPipeline',
            'REQUEST':'${{ github.workspace }}/request-source/OpenProblems/SolitonClassification/FirstFourReleaseExecution/request.json'},
        'steps':[run('Set isolated publication paths',
            'printf \'WORK=%s/rotating-first-four-release\\n\' "$RUNNER_TEMP" >> "$GITHUB_ENV"\n'),
            {'uses':'actions/checkout@v4','with':{'ref':revision,'path':'tool-source','persist-credentials':False}},
            {'uses':'actions/checkout@v4','with':{'ref':PLAN_REVISION,'path':'plan-source','persist-credentials':False}},
            {'uses':'actions/checkout@v4','with':{'ref':'${{ github.sha }}','path':'request-source','persist-credentials':False}},
            run('Verify pinned tools, unchanged full plan, request and live origins',py(VERIFY),env={'GH_TOKEN':'${{ github.token }}'}),
            run('Download and hash all four original ZIPs and full archive members',py(DOWNLOAD),env={'GH_TOKEN':'${{ github.token }}'}),
            run('Preflight and publish four original archives with full draft and published downloads',
                'python3 -B "$PACKAGE/tools/production_shard_release_publisher_v2.py" --request "$REQUEST" '
                '--request-sha256 "$REQUEST_SHA" --plan "$PLAN_PACKAGE/plan/plan.json" --plan-sha256 "$PLAN_SHA" '
                '--archive-root "$WORK/archives" --output "$WORK/publication" --execute\n',env={'GH_TOKEN':'${{ github.token }}'}),
            run('Validate all four durable records and exact limited scope',py(POSTCHECK)),
            {'name':'Retain requests, original identities and complete journals even on failure','if':'always()',
                'uses':'actions/upload-artifact@v4','with':{
                    'name':'rotating-first-four-publication-${{ github.run_id }}-${{ github.run_attempt }}',
                    'path':'${{ env.WORK }}/evidence\n${{ env.WORK }}/origin_journal\n${{ env.WORK }}/download_journal\n${{ env.WORK }}/publication',
                    'if-no-files-found':'warn','retention-days':30,'compression-level':1}}]}}}


def yaml_lines(value,indent=0):
    pad=' '*indent
    if isinstance(value,dict):
        for key,child in value.items():
            label=json.dumps(key)+':'
            if isinstance(child,(dict,list)) and child:
                yield pad+label;yield from yaml_lines(child,indent+2)
            elif isinstance(child,str) and '\n' in child:
                yield pad+label+' |'
                for line in child.rstrip('\n').split('\n'):yield pad+'  '+line
            else:yield pad+label+' '+json.dumps(child)
    elif isinstance(value,list):
        for child in value:
            if isinstance(child,(dict,list)) and child:
                yield pad+'-';yield from yaml_lines(child,indent+2)
            else:yield pad+'- '+json.dumps(child)
    else:raise TypeError('Structured YAML only')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('tool-revision','package-sha256','package-relative'):p.add_argument('--'+name,required=True)
    for name in ('package','plan','origin-run','origin-artifacts','output'):p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--download-receipt',type=Path,action='append',required=True);a=p.parse_args()
    package=check_package(a.package,a.package_sha256)
    read=lambda path:publisher.core.strict_json(publisher.core.plain_path(path,'file').read_bytes())
    check_evidence(read(a.origin_run),read(a.origin_artifacts),[read(x) for x in a.download_receipt])
    _,plan,_=publisher.p.bound_plan(a.plan,PLAN_SHA,SOURCE,'RP0000')
    env=envelope(a.tool_revision,plan);raw=publisher.core.json_bytes(env);request_sha=hashlib.sha256(raw).hexdigest()
    doc=workflow(a.tool_revision,a.package_sha256,request_sha,a.package_relative)
    for script in (VERIFY,DOWNLOAD,POSTCHECK):ast.parse(script)
    require(all('runner.' not in x for x in doc['jobs']['publish']['env'].values()),'Invalid jobs.env runner context')
    out=publisher.core.fresh_path(a.output);out.mkdir(parents=True)
    (out/'request.json').write_bytes(raw)
    (out/'rotating-publish-first-four.yml').write_text('\n'.join(yaml_lines(doc))+'\n',encoding='utf-8',newline='\n')
    report={'schema':'rotating.first-four-release-preparation.v1','tool_revision':a.tool_revision,
        'publisher_sha256':WRITER,'package_inventory_sha256':a.package_sha256,'plan_sha256':PLAN_SHA,
        'request_sha256':request_sha,'workflow_sha256':sha(out/'rotating-publish-first-four.yml'),
        'source_sha256':sha(__file__),'evidence_inputs':{str(f.resolve()):sha(f) for f in
            [a.origin_run,a.origin_artifacts,*a.download_receipt]},'scope':'partial','requested_archives':4,
        'actual_network_requests':0,'actual_github_writes':0,'actual_archive_preflights_here':0,
        'workflow_executed':False,'release_created':False,'full_certificate_proved':False}
    (out/'preparation_report.json').write_bytes(publisher.core.json_bytes(report))
    print(json.dumps(report))


if __name__=='__main__':main()
