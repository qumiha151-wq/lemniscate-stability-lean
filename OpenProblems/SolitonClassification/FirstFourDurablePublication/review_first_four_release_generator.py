"""Local structural/runtime fixtures only. No network, release or Lean execution."""
from pathlib import Path
from urllib.error import HTTPError
import ast,copy,hashlib,io,json,os,stat,sys,time,zipfile
import prepare_first_four_shard_release as g

root=Path(__file__).resolve().parents[1]
out=root/'first_four_release_generator_review_v1';out.mkdir(exist_ok=False)
report={'schema':'rotating.first-four-release-generator-review.v1','status':'running',
    'source_sha256':g.sha(g.__file__),'test_sha256':g.sha(__file__),'actual_network_requests':0,
    'actual_github_writes':0,'new_Lean_calls':0,'actual_archive_preflights':0,
    'actual_release_created':False,'full_certificate_proved':False,'rejections':[]}
def reject(name,fn):
    try:fn()
    except (AssertionError,ValueError,KeyError,HTTPError,zipfile.BadZipFile) as e:
        report['rejections'].append({'case':name,'type':type(e).__name__});return
    raise AssertionError('Expected rejection: '+name)
read=lambda p:json.loads(Path(p).read_bytes())
r=read(root/'performance/FirstProductionV3FinalRun.json')
a=read(root/'performance/FirstProductionV3FinalArtifacts.json')
receipts=[read(root.parent/'first_production_v3_publication/first_three_downloads/download_verification.json'),
          read(root.parent/'first_production_v3_publication/fourth_download/download_verification.json')]
g.check_evidence(r,a,receipts)
for field,value in [('id',1),('head_sha','0'*40),('run_attempt',2),('status','in_progress'),('conclusion','failure')]:
    bad=copy.deepcopy(r);bad[field]=value;reject('origin_'+field,lambda:g.check_evidence(bad,a,receipts))
for field,value in [('expired',True),('size_in_bytes',1),('digest','sha256:'+'0'*64)]:
    bad=copy.deepcopy(a);next(x for x in bad['artifacts'] if x['id']==g.ROWS[0][1])[field]=value
    reject('artifact_'+field,lambda:g.check_evidence(r,bad,receipts))
reject('missing_receipt',lambda:g.check_evidence(r,a,[receipts[0]]))
reject('duplicate_receipt',lambda:g.check_evidence(r,a,[receipts[0],receipts[0]]))
bad=copy.deepcopy(receipts);bad[0][0]['files'][g.archive_member('RP0000')]['sha256']='0'*64
reject('archive_receipt_hash',lambda:g.check_evidence(r,a,bad))
plan_path=root/'production_pipeline_package_v1/plan/plan.json'
_,plan,_=g.publisher.p.bound_plan(plan_path,g.PLAN_SHA,g.SOURCE,'RP0000')
actual_p='eab61f0d4210d8e05d27a8b5a55f2bf3df34140f'
envelope=g.envelope(actual_p,plan)
for p in ('','P','0'*39,'x'*40,None):reject('invalid_P_'+str(p),lambda:g.envelope(p,plan))
for path in ('../../escape','OpenProblems/SolitonClassification/../Bad','OpenProblems/SolitonClassification/Bad/name'):
    reject('unsafe_package_'+path,lambda:g.workflow(actual_p,'0'*64,'1'*64,path))
doc=g.workflow(actual_p,'0'*64,'1'*64,'OpenProblems/SolitonClassification/ShardReleaseToolsV2')
assert all('runner.' not in v for v in doc['jobs']['publish']['env'].values())
assert doc['permissions']=={'contents':'write','actions':'read'}
assert doc['concurrency']['cancel-in-progress'] is False
assert [x['with']['ref'] for x in doc['jobs']['publish']['steps'] if x.get('uses')=='actions/checkout@v4']==[
    actual_p,g.PLAN_REVISION,'${{ github.sha }}']
assert doc['jobs']['publish']['steps'][-1]['if']=='always()'
assert '/zips' not in doc['jobs']['publish']['steps'][-1]['with']['path']
for s in (g.VERIFY,g.DOWNLOAD,g.POSTCHECK):ast.parse(s)
report['embedded_Python_ASTs']=3
report['actual_saved_origin_and_four_download_receipts_checked']=True
report['workflow_rendered_only_in_memory']=True

class Response(io.BytesIO):
    status=200


def download_case(name,mode):
    case=out/name;case.mkdir();work=case/'work';work.mkdir();(work/'evidence').mkdir()
    q=copy.deepcopy(envelope['original_request']);payloads={};access=[]
    for i,job in enumerate(q['jobs']):
        payload=('SIMULATED NON-LEAN ARCHIVE '+job['key']).encode()
        job['archive_bytes']=len(payload);job['archive_sha256']=hashlib.sha256(payload).hexdigest()
        stream=io.BytesIO()
        with zipfile.ZipFile(stream,'w') as z:
            member=g.archive_member(job['key'])
            if mode=='path' and i==0:z.writestr('../escape',b'x')
            if mode=='duplicate' and i==0:z.writestr(member.upper(),b'x')
            if mode=='link' and i==0:
                info=zipfile.ZipInfo('symlink');info.create_system=3;info.external_attr=(stat.S_IFLNK|0o777)<<16
                z.writestr(info,b'x')
            z.writestr(member,payload)
        raw=stream.getvalue();payloads[job['origin_artifact_id']]=raw
        job['origin_artifact_zip_bytes']=len(raw);job['origin_artifact_zip_sha256']=hashlib.sha256(raw).hexdigest()
        if mode=='zip_hash' and i==0:job['origin_artifact_zip_sha256']='0'*64
        if mode=='archive_hash' and i==0:job['archive_sha256']='0'*64
    request=case/'request.json';request.write_bytes(g.publisher.core.json_bytes({'original_request':q}))
    class FakeClient:
        writes=0
        def __init__(self,*args,**kwargs):pass
        def verify_origin(self,job):access.append(('origin',job['key']));return True
        def open(self,url,accept,authenticated=True):
            if url.startswith('https://api.github.com/'):
                assert authenticated;aid=int(url.split('/')[-2]);access.append(('api',aid))
                host='example.blob.core.windows.net' if mode!='foreign_redirect' else 'example.invalid'
                raise HTTPError(url,302,'Synthetic redirect',{'Location':'https://'+host+'/'+str(aid)},None)
            assert authenticated is False;aid=int(url.rsplit('/',1)[1]);access.append(('signed_without_token',aid))
            return Response(payloads[aid])
    old=g.publisher.w.ReleaseHTTP;env=os.environ.copy()
    try:
        g.publisher.w.ReleaseHTTP=FakeClient
        os.environ.update({'WORK':str(work.resolve()),'REQUEST':str(request.resolve()),'PACKAGE':str(case.resolve()),'GH_TOKEN':'SYNTHETIC_NOT_A_TOKEN'})
        exec(compile(g.DOWNLOAD,'<download runtime fixture>','exec'),{})
    finally:
        g.publisher.w.ReleaseHTTP=old;os.environ.clear();os.environ.update(env)
    assert len([x for x in access if x[0]=='signed_without_token'])==4
    assert len(read(work/'evidence/downloads.json'))==4
    assert len(list((work/'zips').glob('*.zip')))==4
    return {'mode':mode,'synthetic_ZIP_downloads':4,'synthetic_archive_members':4,'actual_network':False}

report['positive_runtime_download_fixture']=download_case('good','good')
for mode in ('path','duplicate','link','zip_hash','archive_hash','foreign_redirect'):
    reject('download_'+mode,lambda m=mode:download_case(m,m))
env=os.environ.copy()
try:
    os.environ.update({'PACKAGE':'unused','REQUEST':'unused','PLAN_PACKAGE':'unused','GITHUB_RUN_ATTEMPT':'2'})
    reject('runtime_rerun_before_io',lambda:exec(compile(g.VERIFY,'<rerun fixture>','exec'),{}))
finally:os.environ.clear();os.environ.update(env)
assert g.sha(g.__file__)==report['source_sha256']
report['status']='checked';report['independent_YAML_parser_run']=False
(out/'report.json').write_bytes(g.publisher.core.json_bytes(report))
print(json.dumps({'status':'checked','rejections':len(report['rejections']),'report_sha256':g.sha(out/'report.json'),
    'actual_network_requests':0,'actual_github_writes':0,'new_Lean_calls':0}))
