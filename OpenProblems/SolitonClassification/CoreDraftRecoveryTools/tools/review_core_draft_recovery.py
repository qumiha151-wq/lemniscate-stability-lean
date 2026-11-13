"""Actual failed-journal preflight plus explicitly synthetic no-network wire tests."""
from pathlib import Path
from urllib.parse import urlsplit,parse_qs
from http.client import HTTPResponse
from urllib.error import HTTPError
from unittest.mock import patch
from types import SimpleNamespace
import argparse,copy,hashlib,io,json,time
import production_core_draft_recovery as w

core,c,r=w.core,w.c,w.r


class MemorySocket:
    def __init__(self,data):self.data=data
    def makefile(self,*args,**kwargs):return io.BytesIO(self.data)


def pin(path):return {'sha256':c.digest(path),'bytes':path.stat().st_size}


def request_for(inputs,fixture):
    original=core.strict_json((inputs/'original_request.json').read_bytes())
    return {'schema':w.SCHEMA,'repository':r.REPO,'test_fixture':fixture,
        'publisher_revision':'e'*40,'publisher_sha256':c.digest(w.__file__),'helper_sha256':w.helpers(),
        'release_id':443789076,'asset_id':742149339,'original_request':pin(inputs/'original_request.json'),
        'original_journal':{p.name:pin(p) for p in sorted((inputs/'original_journal').iterdir())},
        'original_journal_last_sha256':c.digest(inputs/'original_journal/00025_failed.json'),
        'failed_execution':{'run_id':43360690582,'run_attempt':1,'job_id':131673215746,
            'workflow_revision':'9e5bca3af5cff67ac476196fb19c56752bb825fd','artifact_id':14007623591,
            'artifact_zip_sha256':'b671403fa6d15fa70755c5612333f3ff1d1947ad787070760de1f01598e73068',
            'artifact_zip_bytes':98455}}


def actual_inputs(source,out):
    out.mkdir();(out/'original_journal').mkdir();(out/'evidence').mkdir()
    (out/'original_request.json').write_bytes((source/'evidence/approved_request.json').read_bytes())
    for p in (source/'journal').iterdir():(out/'original_journal'/p.name).write_bytes(p.read_bytes())
    for key in ('pack','restore','imports'):
        (out/'evidence'/(key+'.json')).write_bytes((source/'inputs'/(key+'.json')).read_bytes())


def synthetic_inputs(source,out,body):
    actual_inputs(source,out)
    original=core.strict_json((out/'original_request.json').read_bytes());old_archive=copy.deepcopy(original['archive'])
    digest=hashlib.sha256(body).hexdigest();name='SolitonClassification-exact-core-'+digest[:16]+'.tar.xz'
    original['test_fixture']=True
    original['archive'].update(sha256=digest,bytes=len(body),asset_name=name)
    for key,p in original['evidence'].items():
        path=out/'evidence'/p['file'];data=core.strict_json(path.read_bytes());data['archive_sha256']=digest
        if key=='pack':data['archive_bytes']=len(body)
        path.write_bytes(core.json_bytes(data));p.update(pin(path))
    (out/'original_request.json').write_bytes(core.json_bytes(original))
    journal=out/'original_journal'
    def transform(obj):
        if isinstance(obj,list):return [transform(x) for x in obj]
        if not isinstance(obj,dict):return obj
        result={k:transform(v) for k,v in obj.items()}
        for key,value in list(result.items()):
            if value==old_archive['sha256']:result[key]=digest
            elif value=='sha256:'+old_archive['sha256']:result[key]='sha256:'+digest
            elif value==old_archive['asset_name']:result[key]=name
            elif isinstance(value,str) and value.endswith('/'+old_archive['asset_name']):
                result[key]=value[:-len(old_archive['asset_name'])]+name
            elif type(value) is int and value==old_archive['bytes']:result[key]=len(body)
        return result
    for path in journal.glob('*_raw_response.json'):
        path.write_bytes(core.json_bytes(transform(core.strict_json(path.read_bytes()))))
    previous=None
    for path in sorted(journal.glob('*.json')):
        if path.name.endswith('_raw_response.json'):continue
        data=transform(core.strict_json(path.read_bytes()));data['previous_sha256']=previous
        if data['event']=='api_response':data['data'].update(pin(journal/data['data']['file']))
        if data['event']=='started':data['data'].update(test_fixture=True,
            request_sha256=c.digest(out/'original_request.json'))
        path.write_bytes(core.json_bytes(data));previous=c.digest(path)


class Fixture:
    def __init__(self,ctx,body,scenario):
        self.ctx=ctx;self.body=body;self.scenario=scenario;self.downloads=0;self.writes=[];self.requests=[]
        self.release=copy.deepcopy(ctx['original_release']);self.asset=copy.deepcopy(ctx['original_asset'])
        self.published=False;self.mutated_after_download=False

    def open(self,request,timeout):
        u=urlsplit(request.full_url);assert u.netloc=='127.0.0.1:1';assert timeout in (30,90)
        method=request.get_method();headers=dict(request.header_items());path=u.path
        self.requests.append((method,path));s=self.scenario;q=self.ctx['request'];o=self.ctx['original'];f=q['failed_execution']
        if method!='GET':
            self.writes.append((method,path));assert method=='PATCH' and path==w.API+'/releases/'+str(q['release_id'])
            assert json.loads(request.data)=={'draft':False} and headers.get('Authorization')=='Bearer fixture-token'
            assert len(request.data)==int(headers['Content-length'])
            self.published=True;self.release.update(draft=False,published_at='2026-11-13T04:00:00Z',immutable=True,
                html_url='https://github.com/'+r.REPO+'/releases/tag/'+o['tag'])
            self.asset['browser_download_url']='https://github.com/'+r.REPO+'/releases/download/'+o['tag']+'/'+o['archive']['asset_name']
            self.release['assets']=[copy.deepcopy(self.asset)]
            if s=='ambiguous_patch':raise TimeoutError('synthetic publish response lost')
            data=copy.deepcopy(self.release)
        elif path==w.API+'/actions/runs/'+str(f['run_id']):
            data={'id':f['run_id'],'repository':{'full_name':r.REPO},'head_sha':f['workflow_revision'],
                'run_attempt':f['run_attempt'],'status':'completed','conclusion':'success' if s=='failed_origin_changed' else 'failure'}
        elif path==w.API+'/actions/jobs/'+str(f['job_id']):
            data={'id':f['job_id'],'run_id':f['run_id'],'head_sha':f['workflow_revision'],
                'status':'completed','conclusion':'failure'}
        elif path==w.API+'/actions/artifacts/'+str(f['artifact_id']):
            data={'id':f['artifact_id'],'expired':s=='journal_artifact_expired',
                'workflow_run':{'id':f['run_id'],'head_sha':f['workflow_revision']},
                'size_in_bytes':f['artifact_zip_bytes'],'digest':'sha256:'+f['artifact_zip_sha256']}
        elif path.startswith(w.API+'/actions/runs/'):
            run=int(path.rsplit('/',1)[1]);data={'id':run,'repository':{'full_name':r.REPO},
                'head_sha':o['source_revision'],'status':'completed','conclusion':'success'}
        elif path.startswith(w.API+'/actions/artifacts/'):
            origin=next(x for x in o['origins'].values() if str(x['origin_artifact_id'])==path.rsplit('/',1)[1])
            data={'id':origin['origin_artifact_id'],'expired':False,
                'workflow_run':{'id':origin['origin_run_id'],'head_sha':o['source_revision']},
                'size_in_bytes':origin['origin_artifact_zip_bytes'],'digest':'sha256:'+origin['origin_artifact_zip_sha256']}
        elif path==w.API+'/git/ref/tags/'+o['tag']:
            data={'ref':'refs/tags/'+o['tag'],'object':{'type':'commit','sha':o['source_revision']}}
            if s=='wrong_tag' or (s=='tag_moves_after_draft' and self.downloads):data['object']['sha']='0'*40
        elif path==w.API+'/releases/'+str(q['release_id']):
            data=copy.deepcopy(self.release)
            if s=='already_published':data.update(draft=False,published_at='2026-11-13T03:00:00Z')
            if s=='changed_body':data['body']='changed'
            if s=='changed_title':data['name']='changed'
            if s=='foreign_release_api':data['url']='https://api.github.com/repos/other/repo/releases/'+str(q['release_id'])
            if s=='draft_foreign_html':data['html_url']='https://example.com/releases/tag/'+o['tag']
            if s=='draft_asset_extra':data['assets'].append(copy.deepcopy(self.asset))
            if s=='published_keeps_draft_slug' and self.published:data['html_url']=self.ctx['original_release']['html_url']
            if s=='changed_published_body' and self.published:data['body']='changed'
        elif path==w.API+'/releases/'+str(q['release_id'])+'/assets':
            assert parse_qs(u.query)=={'per_page':['100'],'page':['1']}
            data=[copy.deepcopy(self.asset)]
            if s=='asset_list_extra':data.append(copy.deepcopy(self.asset))
            if s=='asset_list_empty':data=[]
            if s=='asset_list_wrong_id':data[0]['id']+=1
        elif path==w.API+'/releases/assets/'+str(q['asset_id']):
            if headers.get('Accept')=='application/octet-stream':
                self.downloads+=1;data=self.body
                if s=='short_draft_bytes' and not self.published:data=data[:-1]
                if s=='corrupt_draft_bytes' and not self.published:data=bytes([data[0]^1])+data[1:]
                if s=='long_published_bytes' and self.published:data=data+b'!'
                if s=='corrupt_published_bytes' and self.published:data=bytes([data[0]^1])+data[1:]
                if s=='identity_moves_after_published_download' and self.published:
                    self.asset['id']+=1;self.release['assets']=[copy.deepcopy(self.asset)]
            else:
                data=copy.deepcopy(self.asset);data['download_count']=self.downloads
                if s=='draft_asset_url_mismatch' and not self.published:
                    data['browser_download_url']='https://github.com/'+r.REPO+'/releases/download/'+o['tag']+'/'+o['archive']['asset_name']
                if s=='wrong_asset_digest':data['digest']='sha256:'+'0'*64
                if s=='wrong_asset_state':data['state']='starter'
        else:raise AssertionError('Unexpected GET '+path)
        raw=data if isinstance(data,bytes) else json.dumps(data).encode()
        wire=('HTTP/1.1 200 Fixture\r\nContent-Length: '+str(len(raw))+'\r\n\r\n').encode()+raw
        response=HTTPResponse(MemorySocket(wire));response.begin();return response


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--original',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    out=core.fresh_path(args.output);out.mkdir(parents=True);started=time.perf_counter();cases=[]
    def reject(name,fn):
        try:fn()
        except Exception as e:cases.append({'name':name,'rejected':True,'exception_type':type(e).__name__})
        else:raise AssertionError('Accepted '+name)
    actual=out/'actual_inputs';actual_inputs(args.original,actual);aq=request_for(actual,False)
    ap=out/'actual_request.json';ap.write_bytes(core.json_bytes(aq));actual_ctx=w.prepare(ap,c.digest(ap),actual)
    body=b'SYNTHETIC CORE DRAFT RECOVERY; NO REAL LEAN CONTENT\n'*4096
    inputs=out/'synthetic_inputs';synthetic_inputs(args.original,inputs,body)
    q=request_for(inputs,True);qp=out/'synthetic_request.json';qp.write_bytes(core.json_bytes(q))
    ctx=w.prepare(qp,c.digest(qp),inputs,True)
    reject('fixture_production_boundary',lambda:w.prepare(qp,c.digest(qp),inputs))
    for name,change in [('wrong_script',lambda x:x.update(publisher_sha256='0'*64)),
        ('wrong_helpers',lambda x:x.update(helper_sha256={})),('invalid_release',lambda x:x.update(release_id=True)),
        ('unsafe_journal',lambda x:x['original_journal'].update({'../outside.json':next(iter(x['original_journal'].values()))}))]:
        bad=copy.deepcopy(q);change(bad);reject(name,lambda bad=bad:w.validate_request(bad,True))
    scenarios=['good','failed_origin_changed','journal_artifact_expired','wrong_tag','already_published','changed_body',
        'changed_title','foreign_release_api','draft_foreign_html','draft_asset_extra','asset_list_extra','asset_list_empty',
        'asset_list_wrong_id','draft_asset_url_mismatch','wrong_asset_digest','wrong_asset_state','short_draft_bytes',
        'corrupt_draft_bytes','tag_moves_after_draft','ambiguous_patch','published_keeps_draft_slug','changed_published_body',
        'long_published_bytes','corrupt_published_bytes','identity_moves_after_published_download']
    outcomes=[]
    for scenario in scenarios:
        journal=w.old.Journal(out/scenario);client=w.RecoveryHTTP(journal,q['release_id'],api='http://127.0.0.1:1',token='fixture-token',fixture=True)
        fixture=Fixture(ctx,body,scenario);client.opener=fixture
        if scenario=='good':
            result=w.recover(ctx,client,journal)
            assert result['status']=='fixture_only' and result['remote_durability_verified'] is False
            assert result['actual_http_writes']==1 and fixture.downloads==2
        else:reject(scenario,lambda:w.recover(ctx,client,journal))
        import review_core_release_publisher as old_test
        events=old_test.verify_journal(journal.root)
        assert events[-1]['event']==('finished' if scenario=='good' else 'failed')
        assert len(fixture.writes)<=1 and all(method=='PATCH' for method,path in fixture.writes)
        if scenarios.index(scenario)<scenarios.index('ambiguous_patch') and scenario!='good':assert not fixture.writes
        if scenario!='good':assert not (journal.root/'result.json').exists()
        outcomes.append({'scenario':scenario,'writes':len(fixture.writes),'binary_downloads':fixture.downloads,
            'published_in_memory':fixture.published})
    journal=w.old.Journal(out/'write_boundary');client=w.RecoveryHTTP(journal,q['release_id'],api='http://127.0.0.1:1',token='fixture-token',fixture=True)
    for method,path,payload in [('POST',w.API+'/releases',{}),('DELETE',w.API+'/releases/'+str(q['release_id']),None),
        ('PATCH',w.API+'/releases/'+str(q['release_id']+1),{'draft':False}),
        ('PATCH',w.API+'/releases/'+str(q['release_id']),{'draft':False,'name':'changed'})]:
        reject('forbidden_write_'+method+'_'+str(len(cases)),lambda:client.mutate(method,path,payload))
    client.writes=1
    reject('second_patch',lambda:client.mutate('PATCH',w.API+'/releases/'+str(q['release_id']),{'draft':False}))
    # Check the deployed sibling performance/reference.py path and every actual
    # helper blob through mocked Git process replies; this is not a real checkout.
    directory=Path(w.__file__).resolve().parent;top=directory.parent;git_calls=[]
    def fake_git(command,**kwargs):
        assert kwargs['check'] is True and kwargs['timeout']==30
        assert all(not key.startswith('GIT_') for key in kwargs['env'])
        op=command[3:];git_calls.append(op)
        if op==['rev-parse','--show-toplevel']:data=str(top).encode()
        elif op==['rev-parse','HEAD']:data=q['publisher_revision'].encode()
        elif len(op)==2 and op[0]=='show':data=(top/op[1].removeprefix('HEAD:')).read_bytes()
        else:raise AssertionError(op)
        return SimpleNamespace(stdout=data)
    with patch.object(w.subprocess,'run',side_effect=fake_git):
        assert w.checked_tool_revision()==q['publisher_revision']
    assert ['show','HEAD:performance/reference.py'] in git_calls
    assert len([x for x in git_calls if x[0]=='show'])==len(w.helpers())+1
    def changed_blob(command,**kwargs):
        result=fake_git(command,**kwargs)
        if command[-1]=='HEAD:performance/reference.py':result.stdout+=b'changed'
        return result
    with patch.object(w.subprocess,'run',side_effect=changed_blob):
        reject('helper_not_actual_committed_blob',w.checked_tool_revision)
    runtime_env={'GITHUB_ACTIONS':'true','GITHUB_REPOSITORY':r.REPO,'GITHUB_SHA':'a'*40,
        'GITHUB_EVENT_NAME':'push','GITHUB_RUN_ID':'99','GITHUB_RUN_ATTEMPT':'2'}
    runtime_journal=w.old.Journal(out/'rerun_boundary')
    runtime_client=w.RecoveryHTTP(runtime_journal,aq['release_id'],token='unused-token')
    reject('workflow_rerun',lambda:w.recover(actual_ctx,runtime_client,runtime_journal,runtime_env))
    pinned_path=inputs/'evidence/pack.json';pinned_bytes=pinned_path.read_bytes()
    pinned_path.write_bytes(pinned_bytes+b' ')
    reject('pinned_input_mutated',lambda:w.recheck(ctx,c.digest(w.__file__)))
    pinned_path.write_bytes(pinned_bytes)
    w.recheck(actual_ctx,c.digest(w.__file__));w.recheck(ctx,c.digest(w.__file__))
    report={'schema':'rotating.core-draft-recovery-wire-review.v1','status':'checked',
        'actual_original_journal_request_and_core_reports_checked':True,
        'actual_original_request_sha256':aq['original_request']['sha256'],
        'actual_original_journal_last_sha256':aq['original_journal_last_sha256'],
        'source_sha256':{Path(x).name:c.digest(x) for x in (__file__,w.__file__,w.url_protocol.__file__)},
        'actual_github_requests':0,'actual_github_writes':0,'actual_network_sockets':0,'actual_lean_runs':0,
        'synthetic_payload_is_real_core':False,'full_certificate_proved':False,
        'tool_git_identity_test':'mocked Git process replies, not an actual committed checkout',
        'cases':cases,'scenarios':outcomes,'wall_seconds':time.perf_counter()-started}
    (out/'review.json').write_bytes(core.json_bytes(report))
    print(json.dumps({'status':'checked','rejections':len(cases),'scenarios':len(outcomes),
        'actual_github_writes':0,'wall_seconds':report['wall_seconds']}),flush=True)


if __name__=='__main__':main()
