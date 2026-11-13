"""No-network wire fixtures for the new core request and journaled publisher.

Actual downloaded core reports are checked separately; the small upload payload
and HTTP service are explicitly synthetic. No socket or GitHub write is used.
"""
from pathlib import Path
from http.client import HTTPResponse
from urllib.parse import urlsplit,parse_qs
from urllib.error import HTTPError
from unittest.mock import patch
from types import SimpleNamespace
import argparse,copy,hashlib,io,json,os,time
import production_core_release_publisher as w

r,core,c,a=w.r,w.core,w.c,w.adapter


class MemorySocket:
    def __init__(self,data):self.data=data
    def makefile(self,*args,**kwargs):return io.BytesIO(self.data)


class Fixture:
    def __init__(self,q,body,scenario='good'):
        self.q=q;self.body=body;self.scenario=scenario
        self.tag=None;self.release=None;self.asset=None
        self.writes=[];self.requests=[];self.downloads=0;self.published=False

    def open(self,request,timeout):
        assert timeout in (30,90)
        u=urlsplit(request.full_url);assert u.netloc=='127.0.0.1:1'
        method=request.get_method();path=u.path;s=self.scenario;q=self.q
        self.requests.append((method,path))
        headers=dict(request.header_items());status=200;data=None
        if method!='GET':
            self.writes.append((method,path))
            assert method in ('POST','PATCH') and headers.get('Authorization')=='Bearer fixture-token'
            raw=request.data.read() if hasattr(request.data,'read') else request.data
            assert len(raw)==int(headers['Content-length'])
            if s=='ambiguous_tag_creation' and path==w.API+'/git/refs':
                self.tag={'ref':'refs/tags/'+q['tag'],'object':{'type':'commit','sha':q['source_revision']}}
                raise TimeoutError('synthetic ambiguous connection after tag creation')
            if method=='POST' and path==w.API+'/git/refs':
                obj=json.loads(raw);assert obj=={'ref':'refs/tags/'+q['tag'],'sha':q['source_revision']}
                self.tag={'ref':obj['ref'],'object':{'type':'commit','sha':obj['sha']}}
                data=copy.deepcopy(self.tag);status=201
                if s=='wrong_created_tag':data['ref']='refs/tags/wrong'
            elif method=='POST' and path==w.API+'/releases':
                obj=json.loads(raw);assert obj['draft'] is True and obj['target_commitish']==q['source_revision']
                self.release={'id':10,'tag_name':q['tag'],'draft':True,'published_at':None,'assets':[],'immutable':False}
                data=copy.deepcopy(self.release);status=201
                if s=='nonempty_created_draft':data['assets']=[{'id':999}]
            elif method=='POST' and path==w.API+'/releases/10/assets':
                assert parse_qs(u.query)=={'name':[q['archive']['asset_name']]}
                self.body=raw
                self.asset={'id':11,'name':q['archive']['asset_name'],'state':'uploaded',
                    'size':len(raw),'digest':'sha256:'+hashlib.sha256(raw).hexdigest(),
                    'browser_download_url':'https://github.com/'+r.REPO+'/releases/download/'+q['tag']+'/'+q['archive']['asset_name']}
                if s=='starter_asset':self.asset['state']='starter'
                if s=='wrong_upload_digest':self.asset['digest']='sha256:'+'0'*64
                self.release['assets']=[copy.deepcopy(self.asset)]
                if s=='extra_draft_asset':self.release['assets'].append({'id':999,'name':'other'})
                data=copy.deepcopy(self.asset);status=201
            elif method=='PATCH' and path==w.API+'/releases/10':
                assert json.loads(raw)=={'draft':False}
                self.published=True;self.release.update(draft=False,published_at='2026-11-13T00:00:00Z',immutable=True)
                data=copy.deepcopy(self.release)
            else:raise AssertionError('Forbidden synthetic mutation '+method+' '+path)
        elif path.startswith(w.API+'/actions/runs/'):
            data={'id':7,'repository':{'full_name':r.REPO},'head_sha':q['source_revision'],
                  'status':'completed','conclusion':'failure' if s=='failed_origin' else 'success'}
        elif path.startswith(w.API+'/actions/artifacts/'):
            origin=next(x for x in q['origins'].values() if str(x['origin_artifact_id'])==path.rsplit('/',1)[1])
            data={'id':origin['origin_artifact_id'],'expired':s=='expired_origin',
                'workflow_run':{'id':7,'head_sha':q['source_revision']},
                'size_in_bytes':origin['origin_artifact_zip_bytes'],
                'digest':'sha256:'+origin['origin_artifact_zip_sha256']}
        elif path==w.API+'/commits/'+q['source_revision']:
            data={'sha':'0'*40 if s=='wrong_source_commit' else q['source_revision']}
        elif path==w.API+'/git/ref/tags/'+q['tag']:
            data=copy.deepcopy(self.tag)
            if s=='preexisting_tag' and self.tag is None:data={'ref':'refs/tags/'+q['tag']}
            if data is None:status=404
            if data and (s=='tag_moves_during_draft' and self.downloads or s=='tag_moves_after_publish' and self.published):
                data['object']={'type':'commit','sha':'0'*40}
        elif path==w.API+'/releases/tags/'+q['tag']:
            if s=='preexisting_release':data={'id':10}
            else:status=404
        elif path==w.API+'/releases':
            assert parse_qs(u.query)=={'per_page':['100'],'page':['1']}
            data=[{'tag_name':q['tag'],'draft':True}] if s=='existing_draft_collection' else []
        elif path==w.API+'/releases/10':
            data=copy.deepcopy(self.release)
            if s=='wrong_published_membership' and self.published:data['assets']=[]
        elif path==w.API+'/releases/assets/11':
            if headers.get('Accept')=='application/octet-stream':
                self.downloads+=1;data=self.body
                if s=='bad_draft_download' and not self.published:data=data[:-1]
                if s=='bad_published_download' and self.published:data=data+b'!'
                if s=='corrupt_published_download' and self.published:data=bytes([data[0]^1])+data[1:]
            else:
                data=copy.deepcopy(self.asset);data['download_count']=self.downloads
                if s=='changed_published_identity' and self.published and self.downloads>=2:data['id']=12
        else:raise AssertionError('Unexpected fixture GET '+path)
        if status==404:data={'message':'Not Found'}
        raw=data if isinstance(data,bytes) else json.dumps(data).encode()
        wire=('HTTP/1.1 '+str(status)+' Fixture\r\nContent-Length: '+str(len(raw))+'\r\n\r\n').encode()+raw
        response=HTTPResponse(MemorySocket(wire));response.begin()
        if status>=300:raise HTTPError(request.full_url,status,'Fixture',response.headers,response)
        return response


def verify_journal(path):
    previous=None;events=[]
    for f in sorted(path.glob('[0-9][0-9][0-9][0-9][0-9]_*.json')):
        if f.name.endswith('_raw_response.json'):continue
        data=core.strict_json(f.read_bytes())
        assert data['sequence']==len(events) and data['previous_sha256']==previous
        previous=c.digest(f);events.append(data)
        if data['event']=='api_response':
            row=data['data'];response=path/row['file']
            assert response.stat().st_size==row['bytes'] and c.digest(response)==row['sha256']
    return events


def main():
    parser=argparse.ArgumentParser()
    for name in ['output','pack','restore','imports']:parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args();out=core.fresh_path(args.output);out.mkdir(parents=True)
    started=time.perf_counter();cases=[]
    def reject(name,fn):
        try:fn()
        except Exception as error:cases.append({'case':name,'rejected':True,'exception_type':type(error).__name__})
        else:raise AssertionError('Accepted '+name)
    evidence={key:core.strict_json(getattr(args,key).read_bytes()) for key in ('pack','restore','imports')}
    actual=evidence['pack']
    q={'schema':a.SCHEMA,'repository':r.REPO,'test_fixture':True,'layer':'original-core',
        'source_revision':actual['revision'],'publisher_revision':'f'*40,'publisher_sha256':c.digest(w.__file__),
        'helper_sha256':a.helpers(),'tag':'soliton-rotating-'+actual['revision'][:12]+'-core-wire-fixture',
        'title':'SYNTHETIC WIRE FIXTURE ONLY','base_lock_sha256':actual['base_lock_sha256'],
        'source_inventory_sha256':actual['source_inventory_sha256'],'archive':{'file':'exact-core.tar.xz',
            'sha256':actual['archive_sha256'],'bytes':actual['archive_bytes'],
            'asset_name':'SolitonClassification-exact-core-'+actual['archive_sha256'][:16]+'.tar.xz'},
        'evidence':{},'origins':{}}
    # This checks actual downloaded evidence only, without obtaining the 1.3GB core.
    actual_check=a.check_evidence(q,**evidence)
    input_dir=out/'synthetic_inputs';input_dir.mkdir()
    body=b'SYNTHETIC CORE UPLOAD, NOT A LEAN ARCHIVE\n'*4096
    archive=input_dir/'exact-core.tar.xz';archive.write_bytes(body)
    q['archive'].update(sha256=c.digest(archive),bytes=len(body),
        asset_name='SolitonClassification-exact-core-'+c.digest(archive)[:16]+'.tar.xz')
    for key,obj in evidence.items():
        obj=copy.deepcopy(obj);obj['archive_sha256']=c.digest(archive)
        if key=='pack':obj['archive_bytes']=len(body)
        f=input_dir/(key+'.json');f.write_bytes(core.json_bytes(obj))
        q['evidence'][key]={'file':f.name,'sha256':c.digest(f),'bytes':f.stat().st_size}
    for i,key in enumerate(('archive','producer_evidence','consumer_evidence'),20):
        q['origins'][key]={'origin_run_id':7,'origin_head_sha':q['source_revision'],'origin_artifact_id':i,
            'origin_artifact_zip_sha256':str(i)[0]*64,'origin_artifact_zip_bytes':123+i}
    request=out/'request.json';request.write_bytes(core.json_bytes(q))
    ctx=a.prepare(request,c.digest(request),input_dir,c.digest(w.__file__),True)
    reject('fixture_blocked_in_production',lambda:a.validate_request(q,c.digest(w.__file__)))
    for name,change in [('wrong_layer',lambda x:x.update(layer='original-data')),
        ('wrong_repo',lambda x:x.update(repository='other/repo')),
        ('wrong_publisher',lambda x:x.update(publisher_sha256='0'*64)),
        ('wrong_helper',lambda x:x.update(helper_sha256={})),
        ('wrong_archive_path',lambda x:x['archive'].update(file='../core.tar.xz')),
        ('asset_2gib',lambda x:x['archive'].update(bytes=2*1024**3)),
        ('duplicate_origins',lambda x:x['origins']['consumer_evidence'].update(x['origins']['archive'])),
        ('mixed_run',lambda x:x['origins']['consumer_evidence'].update(origin_run_id=8))]:
        bad=copy.deepcopy(q);change(bad)
        reject(name,lambda bad=bad:a.validate_request(bad,c.digest(w.__file__),True))
    for name,key,change in [('no_private_audit','imports',lambda x:x.update(actual_fresh_private_audit=False)),
        ('wrong_counts','imports',lambda x:x['modules'][0].update(private_declarations=330)),
        ('failed_actual_import','imports',lambda x:x['modules'][1].update(exit_code=1)),
        ('false_base_check','restore',lambda x:x.update(complete_restored_base_twice_checked=False)),
        ('wrong_archive_hash','pack',lambda x:x.update(archive_sha256='0'*64))]:
        bad=copy.deepcopy(evidence);change(bad[key])
        actual_q=copy.deepcopy(q);actual_q['archive']={'sha256':actual['archive_sha256'],'bytes':actual['archive_bytes']}
        reject(name,lambda bad=bad:a.check_evidence(actual_q,**bad))
    env={'GITHUB_ACTIONS':'true','GITHUB_REPOSITORY':r.REPO,'GITHUB_SHA':'e'*40,
         'GITHUB_EVENT_NAME':'push','GITHUB_RUN_ID':'1'}
    reject('no_real_execution_of_fixture',lambda:w.actions_context(q,env,q['publisher_revision']))
    production=copy.deepcopy(q);production['test_fixture']=False
    for name,change in [('local_not_actions',lambda x:x.update(GITHUB_ACTIONS='false')),
        ('invalid_workflow_sha',lambda x:x.update(GITHUB_SHA='not-a-commit')),
        ('pull_request_event',lambda x:x.update(GITHUB_EVENT_NAME='pull_request'))]:
        bad=dict(env);change(bad);reject(name,lambda bad=bad:w.actions_context(production,bad,q['publisher_revision']))
    reject('wrong_actual_tool_revision',lambda:w.actions_context(production,env,'0'*40))
    identity=w.actions_context(production,env,q['publisher_revision'])
    assert identity['tool_revision']!=identity['workflow_revision']
    git_calls=[]
    def fake_git(command,**kwargs):
        git_calls.append(command)
        assert kwargs['check'] is True and kwargs['timeout']==30
        assert all(not k.startswith('GIT_') for k in kwargs['env'])
        operation=command[3:]
        if operation==['rev-parse','--show-toplevel']:data=str(Path(w.__file__).resolve().parent).encode()
        elif operation==['rev-parse','HEAD']:data=q['publisher_revision'].encode()
        elif operation==['show','HEAD:'+Path(w.__file__).name]:data=Path(w.__file__).read_bytes()
        else:raise AssertionError('Unexpected Git command')
        return SimpleNamespace(stdout=data)
    with patch.object(w.subprocess,'run',side_effect=fake_git):
        assert w.checked_tool_revision()==q['publisher_revision']
    def wrong_blob(command,**kwargs):
        result=fake_git(command,**kwargs)
        if command[3]=='show':result.stdout+=b'changed'
        return result
    with patch.object(w.subprocess,'run',side_effect=wrong_blob):
        reject('uncommitted_publisher_blob',w.checked_tool_revision)
    outcomes=[]
    for scenario in ['good','failed_origin','expired_origin','wrong_source_commit','preexisting_tag',
        'preexisting_release','existing_draft_collection','ambiguous_tag_creation','wrong_created_tag',
        'nonempty_created_draft','starter_asset','wrong_upload_digest','extra_draft_asset','bad_draft_download',
        'tag_moves_during_draft','tag_moves_after_publish','bad_published_download','corrupt_published_download',
        'wrong_published_membership','changed_published_identity']:
        journal=w.Journal(out/scenario);client=w.ReleaseHTTP(journal,api='http://127.0.0.1:1',token='fixture-token',fixture=True)
        fixture=Fixture(q,body,scenario);client.opener=fixture
        if scenario=='good':
            result=w.publish(ctx,client,journal)
            assert result['status']=='fixture_only' and result['remote_durability_verified'] is False
            assert fixture.downloads==2 and len(fixture.writes)==4
        else:reject(scenario,lambda:w.publish(ctx,client,journal))
        events=verify_journal(journal.root)
        assert events[-1]['event']==('finished' if scenario=='good' else 'failed')
        assert all(method in ('POST','PATCH') for method,path in fixture.writes)
        if scenario in ('failed_origin','expired_origin','wrong_source_commit','preexisting_tag',
                        'preexisting_release','existing_draft_collection'):assert not fixture.writes
        if scenario=='ambiguous_tag_creation':assert len(fixture.writes)==1 and fixture.tag is not None
        if scenario in ('starter_asset','wrong_upload_digest','extra_draft_asset','bad_draft_download',
                        'tag_moves_during_draft'):assert not fixture.published
        assert not any('DELETE'==method for method,path in fixture.requests)
        outcomes.append({'scenario':scenario,'writes':len(fixture.writes),'binary_downloads':fixture.downloads,
            'journal_events':len(events),'published_in_memory':fixture.published})
    # Original input remains retained and untouched, including on failed writes.
    a.recheck(ctx,c.digest(w.__file__))
    report={'schema':'rotating.core-release-wire-fixture.v1','status':'checked','actual_core_evidence_check':actual_check,
        'fixture_upload_is_real_core':False,'actual_github_requests':0,'actual_github_writes':0,
        'actual_network_sockets':0,'actual_lean_runs':0,'full_certificate_proved':False,
        'actual_platform':os.name,'journal_directory_fsync_exercised':os.name=='posix',
        'power_loss_simulated':False,'tool_git_identity_test':'mocked process responses, no actual checkout assertion',
        'input_actual_evidence_sha256':{k:c.digest(getattr(args,k)) for k in ('pack','restore','imports')},
        'sources_sha256':{Path(x).name:c.digest(x) for x in (__file__,w.__file__,a.__file__)},
        'cases':cases,'scenarios':outcomes,'wall_seconds':time.perf_counter()-started}
    (out/'review.json').write_bytes(core.json_bytes(report))
    print(json.dumps({'status':'checked','rejections':len(cases),'scenarios':len(outcomes),
        'actual_github_writes':0,'actual_network_sockets':0,'wall_seconds':report['wall_seconds']}),flush=True)


if __name__=='__main__':main()
