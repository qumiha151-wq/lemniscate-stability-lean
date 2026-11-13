"""Separately reviewed recovery of one pinned existing core draft.

No creation, upload, deletion, tag change, retry, or published-state resume.
An externally pinned failed journal and original request remain unchanged.
Only one PATCH {draft:false} is possible, after a complete asset-ID download.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess
import production_core_release_publisher as old
import production_release_url_protocol as url_protocol

adapter,r,c,core,require=old.adapter,old.r,old.c,old.core,old.require
API=old.API
SCHEMA='rotating.core-draft-recovery-request.v1'
ASSET_KEYS=['id','url','name','state','size','digest','browser_download_url']
RELEASE_KEYS=['id','url','html_url','tag_name','target_commitish','name','body',
              'draft','prerelease','published_at','immutable']


def helpers():
    return {**adapter.helpers(),Path(old.__file__).name:c.digest(old.__file__),
            Path(url_protocol.__file__).name:c.digest(url_protocol.__file__)}


def selected(value,keys):
    return {k:value.get(k) for k in keys}


def check_pin(row):
    require(set(row)=={'sha256','bytes'} and isinstance(row['sha256'],str)
        and c.SHA.fullmatch(row['sha256']) and type(row['bytes']) is int
        and 0<row['bytes']<=16*1024**2,'Invalid small input pin')


def validate_request(q,allow_fixture=False):
    require(set(q)=={'schema','repository','test_fixture','publisher_revision','publisher_sha256',
        'helper_sha256','release_id','asset_id','original_request','original_journal',
        'original_journal_last_sha256','failed_execution'},'Wrong recovery request fields')
    require(q['schema']==SCHEMA and q['repository']==r.REPO,'Wrong recovery scope')
    require(type(q['test_fixture']) is bool and (not q['test_fixture'] or allow_fixture),
        'Fixture recovery forbidden in production')
    require(isinstance(q['publisher_revision'],str) and core.REVISION.fullmatch(q['publisher_revision'])
        and q['publisher_sha256']==c.digest(__file__) and q['helper_sha256']==helpers(),
        'Recovery tool implementation differs')
    for k in ['release_id','asset_id']:
        require(type(q[k]) is int and q[k]>0,'Invalid existing remote id')
    check_pin(q['original_request'])
    require(isinstance(q['original_journal'],dict) and 1<=len(q['original_journal'])<=100,
        'Missing pinned original journal')
    for name,pin in q['original_journal'].items():
        require(re.fullmatch('[0-9]{5}_[a-z_]+[.]json',name),'Unsafe original journal name')
        check_pin(pin)
    require(isinstance(q['original_journal_last_sha256'],str)
        and c.SHA.fullmatch(q['original_journal_last_sha256']),'Invalid original journal chain pin')
    f=q['failed_execution']
    require(set(f)=={'run_id','run_attempt','job_id','workflow_revision','artifact_id',
        'artifact_zip_sha256','artifact_zip_bytes'},'Wrong failed execution pin fields')
    for k in ['run_id','run_attempt','job_id','artifact_id','artifact_zip_bytes']:
        require(type(f[k]) is int and f[k]>0,'Invalid failed execution id')
    require(core.REVISION.fullmatch(f['workflow_revision']) and c.SHA.fullmatch(f['artifact_zip_sha256']),
        'Invalid failed execution digest/revision')


def check_original_journal(q,original,root):
    previous=None;events=[];referenced=set()
    paths=sorted(root.glob('*.json'))
    for path in paths:
        if path.name.endswith('_raw_response.json'):continue
        event=core.strict_json(path.read_bytes());i=len(events)
        require(event['schema']=='rotating.release-journal-event.v1' and event['sequence']==i
            and event['previous_sha256']==previous
            and path.name==str(i).zfill(5)+'_'+event['event']+'.json','Broken original event chain')
        previous=c.digest(path);events.append(event)
        if event['event']=='api_response':
            pin=event['data'];name=pin['file']
            require(name==str(i).zfill(5)+'_raw_response.json' and name in q['original_journal']
                and q['original_journal'][name]=={'sha256':pin['sha256'],'bytes':pin['bytes']},
                'Original raw response pin differs')
            referenced.add(name)
    require(previous==q['original_journal_last_sha256'] and len(events)==26,
        'Wrong original failed journal endpoint')
    require(referenced=={p.name for p in paths if p.name.endswith('_raw_response.json')},
        'Unreferenced original raw response')
    start,end=events[0],events[-1];f=q['failed_execution']
    require(start['event']=='started' and end['event']=='failed','Original journal did not fail')
    d=start['data']
    require(d['request_sha256']==q['original_request']['sha256']
        and d['source_revision']==original['source_revision']
        and d['publisher_revision']==original['publisher_revision']
        and d['publisher_sha256']==original['publisher_sha256']
        and d['test_fixture']==q['test_fixture']
        and d['actual_lean_run_here'] is False and d['full_certificate_proved'] is False
        and d['actions']['run_id']==f['run_id']
        and d['actions']['workflow_revision']==f['workflow_revision']
        and d['actions']['tool_revision']==original['publisher_revision'],
        'Original execution binding differs')
    require(end['data']['writes_attempted']==3 and end['data']['remote_cleanup_performed'] is False
        and end['data']['automatic_retry_performed'] is False,'Unexpected original write history')
    intents=[x['data'] for x in events if x['event']=='mutation_intent']
    require(len(intents)==3 and [x['method'] for x in intents]==['POST']*3
        and [x['endpoint'] for x in intents]==[API+'/git/refs',API+'/releases',
                API+'/releases/'+str(q['release_id'])+'/assets'],'Unexpected original mutations')
    require(intents[0]['payload']=={'ref':'refs/tags/'+original['tag'],'sha':original['source_revision']}
        and intents[1]['payload']['tag_name']==original['tag']
        and intents[1]['payload']['target_commitish']==original['source_revision']
        and intents[1]['payload']['draft'] is True
        and intents[2]['upload_name']==original['archive']['asset_name']
        and intents[2]['bytes']==original['archive']['bytes'],'Original mutation payloads differ')
    require(events[18]['event']=='created_draft' and events[18]['data']['release_id']==q['release_id']
        and events[22]['event']=='uploaded_asset' and events[22]['data']['release_id']==q['release_id']
        and events[22]['data']['asset_id']==q['asset_id'],'Original created ids differ')
    release=core.strict_json((root/'00023_raw_response.json').read_bytes())
    asset=core.strict_json((root/'00024_raw_response.json').read_bytes())
    check_state(q,original,release,asset,release['assets'],draft=True)
    return release,asset


def check_state(q,original,release,asset,assets,*,draft):
    identity=url_protocol.validate_release(release,q['release_id'],original['tag'],
        original['source_revision'],draft=draft)
    a=original['archive']
    url_protocol.validate_asset(asset,identity,q['asset_id'],a['asset_name'],a['sha256'],a['bytes'])
    require(release['name']==original['title'] and release['prerelease'] is False,
        'Release presentation/scope differs')
    require(isinstance(assets,list) and len(assets)==1 and isinstance(release['assets'],list)
        and len(release['assets'])==1,'Existing release must have exactly the pinned asset')
    for row in [assets[0],release['assets'][0]]:
        require(selected(row,ASSET_KEYS)==selected(asset,ASSET_KEYS),'Existing release asset set differs')
    return selected(release,RELEASE_KEYS),selected(asset,ASSET_KEYS)


def prepare(request,request_sha,input_root,allow_fixture=False):
    path=core.plain_path(request,'file');root=core.plain_path(input_root,'dir')
    require(path.stat().st_size<=r.REQUEST_LIMIT and c.digest(path)==request_sha,'Recovery request pin differs')
    q=core.strict_json(path.read_bytes());validate_request(q,allow_fixture)
    pinned={path:request_sha}
    def load(name,pin):
        f=core.plain_path(c.confined(root,name),'file')
        require(f.stat().st_size==pin['bytes'] and c.digest(f)==pin['sha256'],'Pinned recovery input differs')
        pinned[f]=pin['sha256'];return core.strict_json(f.read_bytes())
    original=load('original_request.json',q['original_request'])
    adapter.validate_request(original,c.digest(old.__file__),allow_fixture)
    require(original['test_fixture']==q['test_fixture'],'Mixed fixture/production inputs')
    evidence={k:load('evidence/'+v['file'],{'sha256':v['sha256'],'bytes':v['bytes']})
        for k,v in original['evidence'].items()}
    scope=adapter.check_evidence(original,**evidence)
    journal=core.plain_path(root/'original_journal','dir')
    require({x.name for x in journal.iterdir()}==set(q['original_journal']),'Original journal file set differs')
    for name,pin in q['original_journal'].items():load('original_journal/'+name,pin)
    release,asset=check_original_journal(q,original,journal)
    return {'request':q,'request_sha256':request_sha,'original':original,'pinned_files':pinned,
        'helpers':helpers(),'scope':scope,'original_release':release,'original_asset':asset}


def checked_tool_revision():
    directory=Path(__file__).resolve().parent;env=os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):env.pop(key)
    def git(*args):
        return subprocess.run(['git','-C',str(directory),*args],env=env,check=True,
            stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30).stdout
    top=core.plain_path(Path(git('rev-parse','--show-toplevel').decode().strip()),'dir').resolve()
    revision=git('rev-parse','HEAD').decode().strip()
    require(core.REVISION.fullmatch(revision),'Invalid recovery checkout revision')
    source_pins={Path(__file__).resolve():c.digest(__file__)}
    source_pins.update({(directory.parent/'performance'/name if name=='reference.py'
            else directory/name).resolve():digest for name,digest in helpers().items()})
    for path,digest in source_pins.items():
        require(path.is_relative_to(top) and c.digest(path)==digest
            and git('show','HEAD:'+path.relative_to(top).as_posix())==path.read_bytes(),
            'Recovery code is not the committed checkout blob')
    return revision


class RecoveryHTTP(old.ReleaseHTTP):
    def __init__(self,journal,release_id,**kwargs):
        super().__init__(journal,**kwargs);self.release_id=release_id

    def mutate(self,method,suffix,payload=None,archive=None,name=None):
        require(self.writes==0 and method=='PATCH' and suffix==API+'/releases/'+str(self.release_id)
            and payload=={'draft':False} and archive is None and name is None,
            'Recovery permits only one publication PATCH to its pinned release')
        return super().mutate(method,suffix,payload)


def verify_failed_origin(client,q):
    f=q['failed_execution']
    run,_=client.metadata(API+'/actions/runs/'+str(f['run_id']))
    job,_=client.metadata(API+'/actions/jobs/'+str(f['job_id']))
    artifact,_=client.metadata(API+'/actions/artifacts/'+str(f['artifact_id']))
    require(run['id']==f['run_id'] and run['repository']['full_name']==r.REPO
        and run['head_sha']==f['workflow_revision'] and run['run_attempt']==f['run_attempt']
        and run['status']=='completed' and run['conclusion']=='failure','Original failed run differs')
    require(job['id']==f['job_id'] and job['run_id']==f['run_id']
        and job['head_sha']==f['workflow_revision'] and job['status']=='completed'
        and job['conclusion']=='failure','Original failed job differs')
    require(artifact['id']==f['artifact_id'] and artifact['expired'] is False
        and artifact['workflow_run']['id']==f['run_id']
        and artifact['workflow_run']['head_sha']==f['workflow_revision']
        and artifact['digest']=='sha256:'+f['artifact_zip_sha256']
        and artifact['size_in_bytes']==f['artifact_zip_bytes'],'Original journal artifact differs')


def recheck(ctx,code_sha):
    require(c.digest(__file__)==code_sha and ctx['helpers']==helpers(),'Recovery implementation changed')
    for path,digest in ctx['pinned_files'].items():
        require(core.plain_path(path,'file')==path and c.digest(path)==digest,'Recovery input changed')


def recover(ctx,client,journal,environment=None):
    q,o=ctx['request'],ctx['original'];a=o['archive'];code_sha=c.digest(__file__)
    require(client.fixture==q['test_fixture'] and client.release_id==q['release_id']
        and journal is client.journal,'Recovery client/request mismatch')
    actions=None
    if not client.fixture:
        env=environment if environment is not None else os.environ
        require(env.get('GITHUB_RUN_ATTEMPT')=='1','Recovery workflow reruns require a new review')
        actions=old.actions_context(q,env,checked_tool_revision())
    def local():
        recheck(ctx,code_sha)
        if not client.fixture:require(checked_tool_revision()==q['publisher_revision'],'Recovery checkout moved')
    def origins():
        verify_failed_origin(client,q)
        for origin in o['origins'].values():client.verify_origin(origin)
    def snapshot(draft):
        release,rhash=client.metadata(API+'/releases/'+str(q['release_id']))
        asset,ahash=client.metadata(API+'/releases/assets/'+str(q['asset_id']))
        assets,_=client.metadata(API+'/releases/'+str(q['release_id'])+'/assets?per_page=100&page=1')
        state=check_state(q,o,release,asset,assets,draft=draft)
        old.exact_tag(client,o['tag'],o['source_revision'])
        return state,release,asset,rhash,ahash
    journal.event('started',{'request_sha256':ctx['request_sha256'],'original_request_sha256':q['original_request']['sha256'],
        'original_journal_last_sha256':q['original_journal_last_sha256'],'actions':actions,
        'release_id':q['release_id'],'asset_id':q['asset_id'],'test_fixture':client.fixture,
        'allowed_mutation':'one PATCH draft:false to the pinned existing release','full_certificate_proved':False,
        'journal_sync':'file_and_directory_fsync' if os.name=='posix' else 'file_fsync_no_directory_sync'})
    try:
        local();origins()
        initial=snapshot(True)
        expected=(selected(ctx['original_release'],RELEASE_KEYS),selected(ctx['original_asset'],ASSET_KEYS))
        require(initial[0]==expected,'Existing draft differs from the reviewed original journal')
        draft_download=client.binary(q['asset_id'],a['sha256'],a['bytes'])
        journal.event('draft_download_verified',draft_download)
        local();origins()
        require(snapshot(True)[0]==initial[0],'Draft changed before recovery publication')
        client.mutate('PATCH',API+'/releases/'+str(q['release_id']),{'draft':False})
        published=snapshot(False)
        require(published[1]['body']==ctx['original_release']['body'],'Published release scope changed')
        published_download=client.binary(q['asset_id'],a['sha256'],a['bytes'])
        journal.event('published_download_verified',published_download)
        final=snapshot(False)
        require(final[0]==published[0],'Published identity changed during complete redownload')
        local()
        _,release,asset,rhash,ahash=final
        record={'schema':'rotating.durable-core-release-record.v1','kind':'publisher_verified_core_release_asset',
            'status':'fixture_only' if client.fixture else 'remote_verified','test_fixture':client.fixture,
            'repository':r.REPO,'revision':o['source_revision'],'base_lock_sha256':o['base_lock_sha256'],
            'source_inventory_sha256':o['source_inventory_sha256'],
            'release':{'id':q['release_id'],'tag':o['tag'],'draft':False,'published_at':release['published_at'],
                'immutable_observed':release.get('immutable')},
            'asset':selected(asset,['id','name','state','size','digest','browser_download_url']),
            'verification':{'method':'GitHub REST metadata plus complete draft and published asset-ID redownloads',
                'redownload_sha256':published_download['sha256'],'redownload_bytes':published_download['bytes'],
                'draft_redownload':draft_download,'asset_api_sha256':ahash,'release_api_sha256':rhash,
                'verified_at':old.utc()},
            'publisher':{'revision':q['publisher_revision'],'request_sha256':ctx['request_sha256'],
                'script_sha256':code_sha,'actions':actions,'journal_previous_sha256':journal.previous},
            'recovery':{'original_request_sha256':q['original_request']['sha256'],
                'original_publisher_revision':o['publisher_revision'],
                'original_journal_last_sha256':q['original_journal_last_sha256'],
                'original_failed_execution':q['failed_execution'],'created_new_release_or_asset':False},
            'actual_http_writes':client.writes,'remote_durability_verified':not client.fixture,
            'actual_lean_run_here':False,'full_certificate_proved':False}
        old.durable_new(journal.root/'result.json',core.json_bytes(record))
        journal.event('finished',{'result_sha256':c.digest(journal.root/'result.json'),'writes':client.writes})
        return record
    except Exception as error:
        journal.event('failed',{'exception_type':type(error).__name__,'writes_attempted':client.writes,
            'remote_cleanup_performed':False,'automatic_retry_performed':False,
            'recovery_requires_separate_review':True})
        raise


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['request','input-root','output']:parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--request-sha256',required=True);parser.add_argument('--execute',action='store_true')
    args=parser.parse_args();ctx=prepare(args.request,args.request_sha256,args.input_root)
    require(not args.output.resolve().is_relative_to(args.input_root.resolve()),'Output overlaps original input')
    journal=old.Journal(args.output)
    if not args.execute:
        journal.event('dry_run',{'actual_http_writes':0,'request_sha256':args.request_sha256,**ctx['scope']})
        print(json.dumps({'status':'recovery_inputs_checked','actual_http_writes':0}));return
    token=os.environ.get('GH_TOKEN');require(token,'GH_TOKEN is absent')
    client=RecoveryHTTP(journal,ctx['request']['release_id'],token=token)
    result=recover(ctx,client,journal)
    print(json.dumps({'status':result['status'],'release_id':result['release']['id'],
        'asset_id':result['asset']['id'],'actual_http_writes':result['actual_http_writes']}))


if __name__=='__main__':main()
