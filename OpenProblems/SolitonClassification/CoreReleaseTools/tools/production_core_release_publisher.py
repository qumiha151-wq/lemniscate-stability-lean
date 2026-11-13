"""New journaled Layer A-core publisher; only explicit pinned Actions execution.

No overwrite, delete, tag move, or automatic retry/resume operation exists. Every
mutation intent is fsynced before its request. An ambiguous failure leaves the
remote draft/tag intact for separately reviewed recovery. Local tests inject an
in-memory HTTP transport and cannot emit production durable records.
"""
from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request
from urllib.error import HTTPError
from urllib.parse import urlencode
import argparse,hashlib,json,os,re,subprocess,time
import production_core_release_request as adapter

r,c,core,require=adapter.r,adapter.c,adapter.core,adapter.require
API='/repos/'+r.REPO


def utc():
    return datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


def sync_directory(path):
    if os.name=='posix':
        fd=os.open(path,os.O_RDONLY|getattr(os,'O_DIRECTORY',0))
        try:os.fsync(fd)
        finally:os.close(fd)


def durable_new(path,raw):
    with path.open('xb') as f:
        f.write(raw);f.flush();os.fsync(f.fileno())
    sync_directory(path.parent)


def durable_directory(path):
    missing=[];at=path
    while not at.exists():missing.append(at);at=at.parent
    core.plain_path(at,'dir')
    for at in reversed(missing):
        at.mkdir();sync_directory(at.parent);sync_directory(at)


class Journal:
    def __init__(self,path):
        self.root=core.fresh_path(path);durable_directory(self.root)
        self.number=0;self.previous=None

    def event(self,kind,data):
        require(re.fullmatch('[a-z_]+',kind),'Unsafe journal event')
        value={'schema':'rotating.release-journal-event.v1','sequence':self.number,
            'previous_sha256':self.previous,'at':utc(),'event':kind,'data':data}
        raw=core.json_bytes(value);path=self.root/(str(self.number).zfill(5)+'_'+kind+'.json')
        durable_new(path,raw)
        self.previous=hashlib.sha256(raw).hexdigest();self.number+=1
        return self.previous

    def response(self,raw):
        data=core.strict_json(raw)
        # Exact REST JSON bytes, never a signed binary redirect URL or token.
        name=str(self.number).zfill(5)+'_raw_response.json'
        durable_new(self.root/name,raw)
        self.event('api_response',{'file':name,'sha256':r.p.sha(raw),'bytes':len(raw)})
        return data,r.p.sha(raw)


class TimedFile:
    def __init__(self,file,seconds=1800):
        self.file=file;self.deadline=time.monotonic()+seconds
    def read(self,n=-1):
        require(time.monotonic()<self.deadline,'Upload total deadline exceeded')
        return self.file.read(n)


class ReleaseHTTP(r.ReadOnlyReleaseHTTP):
    def __init__(self,journal,**kwargs):
        super().__init__(**kwargs);self.journal=journal;self.writes=0

    def metadata(self,suffix):
        require(re.fullmatch(re.escape(API)+r'/[A-Za-z0-9_./-]+(?:\?per_page=100&page=[1-9][0-9]*)?',suffix)
            and '..' not in suffix,'Unsafe publisher metadata endpoint')
        with self.open(self.api+suffix,'application/vnd.github+json') as response:
            require(response.status==200,'Unexpected metadata status')
            raw=response.read(r.JSON_LIMIT+1)
        require(len(raw)<=r.JSON_LIMIT,'Oversized metadata')
        return self.journal.response(raw)

    def absent(self,suffix):
        try:self.metadata(suffix)
        except HTTPError as error:
            code=error.code;error.close()
            require(code==404,'Absence check did not return 404')
            self.journal.event('confirmed_absent',{'endpoint':suffix,'status':404});return
        raise RuntimeError('Requested remote identity already exists')

    def no_release_for_tag(self,tag):
        self.absent(API+'/releases/tags/'+tag)
        # The collection includes drafts visible to the publisher credential.
        # Refuse to proceed if the bounded scan cannot establish absence.
        for page in range(1,101):
            rows,_=self.metadata(API+'/releases?per_page=100&page='+str(page))
            require(isinstance(rows,list) and len(rows)<=100,'Malformed release collection')
            require(all(x['tag_name']!=tag for x in rows),'A draft/published release already uses this tag')
            if len(rows)<100:return
        raise RuntimeError('Release absence scan exceeded bounded pages')

    def mutate(self,method,suffix,payload=None,archive=None,name=None):
        upload=archive is not None
        allowed=(method=='POST' and suffix in (API+'/git/refs',API+'/releases')) or (
            method=='PATCH' and re.fullmatch(re.escape(API)+r'/releases/[1-9][0-9]*',suffix))
        if upload:
            allowed=method=='POST' and re.fullmatch(re.escape(API)+r'/releases/[1-9][0-9]*/assets',suffix)
            require(re.fullmatch('[A-Za-z0-9_.-]+',name),'Unsafe upload name')
        require(allowed,'Forbidden release mutation')
        if method=='PATCH':require(payload=={'draft':False},'Only publishing a verified draft is allowed')
        host=self.api if self.fixture or not upload else 'https://uploads.github.com'
        url=host+suffix+(('?'+urlencode({'name':name})) if upload else '')
        headers={'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28'}
        require(self.token,'No publisher credential supplied')
        headers['Authorization']='Bearer '+self.token
        data=core.json_bytes(payload) if not upload else None
        headers['Content-Type']='application/octet-stream' if upload else 'application/json'
        headers['Content-Length']=str(archive.stat().st_size if upload else len(data))
        intent={'method':method,'endpoint':suffix,'upload_name':name,
                'payload':payload,'bytes':int(headers['Content-Length'])}
        self.journal.event('mutation_intent',intent)
        def send(body):
            self.writes+=1
            # NoRedirect also forbids authenticated upload redirects. No retry.
            with self.opener.open(Request(url,headers=headers,data=body,method=method),timeout=90) as response:
                require(response.status==(200 if method=='PATCH' else 201),'Unexpected mutation status')
                raw=response.read(r.JSON_LIMIT+1)
            require(len(raw)<=r.JSON_LIMIT,'Oversized mutation response')
            result,digest=self.journal.response(raw)
            self.journal.event('mutation_response',{'method':method,'endpoint':suffix,'response_sha256':digest})
            return result
        if upload:
            with core.plain_path(archive,'file').open('rb') as f:return send(TimedFile(f))
        return send(data)


def exact_tag(client,tag,revision):
    value,_=client.metadata(API+'/git/ref/tags/'+tag)
    require(value['ref']=='refs/tags/'+tag and value['object']['type']=='commit'
        and value['object']['sha']==revision,'Exact lightweight tag differs')


def verify_draft(client,release_id,asset_id,q):
    release,_=client.metadata(API+'/releases/'+str(release_id))
    asset,_=client.metadata(API+'/releases/assets/'+str(asset_id));a=q['archive']
    require(release['id']==release_id and release['tag_name']==q['tag'] and release['draft'] is True
        and release.get('published_at') is None,'Expected own unpublished draft')
    require(len(release['assets'])==1 and release['assets'][0]['id']==asset_id,'Unexpected draft asset set')
    expected_url='https://github.com/'+r.REPO+'/releases/download/'+q['tag']+'/'+a['asset_name']
    require(asset['id']==asset_id and asset['name']==a['asset_name'] and asset['state']=='uploaded'
        and asset['size']==a['bytes'] and asset['digest']=='sha256:'+a['sha256']
        and asset['browser_download_url']==expected_url,'Draft asset identity differs')
    exact_tag(client,q['tag'],q['source_revision'])
    client.binary(asset_id,a['sha256'],a['bytes'])
    again,_=client.metadata(API+'/releases/'+str(release_id))
    a2,_=client.metadata(API+'/releases/assets/'+str(asset_id))
    keys=['id','name','state','size','digest','browser_download_url']
    require({k:a2.get(k) for k in keys}=={k:asset.get(k) for k in keys}
        and again['id']==release_id and again['draft'] is True and again['tag_name']==q['tag']
        and again.get('published_at') is None and len(again['assets'])==1
        and again['assets'][0]['id']==asset_id,'Draft changed during full redownload')
    exact_tag(client,q['tag'],q['source_revision'])


def checked_tool_revision():
    """Read the actual already-published tool checkout, not the workflow SHA.

    Tools at P run from a later workflow Q. Binding a request committed at Q to Q
    itself would be a hash cycle; P is the independently pinned code identity.
    """
    directory=Path(__file__).resolve().parent
    env=os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):env.pop(key)
    def git(*args):
        result=subprocess.run(['git','-C',str(directory),*args],env=env,check=True,
            stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
        return result.stdout
    top=core.plain_path(Path(git('rev-parse','--show-toplevel').decode('utf-8').strip()),'dir').resolve()
    require(directory.is_relative_to(top),'Publisher source is outside actual tool checkout')
    revision=git('rev-parse','HEAD').decode('utf-8').strip()
    require(core.REVISION.fullmatch(revision),'Invalid actual tool checkout revision')
    relative=Path(__file__).resolve().relative_to(top).as_posix()
    require(git('show','HEAD:'+relative)==Path(__file__).read_bytes(),
            'Publisher bytes are not the actual committed tool blob')
    return revision


def actions_context(q,env,tool_revision):
    require(env.get('GITHUB_ACTIONS')=='true' and env.get('GITHUB_REPOSITORY')==r.REPO
        and tool_revision==q['publisher_revision'],'Execution is not the pinned tool checkout in Actions')
    require(core.REVISION.fullmatch(env.get('GITHUB_SHA','')),'Missing exact workflow revision')
    require(env.get('GITHUB_EVENT_NAME') in ('push','workflow_dispatch')
        and re.fullmatch('[1-9][0-9]*',env.get('GITHUB_RUN_ID','')),'Untrusted publisher event/run')
    require(not q['test_fixture'],'Fixture request cannot execute against GitHub')
    return {'tool_revision':tool_revision,'workflow_revision':env['GITHUB_SHA'],
        'run_id':int(env['GITHUB_RUN_ID']),'event':env['GITHUB_EVENT_NAME']}


def publish(ctx,client,journal,environment=None):
    q=ctx['request'];a=q['archive'];code_sha=c.digest(__file__)
    require(client.fixture==q['test_fixture'],'HTTP/request fixture boundaries differ')
    actions=None
    if not client.fixture:
        actions=actions_context(q,environment if environment is not None else os.environ,checked_tool_revision())
    require(journal is client.journal,'Publisher journal mismatch')
    def recheck():
        require(c.digest(__file__)==code_sha,'Publisher source changed during execution')
        adapter.recheck(ctx,code_sha)
        if not client.fixture:require(checked_tool_revision()==q['publisher_revision'],'Tool checkout moved')
    journal.event('started',{'request_sha256':ctx['request_sha256'],'source_revision':q['source_revision'],
        'publisher_revision':q['publisher_revision'],'publisher_sha256':code_sha,
        'actions':actions,'test_fixture':client.fixture,'actual_lean_run_here':False,'full_certificate_proved':False,
        'journal_sync':'file_and_directory_fsync' if os.name=='posix' else 'file_fsync_no_directory_sync',
        'runner_loss_survival_claimed':False})
    try:
        recheck()
        for origin in q['origins'].values():client.verify_origin(origin)
        commit,_=client.metadata(API+'/commits/'+q['source_revision'])
        require(commit['sha']==q['source_revision'],'Mathematical source commit differs')
        client.absent(API+'/git/ref/tags/'+q['tag']);client.no_release_for_tag(q['tag'])
        created=client.mutate('POST',API+'/git/refs',{'ref':'refs/tags/'+q['tag'],'sha':q['source_revision']})
        require(created['ref']=='refs/tags/'+q['tag'],'Created another tag')
        exact_tag(client,q['tag'],q['source_revision'])
        release=client.mutate('POST',API+'/releases',{'tag_name':q['tag'],'target_commitish':q['source_revision'],
            'name':q['title'],'body':'Exact checked Lean core archive. No numerical trajectory or complete classification claim.',
            'draft':True,'prerelease':False,'generate_release_notes':False})
        release_id=release['id'];require(type(release_id) is int and release_id>0,'Invalid created release id')
        journal.event('created_draft',{'release_id':release_id,'tag':q['tag']})
        require(release['tag_name']==q['tag'] and release['draft'] is True
            and not release['assets'] and release.get('published_at') is None,'Created draft state differs')
        recheck()
        asset=client.mutate('POST',API+'/releases/'+str(release_id)+'/assets',archive=ctx['archive'],name=a['asset_name'])
        asset_id=asset['id'];require(type(asset_id) is int and asset_id>0,'Invalid uploaded asset id')
        journal.event('uploaded_asset',{'release_id':release_id,'asset_id':asset_id,'asset_name':a['asset_name']})
        verify_draft(client,release_id,asset_id,q)
        recheck()
        # Recheck successful origin identities immediately before publication.
        for origin in q['origins'].values():client.verify_origin(origin)
        client.mutate('PATCH',API+'/releases/'+str(release_id),{'draft':False})
        observed=client.verify_published(release_id,asset_id,q['tag'],q['source_revision'],
            a['asset_name'],a['sha256'],a['bytes'])
        release,rhash=client.metadata(API+'/releases/'+str(release_id))
        asset,ahash=client.metadata(API+'/releases/assets/'+str(asset_id))
        require(release['draft'] is False and len(release['assets'])==1 and release['assets'][0]['id']==asset_id,
                'Published asset set changed')
        require(release['id']==release_id and release['tag_name']==q['tag']
            and isinstance(release.get('published_at'),str) and release['published_at']
            and asset['id']==asset_id and asset['name']==a['asset_name'] and asset['state']=='uploaded'
            and asset['size']==a['bytes'] and asset['digest']=='sha256:'+a['sha256']
            and asset['browser_download_url']=='https://github.com/'+r.REPO+'/releases/download/'+q['tag']+'/'+a['asset_name'],
            'Final published identity differs')
        exact_tag(client,q['tag'],q['source_revision'])
        recheck()
        record={'schema':'rotating.durable-core-release-record.v1','kind':'publisher_verified_core_release_asset',
            'status':'fixture_only' if client.fixture else 'remote_verified','test_fixture':client.fixture,
            'repository':r.REPO,'revision':q['source_revision'],'base_lock_sha256':q['base_lock_sha256'],
            'source_inventory_sha256':q['source_inventory_sha256'],
            'release':{'id':release_id,'tag':q['tag'],'draft':False,'published_at':release['published_at'],
                       'immutable_observed':release.get('immutable')},
            'asset':{k:asset[k] for k in ['id','name','state','size','digest','browser_download_url']},
            'verification':{'method':'GitHub REST metadata plus full redownload',
                'redownload_sha256':observed['download']['sha256'],'redownload_bytes':observed['download']['bytes'],
                'asset_api_sha256':ahash,'release_api_sha256':rhash,'verified_at':utc()},
            'publisher':{'revision':q['publisher_revision'],'request_sha256':ctx['request_sha256'],
                'script_sha256':code_sha,'actions':actions,'journal_previous_sha256':journal.previous},
            'actual_http_writes':client.writes,'remote_durability_verified':not client.fixture,
            'actual_lean_run_here':False,'full_certificate_proved':False}
        durable_new(journal.root/'result.json',core.json_bytes(record))
        journal.event('finished',{'result_sha256':c.digest(journal.root/'result.json'),
            'remote_durability_verified':not client.fixture,'writes':client.writes})
        return record
    except Exception as error:
        journal.event('failed',{'exception_type':type(error).__name__,
            'http_status':error.code if isinstance(error,HTTPError) else None,
            'writes_attempted':client.writes,'remote_cleanup_performed':False,
            'automatic_retry_performed':False,'recovery_requires_separate_review':True})
        raise


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['request','input-root','output']:parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--request-sha256',required=True)
    parser.add_argument('--execute',action='store_true')
    args=parser.parse_args()
    ctx=adapter.prepare(args.request,args.request_sha256,args.input_root,c.digest(__file__))
    require(not args.output.resolve().is_relative_to(args.input_root.resolve()),'Output overlaps pinned input')
    journal=Journal(args.output)
    if not args.execute:
        journal.event('dry_run',{'request_sha256':args.request_sha256,'actual_http_writes':0,
            'release_created':False,'remote_durability_verified':False,**ctx['scope']})
        print(json.dumps({'status':'local_core_preflight_checked','actual_http_writes':0}));return
    actions_context(ctx['request'],os.environ,checked_tool_revision())
    token=os.environ.get('GH_TOKEN');require(token,'GH_TOKEN is absent')
    client=ReleaseHTTP(journal,token=token)
    result=publish(ctx,client,journal)
    print(json.dumps({'status':result['status'],'release_id':result['release']['id'],
        'asset_id':result['asset']['id'],'remote_durability_verified':result['remote_durability_verified']}))


if __name__=='__main__':main()
