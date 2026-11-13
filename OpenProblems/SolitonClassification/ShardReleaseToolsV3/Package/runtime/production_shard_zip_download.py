"""Read-only, context-bound original Actions ZIP download library. No CLI."""
from pathlib import Path,PurePosixPath
from urllib.parse import urlsplit
from urllib.error import HTTPError
import hashlib,json,math,os,shutil,stat,subprocess,time,zipfile
import production_shard_release_publisher_v3 as v

w,r,c,p,core,origin,require,API=v.w,v.r,v.c,v.p,v.core,v.origin,v.require,v.API
STAGE_CAP=512*1024**2  # Exact cap passed by the frozen 624... preflight to artifact.unpack.
ZIP_EXPANDED_CAP=512*1024**2
HEADROOM=2*1024**3
RESERVE=100


def helpers():return {**v.helpers(),Path(__file__).name:c.digest(__file__)}


def prepare(request,request_sha,plan,plan_sha,catalog,catalog_sha,output,allow_fixture=False):
    request=core.plain_path(request,'file');plan=core.plain_path(plan,'file');catalog=core.plain_path(catalog,'file')
    output=core.fresh_path(output)
    require(request.stat().st_size<=r.REQUEST_LIMIT and c.digest(request)==request_sha
        and catalog.stat().st_size<=origin.LIMIT and c.digest(catalog)==catalog_sha,'Wrong bounded download inputs')
    envelope=core.strict_json(request.read_bytes());cat=core.strict_json(catalog.read_bytes());q=envelope['original_request']
    _,plan_data,_=p.bound_plan(plan,plan_sha,q['source_revision'],'RP0000')
    v.validate_envelope(envelope,plan_data,cat,allow_fixture)
    require(envelope['origin_catalog_sha256']==catalog_sha and q['plan_sha256']==plan_sha,'Wrong download plan/catalog binding')
    for f in (request,plan,catalog):require(not f.resolve().is_relative_to(output.resolve()),'Output/input overlap')
    w.durable_directory(output)
    for name in ('inputs','zips','archives','evidence'):w.durable_directory(output/name)
    pins={request:request_sha,plan:plan_sha,catalog:catalog_sha};known={}
    for name,path in (('request.json',request),('plan.json',plan),('catalog.json',catalog)):
        dest=output/'inputs'/name;w.durable_new(dest,path.read_bytes());known[dest]=c.digest(dest)
    ctx={'request':q,'envelope':envelope,'catalog':cat,'request_path':request,'request_sha256':request_sha,
        'plan_path':plan,'plan_sha256':plan_sha,'catalog_path':catalog,'catalog_sha256':catalog_sha,
        'output':output,'pins':pins,'known':known,'helper_sha256':helpers()}
    recheck(ctx);return ctx


def recheck(ctx):
    require(helpers()==ctx['helper_sha256'],'Download helper changed')
    for f,digest in ctx['pins'].items():require(c.digest(core.plain_path(f,'file'))==digest,'Download input changed')
    require(core.strict_json(ctx['request_path'].read_bytes())==ctx['envelope']
        and ctx['envelope']['original_request']==ctx['request']
        and core.strict_json(ctx['catalog_path'].read_bytes())==ctx['catalog']
        and ctx['envelope']['origin_catalog_sha256']==ctx['catalog_sha256'],'Mixed download context')
    _,plan,_=p.bound_plan(ctx['plan_path'],ctx['plan_sha256'],ctx['request']['source_revision'],'RP0000')
    v.validate_envelope(ctx['envelope'],plan,ctx['catalog'],ctx['request']['test_fixture'])
    require(ctx['request']['plan_sha256']==ctx['plan_sha256'],'Download context plan differs')


def checked_tool_revision():
    revision=v.checked_tool_revision();env=os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):env.pop(key)
    directory=Path(__file__).resolve().parent
    def git(*args):
        return subprocess.run(['git','-C',str(directory),*args],env=env,check=True,
            stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30).stdout
    top=core.plain_path(Path(git('rev-parse','--show-toplevel').decode().strip()),'dir').resolve()
    source=Path(__file__).resolve();require(source.is_relative_to(top),'Outer source outside tool checkout')
    require(git('rev-parse','HEAD').decode().strip()==revision
        and git('show','HEAD:'+source.relative_to(top).as_posix())==source.read_bytes(),
        'Outer source is not its actual committed tool blob')
    return revision


def quota_decision(observed,n,a,epoch,monotonic):
    require(type(n) is int and 1<=n<=32 and type(a) is int and 3<=a<=5,'Wrong read-only quota scope')
    required=n+2*a+RESERVE
    result={'allowed':False,'bootstrap_GETs_already_spent':a,'remaining_successful_path_requests':n+a,
        'conservative_stage_requests':n+2*a,'reserve_requests':RESERVE,'required_remaining':required,
        'observed':observed,'atomic_reservation_claimed':False,'secondary_limit_guarantee':False}
    if observed is None:return {**result,'reason':'no_quota_observation'}
    if not observed.get('valid'):return {**result,'reason':observed.get('reason','invalid_observation')}
    if observed.get('http_status')!=200:return {**result,'reason':'latest_http_status_not_success'}
    age=monotonic-observed['captured_monotonic']
    if not all(math.isfinite(x) for x in (epoch,monotonic,age)) or age<0 or age>30:
        return {**result,'reason':'stale_observation'}
    if epoch>=observed['reset']:return {**result,'reason':'expired_window'}
    if observed['remaining']<required:return {**result,'reason':'insufficient_remaining'}
    return {**result,'allowed':True,'reason':'enough_observed_primary_quota'}


class ReadOnlyHTTP(w.ReleaseHTTP):
    def __init__(self,ctx,journal,*,token,fixture=False,api='https://api.github.com'):
        require(isinstance(token,str) and token and type(fixture) is bool,'Explicit read-only credential/fixture required')
        recheck(ctx);require(ctx['request']['test_fixture'] is fixture,'Download fixture context differs')
        self.ctx=ctx;self.bound_request=core.json_bytes(ctx['request']);self.bound_catalog=core.json_bytes(ctx['catalog'])
        self.latest_quota=None;self.quota_gate=None
        super().__init__(journal,token=token,fixture=fixture,api=api)
        self.opener=v.budget._ObservedOpener(self.opener,self)
    def _observe(self,request,headers,status,error_kind):
        return v.BudgetHTTP._observe(self,request,headers,status,error_kind)
    def mutate(self,*args,**kwargs):
        raise RuntimeError('The original ZIP downloader is read-only')
    def authorize_zip_phase(self):
        recheck(self.ctx)
        require(core.json_bytes(self.ctx['request'])==self.bound_request
            and core.json_bytes(self.ctx['catalog'])==self.bound_catalog,'Quota/download context changed')
        result=quota_decision(self.latest_quota,len(self.ctx['request']['jobs']),origin.request_count(self.ctx['catalog']),
            time.time(),time.monotonic());self.quota_gate=result
        self.journal.event('zip_quota_gate',{'request_sha256':self.ctx['request_sha256'],
            'catalog_sha256':self.ctx['catalog_sha256'],'decision':result,'remote_writes':0,'automatic_wait':False})
        if not result['allowed']:raise v.budget.PrewriteBudgetClosed(result['reason'],result)


def member_name(q,job):
    key=job['key'];return 'job/rotating-'+q['source_revision']+'-'+key[1].lower()+'-'+key[2:]+'-0032.tar.xz'


def extract_archive(zip_path,destination,q,job):
    require(c.digest(core.plain_path(zip_path,'file'))==job['origin_artifact_zip_sha256']
        and zip_path.stat().st_size==job['origin_artifact_zip_bytes'],'Original ZIP changed before extraction')
    destination=core.fresh_path(destination);member=member_name(q,job);seen=set();kinds={};expanded=0
    with zipfile.ZipFile(zip_path) as archive:
        infos=archive.infolist();require(len(infos)<=5000,'Too many ZIP members')
        for info in infos:
            raw=info.filename;canonical=raw.rstrip('/');path=PurePosixPath(raw)
            require(info.orig_filename==raw and '\x00' not in raw and canonical and path.as_posix()==canonical and not path.is_absolute()
                and '..' not in path.parts and '\\' not in canonical and ':' not in canonical,
                'Unsafe/noncanonical ZIP member')
            require(canonical.casefold() not in seen,'Duplicate/casefold ZIP member');seen.add(canonical.casefold())
            mode=stat.S_IFMT(info.external_attr>>16)
            require(mode in (0,stat.S_IFREG,stat.S_IFDIR) and not(info.flag_bits&1),'Special/encrypted ZIP member')
            require((mode!=stat.S_IFDIR or info.is_dir()) and (mode!=stat.S_IFREG or not info.is_dir()),
                'Contradictory ZIP file/directory metadata')
            kinds[canonical.casefold()]=(canonical,info.is_dir())
            expanded+=info.file_size;require(0<=info.file_size and expanded<=ZIP_EXPANDED_CAP,'ZIP expanded-size cap exceeded')
        for canonical,is_dir in kinds.values():
            parts=PurePosixPath(canonical).parts
            for i in range(1,len(parts)):
                prefix='/'.join(parts[:i]);other=kinds.get(prefix.casefold())
                require(other is None or other==(prefix,True),'Ambiguous ZIP parent file/directory')
        info=archive.getinfo(member)
        require(not info.is_dir() and info.file_size==job['archive_bytes'],'Wrong canonical archive member')
        digest=hashlib.sha256();count=0
        with archive.open(info) as source,destination.open('xb') as dest:
            while True:
                block=source.read(min(1024**2,job['archive_bytes']-count+1))
                if not block:break
                count+=len(block);require(count<=job['archive_bytes'],'Oversized extracted original archive')
                digest.update(block);dest.write(block)
            dest.flush();os.fsync(dest.fileno())
        w.sync_directory(destination.parent)
    require(count==job['archive_bytes'] and digest.hexdigest()==job['archive_sha256'],'Wrong extracted original bytes')
    return {'member':member,'zip_expanded_metadata_bytes':expanded,'archive_sha256':digest.hexdigest(),'archive_bytes':count}


def disk_budget(ctx,jobs,filename):
    needed=sum(j['archive_bytes']+j['origin_artifact_zip_bytes'] for j in jobs)+STAGE_CAP+HEADROOM
    free=shutil.disk_usage(core.plain_path(ctx['output'],'dir')).free
    row={'actual_free_bytes':free,'required_free_bytes':needed,'retained_input_bytes':needed-STAGE_CAP-HEADROOM,
        'single_frozen_preflight_expanded_stage_cap':STAGE_CAP,'headroom_bytes':HEADROOM,
        'preflight_helper_sha256':c.digest(r.__file__)}
    path=ctx['output']/'evidence'/filename;w.durable_new(path,core.json_bytes(row));ctx['known'][path]=c.digest(path)
    require(free>=needed,'Insufficient actual disk space');return row


def download_zip(client,job,destination):
    require(client.quota_gate is not None and client.quota_gate['allowed'],'ZIP phase has no context-bound quota gate')
    initial=client.api+API+'/actions/artifacts/'+str(job['origin_artifact_id'])+'/zip'
    try:response=client.open(initial,'application/vnd.github+json')
    except HTTPError as error:
        require(error.code==302,'Unexpected Actions ZIP response')
        location=error.headers.get('Location','');error.close();u=urlsplit(location)
        approved=(u.scheme=='https' and u.port in (None,443) and u.hostname and
            (u.hostname.endswith('.blob.core.windows.net') or u.hostname.endswith('.actions.githubusercontent.com')))
        if client.fixture:approved=(u.scheme=='http' and u.netloc==urlsplit(client.api).netloc)
        require(approved and not u.username and not u.password and not u.fragment,'Unapproved Actions ZIP redirect')
        response=client.open(location,'application/octet-stream',authenticated=False)
    digest=hashlib.sha256();count=0;deadline=time.monotonic()+1200;destination=core.fresh_path(destination)
    with response,destination.open('xb') as dest:
        require(response.status==200,'Wrong final Actions ZIP status')
        while True:
            require(time.monotonic()<deadline,'Actions ZIP total deadline exceeded')
            block=response.read(min(1024**2,job['origin_artifact_zip_bytes']-count+1))
            if not block:break
            count+=len(block);require(count<=job['origin_artifact_zip_bytes'],'Oversized Actions ZIP')
            digest.update(block);dest.write(block)
        dest.flush();os.fsync(dest.fileno())
    w.sync_directory(destination.parent)
    require(count==job['origin_artifact_zip_bytes'] and digest.hexdigest()==job['origin_artifact_zip_sha256'],
        'Incomplete/corrupt Actions ZIP')
    return {'zip_sha256':digest.hexdigest(),'zip_bytes':count}


def journal_files(journal):
    expected={};previous=None
    for number in range(journal.number):
        candidates=[x for x in journal.root.glob(str(number).zfill(5)+'_*.json') if not x.name.endswith('_raw_response.json')]
        require(len(candidates)==1,'Missing/duplicate journal event')
        path=core.plain_path(candidates[0],'file');raw=path.read_bytes();event=core.strict_json(raw)
        require(event['schema']=='rotating.release-journal-event.v1' and event['sequence']==number
            and event['previous_sha256']==previous,'Changed journal chain')
        digest=p.sha(raw);expected[path]=digest;previous=digest
        if event['event']=='api_response':
            row=event['data'];require(row['file']==str(number).zfill(5)+'_raw_response.json','Wrong raw-response path')
            source=core.plain_path(journal.root/row['file'],'file')
            require(source.stat().st_size==row['bytes'] and c.digest(source)==row['sha256'],'Changed raw API response')
            expected[source]=row['sha256']
    require(previous==journal.previous,'Changed journal tail')
    require({f.resolve() for f in journal.root.iterdir()}=={f.resolve() for f in expected},'Extra journal entry')
    return expected


def _download(ctx,client,journal,environment=None):
    require(isinstance(client,ReadOnlyHTTP) and client.ctx is ctx and client.journal is journal
        and journal.root.resolve()==(ctx['output']/'journal').resolve(),'Mixed download client context')
    q=ctx['request'];actions=None
    if not client.fixture:actions=w.actions_context(q,os.environ if environment is None else environment,checked_tool_revision())
    def check():
        recheck(ctx)
        if not client.fixture:require(checked_tool_revision()==q['publisher_revision'],'Outer tool checkout moved')
    journal.event('started',{'request_sha256':ctx['request_sha256'],'catalog_sha256':ctx['catalog_sha256'],
        'test_fixture':client.fixture,'actions':actions,'remote_writes':0,'full_certificate_proved':False})
    try:
        check();disk_budget(ctx,q['jobs'],'disk_before.json')
        before=origin.observe(client,ctx['catalog'],q);client.authorize_zip_phase();records=[]
        for i,job in enumerate(q['jobs']):
            check();disk_budget(ctx,q['jobs'][i:],'disk_'+str(i).zfill(2)+'.json')
            zp=ctx['output']/'zips'/(job['key']+'.zip');ap=ctx['output']/'archives'/job['archive']
            zipped=download_zip(client,job,zp);member=extract_archive(zp,ap,q,job)
            ctx['known'][zp]=job['origin_artifact_zip_sha256'];ctx['known'][ap]=job['archive_sha256']
            row={'key':job['key'],'origin_artifact_id':job['origin_artifact_id'],**zipped,**member}
            journal.event('original_zip_checked',row);records.append(row)
        after=origin.observe(client,ctx['catalog'],q);require(after==before,'Origin changed across all ZIP downloads')
        check();require(client.writes==0,'Read-only client wrote remotely')
        journal.event('ready_to_record',{'archives':len(records),'remote_writes':0,'full_bundle_preflight_here':False})
        expected={**ctx['known'],**journal_files(journal)};actual=set()
        for path in ctx['output'].rglob('*'):
            require(not path.is_symlink() and not(getattr(path,'is_junction',lambda:False)()),'Link in download output')
            if path.is_file():core.plain_path(path,'file');actual.add(path.resolve())
            else:require(path.is_dir() and path in {ctx['output']/n for n in ('inputs','zips','archives','evidence','journal')},
                'Extra/special download directory')
        require(actual=={x.resolve() for x in expected},'Extra/missing download output')
        inventory={}
        for path,digest in expected.items():
            require(c.digest(core.plain_path(path,'file'))==digest,'Download evidence changed at completion')
            inventory[path.relative_to(ctx['output']).as_posix()]={'sha256':digest,'bytes':path.stat().st_size}
        check()
        result={'schema':'rotating.original-zip-download.v1','status':'fixture_only' if client.fixture else 'checked',
            'request_sha256':ctx['request_sha256'],'catalog_sha256':ctx['catalog_sha256'],
            'source_revision':q['source_revision'],'publisher_revision':q['publisher_revision'],'actions':actions,
            'plan_sha256':ctx['plan_sha256'],'base_lock_sha256':q['base_lock_sha256'],'records':records,
            'helper_sha256':ctx['helper_sha256'],'checked_files':inventory,'journal_tail':journal.previous,
            'successful_path_REST_requests':len(records)+2*origin.request_count(ctx['catalog']),
            'test_fixture':client.fixture,'live_origin_verified':not client.fixture,'remote_writes':0,
            'new_Lean_calls':0,'full_bundle_preflight_here':False,'durable_release_verified':False,'full_certificate_proved':False}
        w.durable_new(ctx['output']/'receipt.json',core.json_bytes(result));return result
    except Exception as error:
        journal.event('failed',{'exception_type':type(error).__name__,
            'http_status':error.code if isinstance(error,HTTPError) else None,'remote_writes':client.writes,
            'automatic_retry_performed':False,'cleanup_performed':False})
        raise


def download_with_budget(ctx,*,token,environment=None):
    require(ctx['request']['test_fixture'] is False,'Fixture cannot enter production ZIP download')
    recheck(ctx);journal=w.Journal(ctx['output']/'journal');client=ReadOnlyHTTP(ctx,journal,token=token)
    return _download(ctx,client,journal,environment)
