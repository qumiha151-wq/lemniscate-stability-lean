"""Library-only partial publisher with bulk origin and whole-batch snapshots.

No CLI, automatic wait/retry, catalog creation, or remote cleanup. Production
entry constructs a quota client from the same fully prepared context.
"""
from pathlib import Path
from types import SimpleNamespace
from urllib.error import HTTPError
from urllib.parse import urlsplit
import math,os,subprocess,time
import production_shard_release_publisher_v2 as v
import production_shard_prewrite_budget as budget
import production_bulk_origin as origin

w,r,c,core,p,require,API=v.w,v.r,v.c,v.core,v.p,v.require,v.API
SCHEMA='rotating.release-shards-envelope.v3'
FIXED={
 'production_shard_release_publisher_v2.py':'cba63be08c987643a1bbf86aeb5793171667b433dc2a4bbacd962817fdf90b38',
 'production_shard_prewrite_budget.py':'b44da9709ae548af4caa419cf54601f76a5f663a986cfa96e55992c72a5c37b5'}
RESERVE=100


def helpers():
    values={**v.helpers(),Path(budget.__file__).name:c.digest(budget.__file__),
        Path(origin.__file__).name:c.digest(origin.__file__),Path(__file__).name:c.digest(__file__)}
    require(all(values.get(k)==x for k,x in FIXED.items()),'Frozen v2/quota dependency changed')
    return values


def validate_envelope(envelope,plan,catalog,allow_fixture=False):
    require(isinstance(envelope,dict) and set(envelope)=={'schema','original_request','publisher_sha256',
        'helper_sha256','origin_catalog_sha256'} and envelope['schema']==SCHEMA,'Wrong v3 envelope')
    require(envelope['publisher_sha256']==c.digest(__file__) and envelope['helper_sha256']==helpers(),
        'Wrong v3 implementation pins')
    q=envelope['original_request'];r.validate_request(q,plan,allow_fixture)
    require(envelope['origin_catalog_sha256'] and c.SHA.fullmatch(envelope['origin_catalog_sha256']),
        'Missing catalog hash')
    origin.validate(catalog,q,allow_fixture)
    return q


def prepare(request,request_sha,plan,plan_sha,catalog,catalog_sha,archive_root,output,allow_fixture=False):
    request=core.plain_path(request,'file');plan=core.plain_path(plan,'file');catalog=core.plain_path(catalog,'file')
    archives=core.plain_path(archive_root,'dir');output=core.fresh_path(output)
    require(request.stat().st_size<=r.REQUEST_LIMIT and c.digest(request)==request_sha
        and catalog.stat().st_size<=origin.LIMIT and c.digest(catalog)==catalog_sha,'Bound input hash/size differs')
    raw=request.read_bytes();envelope=core.strict_json(raw);cat=core.strict_json(catalog.read_bytes())
    q=envelope['original_request'];_,plan_data,_=p.bound_plan(plan,plan_sha,q['source_revision'],'RP0000')
    validate_envelope(envelope,plan_data,cat,allow_fixture)
    require(q['plan_sha256']==plan_sha and envelope['origin_catalog_sha256']==catalog_sha,'Plan/catalog pins differ')
    require(not output.is_relative_to(archives) and not archives.is_relative_to(output),'Output/archive overlap')
    w.durable_directory(output);w.durable_new(output/'envelope.json',raw)
    inner=output/'original_request.json';w.durable_new(inner,core.json_bytes(q))
    report=r.preflight(SimpleNamespace(request=inner,request_sha256=c.digest(inner),plan=plan,
        plan_sha256=plan_sha,archive_root=archives,output=output/'preflight',allow_test_fixture=allow_fixture))
    ctx={'request':q,'envelope':envelope,'request_sha256':request_sha,'request_path':request,
        'plan_path':plan,'plan_sha256':plan_sha,'catalog':cat,'catalog_path':catalog,'catalog_sha256':catalog_sha,
        'archive_root':archives,'output':output,'preflight':report,'helper_sha256':helpers(),
        'pins':{request:request_sha,output/'envelope.json':request_sha,inner:c.digest(inner),plan:plan_sha,
            catalog:catalog_sha,output/'preflight/dry_run_plan.json':c.digest(output/'preflight/dry_run_plan.json')}}
    recheck(ctx,True);return ctx


def recheck(ctx,full=False):
    require(helpers()==ctx['helper_sha256'],'V3 helper changed')
    for path,digest in ctx['pins'].items():
        require(c.digest(core.plain_path(path,'file'))==digest,'Pinned publication input changed')
    require(core.strict_json(ctx['request_path'].read_bytes())==ctx['envelope']
        and ctx['envelope']['original_request']==ctx['request']
        and core.strict_json(ctx['catalog_path'].read_bytes())==ctx['catalog']
        and ctx['envelope']['origin_catalog_sha256']==ctx['catalog_sha256'],'Mixed request/catalog contexts')
    _,plan,_=p.bound_plan(ctx['plan_path'],ctx['plan_sha256'],ctx['request']['source_revision'],'RP0000')
    validate_envelope(ctx['envelope'],plan,ctx['catalog'],ctx['request']['test_fixture'])
    if full:
        for job in ctx['request']['jobs']:v.archive_path(ctx,job)


def checked_tool_revision():
    revision=v.checked_tool_revision();env=os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):env.pop(key)
    directory=Path(__file__).resolve().parent
    def git(*args):
        return subprocess.run(['git','-C',str(directory),*args],env=env,check=True,
            stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30).stdout
    top=core.plain_path(Path(git('rev-parse','--show-toplevel').decode().strip()),'dir').resolve()
    require(git('rev-parse','HEAD').decode().strip()==revision,'V3 checkout revision differs')
    for source in (Path(__file__),Path(origin.__file__),Path(budget.__file__)):
        source=source.resolve();require(source.is_relative_to(top),'V3 dependency outside committed checkout')
        require(git('show','HEAD:'+source.relative_to(top).as_posix())==source.read_bytes(),
            'V3 dependency is not its actual committed blob')
    return revision


def remaining_requests(n,a):
    require(type(n) is int and 1<=n<=32 and type(a) is int and 3<=a<=5,'Invalid partial/origin budget')
    return 5*n+a+19


def quota_decision(observed,n,a,epoch,monotonic):
    needed=remaining_requests(n,a)+RESERVE
    result={'allowed':False,'successful_path_requests':remaining_requests(n,a),'reserve_requests':RESERVE,
        'required_remaining':needed,'observed':observed,'atomic_reservation_claimed':False,
        'secondary_limit_guarantee':False}
    if observed is None:return {**result,'reason':'no_api_quota_observation'}
    if not observed.get('valid'):return {**result,'reason':observed.get('reason','invalid_observation')}
    if observed.get('http_status')!=200:return {**result,'reason':'latest_http_status_not_success'}
    age=monotonic-observed['captured_monotonic']
    if not all(math.isfinite(x) for x in (epoch,monotonic,age)) or age<0 or age>30:
        return {**result,'reason':'stale_or_invalid_observation_age'}
    if epoch>=observed['reset']:return {**result,'reason':'rate_window_expired'}
    if observed['remaining']<needed:return {**result,'reason':'insufficient_remaining'}
    return {**result,'allowed':True,'reason':'enough_observed_primary_quota'}


class BudgetHTTP(w.ReleaseHTTP):
    def __init__(self,ctx,journal,*,token,fixture=False,api='https://api.github.com'):
        require(isinstance(token,str) and token and type(fixture) is bool,'Explicit credential/fixture flag required')
        recheck(ctx);q=ctx['request'];require(q['test_fixture'] is fixture,'Client/context fixture boundary differs')
        if not fixture:
            require(ctx.get('preflight',{}).get('status')=='local_preflight_checked'
                and ctx['preflight'].get('test_fixture') is False,'Production requires actual archive preflight')
        self.ctx=ctx;self.request_bytes=core.json_bytes(q);self.catalog_bytes=core.json_bytes(ctx['catalog'])
        self.n=len(q['jobs']);self.a=origin.request_count(ctx['catalog']);remaining_requests(self.n,self.a)
        self.latest_quota=None;self.first_gate=None
        super().__init__(journal,token=token,fixture=fixture,api=api)
        self.opener=budget._ObservedOpener(self.opener,self)

    def _observe(self,request,headers,status,error_kind):
        u=urlsplit(request.full_url)
        approved=(u.scheme=='https' and u.hostname=='api.github.com' and u.port in (None,443)
            and not u.username and not u.password)
        if self.fixture:approved=(u.scheme=='http' and u.netloc=='127.0.0.1:1')
        if not approved:return
        observation={**budget.parse_rate_headers(headers),'http_status':status,'error_kind':error_kind,
            'captured_epoch':time.time(),'captured_monotonic':time.monotonic(),
            'endpoint_path':u.path,'method':request.get_method(),'token_recorded':False,
            'test_fixture':self.fixture,'credential_scope':'same_Actions_publisher_client'}
        self.latest_quota=observation;self.journal.event('quota_observation',observation)

    def mutate(self,method,suffix,payload=None,archive=None,name=None):
        if self.writes==0:
            recheck(self.ctx)
            require(core.json_bytes(self.ctx['request'])==self.request_bytes
                and core.json_bytes(self.ctx['catalog'])==self.catalog_bytes,'Guard/publisher context changed')
            q=self.ctx['request']
            require(method=='POST' and suffix==API+'/git/refs' and archive is None and name is None
                and payload=={'ref':'refs/tags/'+q['tag'],'sha':q['source_revision']},'Wrong first mutation')
            verdict=quota_decision(self.latest_quota,self.n,self.a,time.time(),time.monotonic());self.first_gate=verdict
            self.journal.event('prewrite_quota_gate',{'policy':'bulk-partial-v3','writes_before':0,
                'request_sha256':self.ctx['request_sha256'],'catalog_sha256':self.ctx['catalog_sha256'],
                'job_count':self.n,'decision':verdict,'automatic_wait':False,'automatic_retry':False})
            if not verdict['allowed']:raise budget.PrewriteBudgetClosed(verdict['reason'],verdict)
        return super().mutate(method,suffix,payload=payload,archive=archive,name=name)


def _publish(ctx,client,journal,environment=None):
    q=ctx['request'];jobs=q['jobs']
    require(isinstance(client,BudgetHTTP) and client.ctx is ctx and client.journal is journal
        and client.fixture is q['test_fixture'],'Publisher/client context differs')
    actions=None
    if not client.fixture:
        actions=w.actions_context(q,os.environ if environment is None else environment,checked_tool_revision())
    def check(full=False):
        recheck(ctx,full)
        if not client.fixture:require(checked_tool_revision()==q['publisher_revision'],'Publisher checkout moved')
    journal.event('started',{'schema':SCHEMA,'request_sha256':ctx['request_sha256'],
        'catalog_sha256':ctx['catalog_sha256'],'source_revision':q['source_revision'],
        'publisher_revision':q['publisher_revision'],'actions':actions,'scope':'partial',
        'jobs':[j['key'] for j in jobs],'test_fixture':client.fixture,'full_certificate_proved':False,
        'continuous_remote_invariance_claimed':False,'runner_loss_survival_claimed':False})
    try:
        check(True);before_origin=origin.observe(client,ctx['catalog'],q)
        commit,_=client.metadata(API+'/commits/'+q['source_revision']);require(commit['sha']==q['source_revision'],'Wrong source commit')
        client.absent(API+'/git/ref/tags/'+q['tag']);client.no_release_for_tag(q['tag'])
        tag=client.mutate('POST',API+'/git/refs',{'ref':'refs/tags/'+q['tag'],'sha':q['source_revision']})
        require(tag.get('ref')=='refs/tags/'+q['tag'],'Wrong created tag');w.exact_tag(client,q['tag'],q['source_revision'])
        release=client.mutate('POST',API+'/releases',{'tag_name':q['tag'],'target_commitish':q['source_revision'],
            'name':q['title'],'body':'Checked original numerical shard archives. Scope: partial. '+
                'Inter-shard assembly and complete classification are not claimed.',
            'draft':True,'prerelease':False,'generate_release_notes':False})
        rid=release['id'];require(type(rid) is int and rid>0,'Invalid release id')
        journal.event('created_draft',{'release_id':rid,'tag':q['tag']})
        expected={};by_key={};empty,_=v.release_snapshot(client,rid,q,expected,True)
        for job in jobs:
            check();archive=v.archive_path(ctx,job)
            current,_=client.metadata(API+'/releases/'+str(rid))
            identity=v.protocol.validate_release(current,rid,q['tag'],q['source_revision'],draft=True)
            require(identity==empty['release'],'Draft phase/source identity changed before upload')
            asset=client.mutate('POST',API+'/releases/'+str(rid)+'/assets',archive=archive,name=job['asset_name'])
            wanted=v.expected_asset(q,job,asset['id'])
            require({k:asset.get(k) for k in v.ASSET_CORE_KEYS}==wanted
                and wanted['id'] not in {x['id'] for x in expected.values()},'Upload response differs/reuses id')
            v.protocol.validate_asset(asset,identity,wanted['id'],job['asset_name'],job['archive_sha256'],job['archive_bytes'])
            expected[job['asset_name']]=wanted;by_key[job['key']]=wanted
            journal.event('uploaded_asset',{'key':job['key'],'release_id':rid,'asset_id':wanted['id']})
            v.archive_path(ctx,job)
        d0,_=v.release_snapshot(client,rid,q,expected,True)
        def binary(job,phase):
            result=client.binary(by_key[job['key']]['id'],job['archive_sha256'],job['archive_bytes'])
            journal.event('verified_binary',{'key':job['key'],'asset_id':by_key[job['key']]['id'],
                'phase':phase,**result,'test_fixture':client.fixture});return result
        for job in jobs:binary(job,'draft')
        check(True);require(origin.observe(client,ctx['catalog'],q)==before_origin,'Origin changed before publication')
        d1,_=v.release_snapshot(client,rid,q,expected,True);require(d1==d0,'Draft full snapshot changed across binaries')
        client.mutate('PATCH',API+'/releases/'+str(rid),{'draft':False})
        p0,_=v.release_snapshot(client,rid,q,expected,False);verifications={}
        for job in jobs:
            result=binary(job,'published');wanted=p0['assets'][job['asset_name']]
            row,ahash=client.metadata(API+'/releases/assets/'+str(wanted['id']))
            require(v.protocol.validate_asset(row,p0['release'],wanted['id'],job['asset_name'],
                job['archive_sha256'],job['archive_bytes'])==wanted,'Published post-binary asset differs')
            verifications[job['key']]={'asset_api_sha256':ahash,'redownload_sha256':result['sha256'],
                'redownload_bytes':result['bytes'],'verified_at':w.utc()}
        final,rhash=v.release_snapshot(client,rid,q,expected,False);require(final==p0,'Published full snapshot changed across binaries')
        check(True)
        publisher={'revision':q['publisher_revision'],'script_sha256':c.digest(__file__),
            'request_sha256':ctx['request_sha256'],'origin_catalog_sha256':ctx['catalog_sha256'],
            'actions':actions,'journal_previous_sha256':journal.previous}
        directory=journal.root/'records';w.durable_directory(directory);records=[]
        for job in jobs:
            record=v.make_record(q,job,final['assets'][job['asset_name']],verifications[job['key']],
                final['release'],rhash,client.fixture,publisher)
            raw=core.json_bytes(record);digest=p.sha(raw)
            if not client.fixture:p.durable_record(raw,digest,q['source_revision'],job['archive_sha256'],job['archive_bytes'])
            w.durable_new(directory/(job['key']+'.json'),raw)
            records.append({'key':job['key'],'record_sha256':digest,'record_bytes':len(raw),
                'archive_sha256':job['archive_sha256'],'archive_bytes':job['archive_bytes'],
                'release_id':rid,'asset_id':by_key[job['key']]['id']})
        summary={'schema':'rotating.shard-release-summary.v3','status':'fixture_only' if client.fixture else 'remote_verified',
            'repository':r.REPO,'source_revision':q['source_revision'],'scope':'partial','plan_sha256':q['plan_sha256'],
            'base_lock_sha256':q['base_lock_sha256'],'request_sha256':ctx['request_sha256'],
            'catalog_sha256':ctx['catalog_sha256'],'release_id':rid,'tag':q['tag'],'records':records,
            'publisher':publisher,'test_fixture':client.fixture,'actual_http_writes':client.writes,
            'remote_durability_verified':not client.fixture,'full_certificate_proved':False}
        w.durable_new(journal.root/'summary.json',core.json_bytes(summary))
        journal.event('finished',{'summary_sha256':c.digest(journal.root/'summary.json'),'records':len(records),
            'remote_durability_verified':not client.fixture});return summary
    except Exception as error:
        journal.event('failed',{'exception_type':type(error).__name__,
            'http_status':error.code if isinstance(error,HTTPError) else None,'writes_attempted':client.writes,
            'remote_cleanup_performed':False,'automatic_retry_performed':False,'recovery_requires_separate_review':True})
        raise


def publish_with_budget(ctx,journal,*,token,environment=None):
    """Only production entry. No caller-supplied count, catalog, or HTTP client."""
    require(ctx['request']['test_fixture'] is False,'Fixture context cannot enter production')
    recheck(ctx,True);client=BudgetHTTP(ctx,journal,token=token)
    return _publish(ctx,client,journal,environment)
