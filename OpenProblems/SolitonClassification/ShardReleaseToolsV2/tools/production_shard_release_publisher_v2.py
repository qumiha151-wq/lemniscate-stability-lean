"""Journaled Layer A multi-shard publisher; local work uses wire fixtures only.

Frozen core HTTP/journal and original-data preflight are reused without edits.
No overwrite, deletion, tag movement, automatic retry or resume is implemented.
"""
from pathlib import Path
from types import SimpleNamespace
from urllib.error import HTTPError
import argparse,json,os,subprocess
import production_core_release_publisher as w
import production_release_url_protocol as protocol

r,c,core,require=w.r,w.c,w.core,w.require
p=r.p
API=w.API
SCHEMA='rotating.release-shards-envelope.v2'
FROZEN={
 'production_core_release_publisher.py':'c063b963b402cdce9354caac5451b6bf686ea2297a962e049649e97db2826eed',
 'production_core_release_request.py':'3cd4eb7e08f9e5e7d61a373d31aee03ac1bdd5eec3c1b67254ae925fbc2fe210',
 'production_release_preflight.py':'624df2b5af0c8350bdaeba353b811ae60de9ed17558eeff792da17cd0ff1cf2f',
 'production_release_url_protocol.py':'aaa1f9fbaa1b5b7e3ca12890638abdce4a25d28eb3b992889efa45e8157b1f7d'}
ASSET_KEYS=('id','name','state','size','digest','browser_download_url')
ASSET_CORE_KEYS=('id','name','state','size','digest')


def helpers():
    values={**w.adapter.helpers(),Path(w.__file__).name:c.digest(w.__file__),
            Path(protocol.__file__).name:c.digest(protocol.__file__),
            Path(__file__).name:c.digest(__file__)}
    require(all(values.get(k)==v for k,v in FROZEN.items()),'Frozen publisher/preflight dependency changed')
    return values


def validate_envelope(envelope,plan,allow_fixture=False):
    require(set(envelope)=={'schema','original_request','publisher_sha256','helper_sha256'},
            'Wrong shard envelope fields')
    require(envelope['schema']==SCHEMA and envelope['publisher_sha256']==c.digest(__file__)
        and envelope['helper_sha256']==helpers(),'Shard publisher implementation differs')
    q=envelope['original_request'];r.validate_request(q,plan,allow_fixture)
    require(q['plan_sha256'] and c.SHA.fullmatch(q['plan_sha256']),'Missing full plan digest')
    return q


def prepare(request,request_sha,plan,plan_sha,archive_root,output,allow_fixture=False):
    request=core.plain_path(request,'file');plan=core.plain_path(plan,'file')
    archives=core.plain_path(archive_root,'dir');output=core.fresh_path(output)
    require(request.stat().st_size<=r.REQUEST_LIMIT and c.digest(request)==request_sha,'Shard envelope pin differs')
    raw=request.read_bytes();envelope=core.strict_json(raw)
    q=envelope['original_request'];_,plan_data,_=p.bound_plan(plan,plan_sha,q['source_revision'],'RP0000')
    validate_envelope(envelope,plan_data,allow_fixture)
    require(q['plan_sha256']==plan_sha,'Request/full plan identity differs')
    require(not output.is_relative_to(archives) and not archives.is_relative_to(output),'Output/archive overlap')
    w.durable_directory(output)
    w.durable_new(output/'envelope.json',raw)
    inner=output/'original_request.json';w.durable_new(inner,core.json_bytes(q))
    inner_sha=c.digest(inner)
    report=r.preflight(SimpleNamespace(request=inner,request_sha256=inner_sha,plan=plan,plan_sha256=plan_sha,
        archive_root=archives,output=output/'preflight',allow_test_fixture=allow_fixture))
    ctx={'request':q,'envelope':envelope,'request_sha256':request_sha,'request_path':request,
        'plan_path':plan,'plan_sha256':plan_sha,'archive_root':archives,'output':output,
        'helper_sha256':helpers(),'preflight':report,
        'pins':{request:request_sha,output/'envelope.json':request_sha,inner:inner_sha,
                plan:plan_sha,output/'preflight/dry_run_plan.json':c.digest(output/'preflight/dry_run_plan.json')}}
    recheck(ctx,full=True)
    return ctx


def archive_path(ctx,job):
    path=core.plain_path(c.confined(ctx['archive_root'],job['archive']),'file')
    require(path.stat().st_size==job['archive_bytes'] and c.digest(path)==job['archive_sha256'],
            'Original shard archive changed')
    return path


def recheck(ctx,full=False):
    require(helpers()==ctx['helper_sha256'],'Publisher/helper bytes changed')
    for path,digest in ctx['pins'].items():
        require(c.digest(core.plain_path(path,'file'))==digest,'Bound publication input changed')
    if full:
        for job in ctx['request']['jobs']:archive_path(ctx,job)
        p.bound_plan(ctx['plan_path'],ctx['plan_sha256'],ctx['request']['source_revision'],'RP0000')


def checked_tool_revision():
    revision=w.checked_tool_revision()  # includes the actual frozen core writer blob
    directory=Path(__file__).resolve().parent;env=os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):env.pop(key)
    def git(*args):
        return subprocess.run(['git','-C',str(directory),*args],env=env,check=True,
            stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30).stdout
    top=core.plain_path(Path(git('rev-parse','--show-toplevel').decode().strip()),'dir').resolve()
    require(directory.is_relative_to(top) and git('rev-parse','HEAD').decode().strip()==revision,
            'Shard/core publisher checkouts differ')
    rel=Path(__file__).resolve().relative_to(top).as_posix()
    require(git('show','HEAD:'+rel)==Path(__file__).read_bytes(),'Shard publisher is not its committed tool blob')
    return revision


def stable_asset(asset):
    return {k:asset.get(k) for k in ASSET_KEYS}


def expected_asset(q,job,asset_id):
    require(type(asset_id) is int and asset_id>0,'Invalid uploaded asset id')
    return {'id':asset_id,'name':job['asset_name'],'state':'uploaded','size':job['archive_bytes'],
        'digest':'sha256:'+job['archive_sha256']}


def release_snapshot(client,release_id,q,expected,draft):
    """Complete explicit asset pagination, independent of embedded assets array."""
    release,rhash=client.metadata(API+'/releases/'+str(release_id))
    identity=protocol.validate_release(release,release_id,q['tag'],q['source_revision'],draft=draft)
    assets=[]
    for page in range(1,5):
        rows,_=client.metadata(API+'/releases/'+str(release_id)+'/assets?per_page=100&page='+str(page))
        require(isinstance(rows,list) and len(rows)<=100,'Invalid release-assets page')
        assets.extend(rows)
        require(len(assets)<=250,'Unexpected number of release assets')
        if len(rows)<100:break
    else:raise ValueError('Release-asset pagination did not terminate')
    require(len({x['id'] for x in assets})==len(assets) and len({x['name'] for x in assets})==len(assets),
            'Duplicate asset identity/name across pages')
    require({x['name'] for x in assets}==set(expected),'Release contains missing/extra assets')
    def checked(asset):
        wanted=expected[asset['name']]
        return protocol.validate_asset(asset,identity,wanted['id'],wanted['name'],
            wanted['digest'].removeprefix('sha256:'),wanted['size'])
    actual={x['name']:checked(x) for x in assets}
    require({n:{k:v[k] for k in ASSET_CORE_KEYS} for n,v in actual.items()}==expected,
            'Release contains changed asset identities')
    # The embedded array may be partial, but any embedded entry must agree.
    require(isinstance(release.get('assets'),list) and all(
        x['name'] in expected and checked(x)==actual[x['name']] for x in release['assets']),
        'Embedded release asset identity differs')
    w.exact_tag(client,q['tag'],q['source_revision'])
    return {'release':identity,'assets':actual},rhash


def verify_asset_bytes(client,job,wanted,identity):
    path=API+'/releases/assets/'+str(wanted['id'])
    def checked(asset):
        return protocol.validate_asset(asset,identity,wanted['id'],job['asset_name'],
            job['archive_sha256'],job['archive_bytes'])
    before,_=client.metadata(path);require(checked(before)==wanted,'Asset differs before redownload')
    observed=client.binary(wanted['id'],job['archive_sha256'],job['archive_bytes'])
    after,ahash=client.metadata(path);require(checked(after)==wanted,'Asset differs after redownload')
    return {'asset_api_sha256':ahash,'redownload_sha256':observed['sha256'],
            'redownload_bytes':observed['bytes'],'verified_at':w.utc()}


def make_record(q,job,wanted,verification,release,rhash,fixture,publisher):
    return {'schema':'rotating.durable-release-record.v1','kind':'publisher_verified_release_asset',
        'status':'fixture_only' if fixture else 'remote_verified','test_fixture':fixture,
        'repository':r.REPO,'revision':q['source_revision'],'key':job['key'],
        'base_lock_sha256':q['base_lock_sha256'],'plan_sha256':q['plan_sha256'],
        'release':{'id':release['id'],'tag':q['tag'],'draft':False,
            'published_at':release['published_at'],'immutable_observed':release.get('immutable')},
        'asset':wanted,'verification':{'method':'GitHub REST metadata plus full redownload',
            **verification,'release_api_sha256':rhash},'publisher':publisher,
        'remote_durability_verified':not fixture,'full_certificate_proved':False}


def publish(ctx,client,journal,environment=None):
    q=ctx['request'];jobs=q['jobs']
    require(client.fixture==q['test_fixture'] and client.journal is journal,'Fixture/journal boundary differs')
    actions=None
    if not client.fixture:
        actions=w.actions_context(q,environment if environment is not None else os.environ,checked_tool_revision())
    def check(full=False):
        recheck(ctx,full)
        if not client.fixture:require(checked_tool_revision()==q['publisher_revision'],'Publisher checkout moved')
    journal.event('started',{'schema':SCHEMA,'request_sha256':ctx['request_sha256'],
        'source_revision':q['source_revision'],'publisher_revision':q['publisher_revision'],'actions':actions,
        'scope':q['scope'],'jobs':[j['key'] for j in jobs],'test_fixture':client.fixture,
        'full_certificate_proved':False,'runner_loss_survival_claimed':False})
    try:
        check(True)
        for job in jobs:client.verify_origin(job)
        commit,_=client.metadata(API+'/commits/'+q['source_revision'])
        require(commit['sha']==q['source_revision'],'Wrong source commit')
        client.absent(API+'/git/ref/tags/'+q['tag']);client.no_release_for_tag(q['tag'])
        tag=client.mutate('POST',API+'/git/refs',{'ref':'refs/tags/'+q['tag'],'sha':q['source_revision']})
        require(tag['ref']=='refs/tags/'+q['tag'],'Wrong created tag');w.exact_tag(client,q['tag'],q['source_revision'])
        release=client.mutate('POST',API+'/releases',{'tag_name':q['tag'],'target_commitish':q['source_revision'],
            'name':q['title'],'body':'Checked original numerical shard archives. Scope: '+q['scope']+
                '. Inter-shard assembly and complete classification are not claimed.',
            'draft':True,'prerelease':False,'generate_release_notes':False})
        rid=release['id'];require(type(rid) is int and rid>0,'Invalid created release id')
        journal.event('created_draft',{'release_id':rid,'tag':q['tag']})
        expected={};release_snapshot(client,rid,q,expected,True)
        by_key={}
        for job in jobs:
            check();archive=archive_path(ctx,job)
            asset=client.mutate('POST',API+'/releases/'+str(rid)+'/assets',archive=archive,name=job['asset_name'])
            wanted=expected_asset(q,job,asset['id'])
            require({k:asset.get(k) for k in ASSET_CORE_KEYS}==wanted
                    and wanted['id'] not in {x['id'] for x in expected.values()},
                    'Uploaded response differs or reuses an asset id')
            expected[job['asset_name']]=wanted;by_key[job['key']]=wanted
            journal.event('uploaded_asset',{'key':job['key'],'release_id':rid,'asset_id':wanted['id']})
            before,_=release_snapshot(client,rid,q,expected,True)
            draft_asset=before['assets'][job['asset_name']]
            require(protocol.validate_asset(asset,before['release'],wanted['id'],job['asset_name'],
                job['archive_sha256'],job['archive_bytes'])==draft_asset,'Upload response presentation identity differs')
            verify_asset_bytes(client,job,draft_asset,before['release'])
            after,_=release_snapshot(client,rid,q,expected,True)
            require(after==before,'Draft identity/list changed during redownload')
            archive_path(ctx,job)
        check(True)
        for job in jobs:client.verify_origin(job)
        release_snapshot(client,rid,q,expected,True)
        client.mutate('PATCH',API+'/releases/'+str(rid),{'draft':False})
        start,_=release_snapshot(client,rid,q,expected,False)
        verifications={}
        for job in jobs:
            verifications[job['key']]=verify_asset_bytes(client,job,start['assets'][job['asset_name']],start['release'])
        final,rhash=release_snapshot(client,rid,q,expected,False)
        require(final==start,'Published release/full asset set changed during verification')
        check(True)
        publisher={'revision':q['publisher_revision'],'script_sha256':c.digest(__file__),
            'request_sha256':ctx['request_sha256'],'actions':actions,'journal_previous_sha256':journal.previous}
        directory=journal.root/'records';w.durable_directory(directory);records=[]
        for job in jobs:
            record=make_record(q,job,final['assets'][job['asset_name']],verifications[job['key']],
                               final['release'],rhash,client.fixture,publisher)
            raw=core.json_bytes(record);digest=p.sha(raw)
            if not client.fixture:
                p.durable_record(raw,digest,q['source_revision'],job['archive_sha256'],job['archive_bytes'])
            w.durable_new(directory/(job['key']+'.json'),raw)
            records.append({'key':job['key'],'record_sha256':digest,'record_bytes':len(raw),
                'archive_sha256':job['archive_sha256'],'archive_bytes':job['archive_bytes'],
                'release_id':rid,'asset_id':by_key[job['key']]['id']})
        summary={'schema':'rotating.shard-release-summary.v1','status':'fixture_only' if client.fixture else 'remote_verified',
            'repository':r.REPO,'source_revision':q['source_revision'],'scope':q['scope'],
            'plan_sha256':q['plan_sha256'],'base_lock_sha256':q['base_lock_sha256'],
            'request_sha256':ctx['request_sha256'],'release_id':rid,'tag':q['tag'],'records':records,
            'publisher':publisher,'test_fixture':client.fixture,'actual_http_writes':client.writes,
            'remote_durability_verified':not client.fixture,'full_certificate_proved':False}
        w.durable_new(journal.root/'summary.json',core.json_bytes(summary))
        journal.event('finished',{'summary_sha256':c.digest(journal.root/'summary.json'),
            'records':len(records),'remote_durability_verified':not client.fixture})
        return summary
    except Exception as error:
        journal.event('failed',{'exception_type':type(error).__name__,
            'http_status':error.code if isinstance(error,HTTPError) else None,'writes_attempted':client.writes,
            'remote_cleanup_performed':False,'automatic_retry_performed':False,
            'recovery_requires_separate_review':True})
        raise


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['request','plan','archive-root','output']:parser.add_argument('--'+name,type=Path,required=True)
    for name in ['request-sha256','plan-sha256']:parser.add_argument('--'+name,required=True)
    parser.add_argument('--execute',action='store_true');args=parser.parse_args()
    ctx=prepare(args.request,args.request_sha256,args.plan,args.plan_sha256,args.archive_root,args.output)
    if not args.execute:
        print(json.dumps({'status':'local_shard_preflight_checked','archives':len(ctx['request']['jobs']),
            'actual_http_writes':0,'release_created':False}));return
    w.actions_context(ctx['request'],os.environ,checked_tool_revision())
    token=os.environ.get('GH_TOKEN');require(token,'GH_TOKEN is absent')
    journal=w.Journal(ctx['output']/'journal');client=w.ReleaseHTTP(journal,token=token)
    summary=publish(ctx,client,journal)
    print(json.dumps({'status':summary['status'],'release_id':summary['release_id'],
        'archives':len(summary['records']),'remote_durability_verified':summary['remote_durability_verified']}))


if __name__=='__main__':main()
