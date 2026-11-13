"""Read-only archive preflight and a nonexecuting release mutation plan.

There is deliberately no POST/PATCH/DELETE/upload implementation in this module.
The HTTP reader supports bounded metadata and complete asset verification only.
"""
from pathlib import Path
from urllib.parse import urlsplit
from urllib.request import Request,build_opener,HTTPRedirectHandler
from urllib.error import HTTPError
import argparse,hashlib,json,re,shutil,time
import production_public_projection as p
import production_core_artifact as core

c,require=p.compiler,p.require
REPO=p.REPOSITORY
SCHEMA='rotating.release-original-request.v1'
JSON_LIMIT=8*1024*1024
REQUEST_LIMIT=4*1024*1024


def helpers():
    return {**p.helpers(),Path(core.__file__).name:c.digest(core.__file__),
            Path(__file__).name:c.digest(__file__)}


def validate_request(request,plan,allow_fixture=False):
    require(set(request)=={'schema','test_fixture','repository','scope','layer','source_revision',
        'publisher_revision','plan_sha256','base_lock_sha256','tag','title','helper_sha256','jobs'},
        'Wrong release request fields')
    require(request['schema']==SCHEMA and request['repository']==REPO
        and request['layer']=='original-data' and request['scope'] in ('partial','full'), 'Wrong release scope')
    require(type(request['test_fixture']) is bool and (not request['test_fixture'] or allow_fixture),
            'Test-only request forbidden in production')
    require(request['source_revision']==plan['revision'], 'Wrong mathematical source revision')
    publisher=request['publisher_revision']
    require((publisher is None and request['test_fixture'])
        or (isinstance(publisher,str) and core.REVISION.fullmatch(publisher)), 'Missing exact publisher revision')
    require(c.SHA.fullmatch(request['base_lock_sha256']) and request['helper_sha256']==helpers(),
            'Wrong exact core or validation implementation')
    prefix='soliton-rotating-'+request['source_revision'][:12]+'-original-'
    require(isinstance(request['tag'],str) and request['tag'].startswith(prefix)
        and re.fullmatch('[A-Za-z0-9_.-]{1,160}',request['tag']), 'Noncanonical original-data tag')
    require(isinstance(request['title'],str) and 1<=len(request['title'])<=200
        and '\n' not in request['title'] and '\r' not in request['title'], 'Unsafe release title')
    jobs=request['jobs']
    require(isinstance(jobs,list) and (len(jobs)==250 if request['scope']=='full' else 1<=len(jobs)<=32),
            'Wrong partial/full requested coverage')
    lookup={j['key']:(i,j) for i,j in enumerate(plan['jobs'])}
    seen,indexes=set(),[]
    for job in jobs:
        require(set(job)=={'key','archive','archive_sha256','archive_bytes','asset_name',
            'origin_run_id','origin_head_sha','origin_artifact_id','origin_artifact_zip_sha256',
            'origin_artifact_zip_bytes'}, 'Wrong requested archive fields')
        require(job['key'] in lookup and job['key'] not in seen,'Duplicate/unknown archive job')
        seen.add(job['key']);indexes.append(lookup[job['key']][0])
        require(job['archive']==job['key']+'.tar.xz'
            and job['asset_name']=='SolitonClassification-'+job['key']+'-'+job['archive_sha256'][:16]+'.tar.xz',
            'Noncanonical archive or asset name')
        for name in ['archive_sha256','origin_artifact_zip_sha256']:
            require(isinstance(job[name],str) and c.SHA.fullmatch(job[name]), 'Invalid archive digest')
        require(isinstance(job['origin_head_sha'],str) and core.REVISION.fullmatch(job['origin_head_sha']),
                'Missing exact original workflow revision')
        for name in ['archive_bytes','origin_run_id','origin_artifact_id','origin_artifact_zip_bytes']:
            require(type(job[name]) is int and job[name]>0,'Invalid archive/origin size or id')
        require(job['archive_bytes']<2*1024**3,'Original asset exceeds release per-file cap')
    require(indexes==sorted(indexes),'Reordered source coverage')
    if request['scope']=='full':
        require(indexes==list(range(250)),'Incomplete full release request')
    return lookup


def preflight(args):
    request_path=core.plain_path(args.request,'file')
    require(request_path.stat().st_size<=REQUEST_LIMIT and c.digest(request_path)==args.request_sha256,
            'Externally pinned release request differs')
    raw=request_path.read_bytes();request=core.strict_json(raw)
    _,plan,_=p.bound_plan(args.plan,args.plan_sha256,request['source_revision'],'RP0000')
    require(request['plan_sha256']==args.plan_sha256,'Wrong pinned plan')
    lookup=validate_request(request,plan,args.allow_test_fixture)
    archives=core.plain_path(args.archive_root,'dir');output=core.fresh_path(args.output)
    require(not output.is_relative_to(archives) and not archives.is_relative_to(output), 'Output/archive overlap')
    output.mkdir(parents=True)
    stage=output/'_one_archive_validation'
    before=helpers();records=[]
    for job in request['jobs']:
        archive=core.plain_path(c.confined(archives,job['archive']),'file')
        require(archive.stat().st_size==job['archive_bytes'] and c.digest(archive)==job['archive_sha256'],
                'Original full archive changed')
        try:
            p.artifact.unpack(archive,stage,request['source_revision'],512*1024**2)
            read=lambda name:c.confined(stage,name).read_bytes()
            manifest,report,_,_=p.artifact.validate_bundle(read)
            require(p.sha(read('base_lock.json'))==request['base_lock_sha256'],'Wrong exact archived core')
            p.check_bundle_bindings(manifest,report,read('output_node.json'),plan,lookup[job['key']][1],
                                    args.plan,request['base_lock_sha256'])
            records.append({**job,'manifest_sha256':p.sha(read('manifest.json')),
                'compile_report_sha256':p.sha(read('compile_report.json')),
                'complete_original_archive_validated':True,'original_retained':True})
        finally:
            if stage.exists():
                target=core.plain_path(stage,'dir').resolve()
                require(target.parent==output.resolve() and target.name=='_one_archive_validation','Unsafe scratch cleanup')
                shutil.rmtree(target)
    for job in request['jobs']:
        require(c.digest(c.confined(archives,job['archive']))==job['archive_sha256'],'Original changed after validation')
    require(request_path.read_bytes()==raw and helpers()==before,'Request/helper changed')
    p.bound_plan(args.plan,args.plan_sha256,request['source_revision'],'RP0000')
    # A reviewable plan, not an API execution. Live absence/origin checks precede
    # eventual write implementation, which is intentionally absent from this tool.
    result={'schema':'rotating.release-dry-run.v1','status':'local_preflight_checked',
        'request_sha256':args.request_sha256,'test_fixture':request['test_fixture'],
        'source_revision':request['source_revision'],'publisher_revision':request['publisher_revision'],
        'tag':request['tag'],'scope':request['scope'],'archives':records,'helper_sha256':before,
        'planned_order':['verify_live_origins_and_absent_tag_release','create_exact_tag',
            'create_draft','upload_without_overwrite','verify_draft_assets',
            'publish','verify_published_assets_and_full_redownload','emit_durable_records'],
        'actual_http_writes':0,'live_origin_checks_performed':False,'release_created':False,
        'remote_durability_verified':False,'full_certificate_proved':False}
    core.write_new(output/'dry_run_plan.json',core.json_bytes(result))
    print(json.dumps({'status':result['status'],'archives':len(records),'actual_http_writes':0,
                      'release_created':False}),flush=True)
    return result


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(self,req,fp,code,msg,headers,newurl):
        return None


class ReadOnlyReleaseHTTP:
    """GET only. Fixture origin must be loopback; no publisher token is persisted."""
    def __init__(self,api='https://api.github.com',token=None,fixture=False):
        u=urlsplit(api)
        require((api=='https://api.github.com' and not fixture)
            or (fixture and u.scheme=='http' and u.hostname=='127.0.0.1' and u.port
                and u.path=='' and not u.query and not u.fragment), 'Unapproved API origin')
        self.api,self.token,self.fixture=api,token,fixture
        self.opener=build_opener(NoRedirect)

    def open(self,url,accept,authenticated=True):
        headers={'Accept':accept,'X-GitHub-Api-Version':'2022-11-28'}
        if authenticated and self.token:
            headers['Authorization']='Bearer '+self.token
        return self.opener.open(Request(url,headers=headers,method='GET'),timeout=30)

    def metadata(self,suffix):
        require(re.fullmatch(r'/repos/'+re.escape(REPO)+r'/[A-Za-z0-9_./-]+',suffix)
            and '..' not in suffix,'Unsafe metadata endpoint')
        with self.open(self.api+suffix,'application/vnd.github+json') as response:
            raw=response.read(JSON_LIMIT+1)
        require(len(raw)<=JSON_LIMIT,'Oversized API metadata')
        return core.strict_json(raw),p.sha(raw)

    def binary(self,asset_id,expected_sha,expected_bytes):
        require(type(asset_id) is int and asset_id>0 and c.SHA.fullmatch(expected_sha)
            and type(expected_bytes) is int and expected_bytes>0,'Invalid asset download identity')
        initial=self.api+'/repos/'+REPO+'/releases/assets/'+str(asset_id)
        try:
            response=self.open(initial,'application/octet-stream')
        except HTTPError as error:
            require(error.code==302,'Unexpected binary response')
            location=error.headers.get('Location','');error.close();u=urlsplit(location)
            approved=(u.scheme=='https' and u.hostname in {'release-assets.githubusercontent.com',
                'objects.githubusercontent.com','github-releases.githubusercontent.com'} and u.port in (None,443))
            if self.fixture:
                approved=(u.scheme=='http' and u.netloc==urlsplit(self.api).netloc)
            require(approved and not u.username and not u.password and not u.fragment,'Unapproved asset redirect')
            # Never forward API credentials, including to an approved signed host.
            response=self.open(location,'application/octet-stream',authenticated=False)
        digest=hashlib.sha256();size=0;deadline=time.monotonic()+300
        with response:
            require(response.status==200,'Unexpected final binary status')
            while True:
                require(time.monotonic()<deadline,'Asset total download time exceeded')
                block=response.read(min(1024*1024,expected_bytes-size+1))
                if not block:
                    break
                size+=len(block);require(size<=expected_bytes,'Asset longer than expected')
                digest.update(block)
        require(size==expected_bytes and digest.hexdigest()==expected_sha,'Incomplete/corrupt asset download')
        return {'sha256':digest.hexdigest(),'bytes':size}

    def verify_origin(self,job):
        run,_=self.metadata('/repos/'+REPO+'/actions/runs/'+str(job['origin_run_id']))
        asset,_=self.metadata('/repos/'+REPO+'/actions/artifacts/'+str(job['origin_artifact_id']))
        require(run['id']==job['origin_run_id'] and run['repository']['full_name']==REPO
            and run['head_sha']==job['origin_head_sha'] and run['status']=='completed'
            and run['conclusion']=='success','Original checked run differs/not successful')
        require(asset['id']==job['origin_artifact_id'] and asset['expired'] is False
            and asset['workflow_run']['id']==run['id'] and asset['workflow_run']['head_sha']==run['head_sha']
            and asset['size_in_bytes']==job['origin_artifact_zip_bytes']
            and asset['digest']=='sha256:'+job['origin_artifact_zip_sha256'],'Original Actions artifact differs')
        return True

    def verify_published(self,release_id,asset_id,tag,revision,name,expected_sha,expected_bytes):
        release_path='/repos/'+REPO+'/releases/'+str(release_id)
        asset_path='/repos/'+REPO+'/releases/assets/'+str(asset_id)
        release,rhash=self.metadata(release_path);asset,ahash=self.metadata(asset_path)
        ref,_=self.metadata('/repos/'+REPO+'/git/ref/tags/'+tag)
        require(release['id']==release_id and release['tag_name']==tag and release['draft'] is False
            and isinstance(release.get('published_at'),str) and release['published_at'], 'Release is not published')
        require(ref['ref']=='refs/tags/'+tag and ref['object']['type']=='commit'
            and ref['object']['sha']==revision,'Original tag target changed')
        expected_url='https://github.com/'+REPO+'/releases/download/'+tag+'/'+name
        require(asset['id']==asset_id and asset['name']==name and asset['state']=='uploaded'
            and asset['size']==expected_bytes and asset['digest']=='sha256:'+expected_sha
            and asset['browser_download_url']==expected_url,'Published asset metadata differs')
        # The release asset list binds the requested asset id to this release.
        require(any(a['id']==asset_id and a['name']==name for a in release['assets']), 'Asset belongs to another release')
        observed=self.binary(asset_id,expected_sha,expected_bytes)
        r2,_=self.metadata(release_path);a2,_=self.metadata(asset_path)
        ref2,_=self.metadata('/repos/'+REPO+'/git/ref/tags/'+tag)
        stable_asset=lambda row:{k:row.get(k) for k in ['id','name','state','size','digest','browser_download_url']}
        stable_release=lambda row:({k:row.get(k) for k in ['id','tag_name','draft','published_at','immutable']},
            sorted((a['id'],a['name'],a.get('size'),a.get('digest'),a.get('state')) for a in row['assets']))
        # download_count may legitimately increase because of this very download.
        require(stable_release(r2)==stable_release(release) and stable_asset(a2)==stable_asset(asset)
            and ref2==ref,'Publication identity changed during redownload')
        # Fixture results can never be mistaken for production durable records.
        return {'schema':'rotating.release-read-verification.v1','test_fixture':self.fixture,
            'remote_durable_record_eligible':not self.fixture,'release_id':release_id,'asset_id':asset_id,
            'asset_api_sha256':ahash,'release_api_sha256':rhash,'download':observed,
            'actual_http_writes':0}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['request','plan','archive-root','output']:
        parser.add_argument('--'+name,type=Path,required=True)
    for name in ['request-sha256','plan-sha256']:
        parser.add_argument('--'+name,required=True)
    parser.add_argument('--allow-test-fixture',action='store_true')
    preflight(parser.parse_args())


if __name__=='__main__':
    main()
