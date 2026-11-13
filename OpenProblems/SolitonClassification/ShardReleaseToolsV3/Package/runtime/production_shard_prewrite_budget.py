"""A separately versioned first-write quota guard for frozen partial publishers.

No CLI, sleeps, retry, credential discovery or standalone publication path.
The caller must still execute the frozen validated Actions publisher protocol.
"""
from pathlib import Path
from urllib.error import HTTPError
from urllib.parse import urlsplit
import hashlib,math,re,time
import production_shard_release_publisher_v2 as v

SOURCE='cff971bcac7ac2d83aba04596ce09e44fda1ac29'
PLAN_SHA='a62ef654ec4f2fd01d55b6dae19c28483dba137c424c3068a372c514b89559c1'
BASE_SHA='dcf9b162c42c30f387803fc9f395fcb1183f0e8179f5b46004782ba4bbf1f10d'
WRITER_SHA='cba63be08c987643a1bbf86aeb5793171667b433dc2a4bbacd962817fdf90b38'
RESERVE_REQUESTS=100
MAX_HEADER_AGE_SECONDS=30
RATE_HEADERS=('x-ratelimit-resource','x-ratelimit-limit','x-ratelimit-remaining','x-ratelimit-reset')


class PrewriteBudgetClosed(RuntimeError):
    """No mutation was attempted. This is not an HTTP permission diagnosis."""
    def __init__(self,reason,decision):
        self.reason=reason;self.decision=decision
        super().__init__('Prewrite quota gate closed: '+reason)


def helpers():
    out=v.helpers()
    v.require(out.get('production_shard_release_publisher_v2.py')==WRITER_SHA,'Frozen v2 publisher changed')
    return {**out,Path(__file__).name:v.c.digest(__file__)}


def remaining_requests(n):
    v.require(type(n) is int and 1<=n<=32,'Only partial batches of1..32 are supported')
    return 15*n+16


def parse_rate_headers(headers):
    """Missing, duplicate or malformed fields never become a fabricated zero."""
    if headers is None or not hasattr(headers,'items'):
        return {'valid':False,'reason':'missing_or_duplicate_headers'}
    values={k:[] for k in RATE_HEADERS}
    for key,value in headers.items():
        if not isinstance(key,str):return {'valid':False,'reason':'malformed_header_names'}
        low=key.lower()
        if low in values:values[low].append(value)
    if any(len(xs)!=1 or not isinstance(xs[0],str) for xs in values.values()):
        return {'valid':False,'reason':'missing_or_duplicate_headers'}
    raw={k:xs[0] for k,xs in values.items()}
    if raw['x-ratelimit-resource']!='core':
        return {'valid':False,'reason':'wrong_rate_resource','headers':raw}
    names=RATE_HEADERS[1:]
    if any(re.fullmatch('[0-9]{1,12}',raw[k]) is None for k in names):
        return {'valid':False,'reason':'malformed_rate_numbers','headers':raw}
    limit,remaining,reset=(int(raw[k]) for k in names)
    if limit<=0 or remaining>limit or reset<=0:
        return {'valid':False,'reason':'inconsistent_rate_numbers','headers':raw}
    return {'valid':True,'resource':'core','limit':limit,'remaining':remaining,'reset':reset,'headers':raw}


def decision(observed,n,now_epoch,now_monotonic):
    needed=remaining_requests(n)+RESERVE_REQUESTS
    result={'allowed':False,'successful_path_requests':remaining_requests(n),
        'reserve_requests':RESERVE_REQUESTS,'required_remaining':needed,'observed':observed}
    if observed is None:return {**result,'reason':'no_api_quota_observation'}
    if not observed.get('valid'):return {**result,'reason':observed.get('reason','invalid_observation')}
    if observed.get('http_status')!=200:return {**result,'reason':'latest_http_status_not_success'}
    age=now_monotonic-observed['captured_monotonic']
    if not all(math.isfinite(x) for x in (now_epoch,now_monotonic,age)) or age<0 or age>MAX_HEADER_AGE_SECONDS:
        return {**result,'reason':'stale_or_invalid_observation_age'}
    if now_epoch>=observed['reset']:return {**result,'reason':'rate_window_expired'}
    if observed['remaining']<needed:return {**result,'reason':'insufficient_remaining'}
    return {**result,'allowed':True,'reason':'enough_observed_primary_quota','observation_age_seconds':age,
        'atomic_reservation_claimed':False,'secondary_limit_guarantee':False}


class _ObservedOpener:
    def __init__(self,transport,owner):self.transport,self.owner=transport,owner
    def open(self,request,*args,**kwargs):
        try:response=self.transport.open(request,*args,**kwargs)
        except HTTPError as error:
            self.owner._observe(request,error.headers,error.code,'HTTPError')
            raise
        except Exception:
            self.owner._observe(request,{},None,'no_response')
            raise
        self.owner._observe(request,response.headers,response.status,None)
        return response


class PrewriteBudgetHTTP(v.w.ReleaseHTTP):
    """Intercept the existing opener, so normal and HTTPError headers are seen.

    Only production api.github.com replies are quota observations. Signed CDN
    and upload-host replies cannot overwrite the prior API observation. The
    production superclass still supplies the approved endpoints and transport.
    """
    def __init__(self,journal,request,plan_path,*,token):
        v.require(isinstance(token,str) and bool(token),'Explicit publisher credential is required')
        self._request=request
        self._request_bytes=v.core.json_bytes(request)
        self._plan_path=v.core.plain_path(plan_path,'file')
        _,plan,_=v.p.bound_plan(self._plan_path,PLAN_SHA,SOURCE,'RP0000')
        v.r.validate_request(request,plan,allow_fixture=False)
        v.require(request['scope']=='partial' and request['source_revision']==SOURCE
            and request['plan_sha256']==PLAN_SHA and request['base_lock_sha256']==BASE_SHA,
            'Wrong partial/source/plan/core scope')
        self.n=len(request['jobs']);remaining_requests(self.n)
        self._helper_hashes=helpers();self.latest_quota=None;self.first_gate=None
        super().__init__(journal,token=token)
        self.opener=_ObservedOpener(self.opener,self)

    def _observe(self,request,headers,status,error_kind):
        url=request.full_url if hasattr(request,'full_url') else str(request)
        u=urlsplit(url)
        if not (u.scheme=='https' and u.hostname=='api.github.com' and u.port in (None,443)
                and not u.username and not u.password):return
        observation={**parse_rate_headers(headers),'http_status':status,'error_kind':error_kind,
            'captured_epoch':time.time(),'captured_monotonic':time.monotonic(),
            'endpoint_path':u.path,'method':request.get_method() if hasattr(request,'get_method') else 'GET',
            'credential_scope':'same_Actions_publisher_client','token_recorded':False}
        self.latest_quota=observation
        self.journal.event('quota_observation',observation)

    def mutate(self,method,suffix,payload=None,archive=None,name=None):
        if self.writes==0:
            v.require(method=='POST' and suffix==v.API+'/git/refs' and archive is None and name is None
                and payload=={'ref':'refs/tags/'+self._request['tag'],'sha':SOURCE},
                'First mutation must be the frozen exact-tag operation')
            v.require(v.core.json_bytes(self._request)==self._request_bytes
                and len(self._request['jobs'])==self.n and helpers()==self._helper_hashes
                and v.c.digest(self._plan_path)==PLAN_SHA,'Bound request/source/helper changed')
            verdict=decision(self.latest_quota,self.n,time.time(),time.monotonic())
            self.first_gate=verdict
            self.journal.event('prewrite_quota_gate',{'policy':'partial-first-write-v1',
                'writes_before':self.writes,'request_sha256':hashlib.sha256(self._request_bytes).hexdigest(),
                'job_count':self.n,'decision':verdict,'automatic_wait':False,'automatic_retry':False})
            if not verdict['allowed']:raise PrewriteBudgetClosed(verdict['reason'],verdict)
        # Once writes>0, errors follow the original fail-closed publisher path.
        # This wrapper never loops, sleeps, retries, resumes or cleans up remotely.
        return super().mutate(method,suffix,payload=payload,archive=archive,name=name)


def publish_with_prewrite_budget(ctx,journal,*,token,environment=None):
    """Deployment entry: construct the guard from the SAME actual frozen context.

    There is no caller-supplied N/client, so a smaller unrelated request cannot
    be used to authorize a larger batch. A future reviewed Actions workflow
    must additionally pin this wrapper's committed source/package bytes.
    """
    v.recheck(ctx)
    actual=v.core.strict_json(v.core.plain_path(ctx['request_path'],'file').read_bytes())
    v.require(actual==ctx['envelope'] and actual['original_request']==ctx['request'],
              'Quota and publisher request contexts differ')
    _,plan,_=v.p.bound_plan(ctx['plan_path'],PLAN_SHA,SOURCE,'RP0000')
    v.validate_envelope(actual,plan)
    client=PrewriteBudgetHTTP(journal,ctx['request'],ctx['plan_path'],token=token)
    return v.publish(ctx,client,journal,environment=environment)
