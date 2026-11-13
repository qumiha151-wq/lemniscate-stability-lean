"""Four actual archive preflight plus explicitly synthetic in-memory publisher.

No socket or real GitHub mutation occurs. Tiny wire contexts do not claim their
payloads were numerical archives. Actual archive validation is separate below.
"""
from pathlib import Path
from http.client import HTTPResponse
from urllib.parse import urlsplit,parse_qs
from urllib.error import HTTPError
import argparse,copy,hashlib,io,json,os,shutil,time
import production_shard_release_publisher as s
import review_core_release_publisher as oldtest

w,r,p,c,core=s.w,s.r,s.p,s.c,s.core


class Wire:
    def __init__(self,q,scenario='good'):
        self.q=q;self.scenario=scenario;self.tag=None;self.release=None
        self.assets={};self.bodies={};self.writes=[];self.downloads={};self.published=False

    def open(self,request,timeout):
        assert timeout in (30,90)
        u=urlsplit(request.full_url);assert u.netloc=='127.0.0.1:1'
        path=u.path;method=request.get_method();headers=dict(request.header_items())
        q=self.q;scenario=self.scenario;data=None;status=200
        if method!='GET':
            assert method in ('POST','PATCH') and headers.get('Authorization')=='Bearer fixture-token'
            self.writes.append((method,path))
            raw=request.data.read() if hasattr(request.data,'read') else request.data
            assert len(raw)==int(headers['Content-length'])
            if path==s.API+'/git/refs':
                obj=json.loads(raw);self.tag={'ref':obj['ref'],'object':{'type':'commit','sha':obj['sha']}}
                data=self.tag;status=201
            elif path==s.API+'/releases':
                obj=json.loads(raw);assert obj['draft'] is True
                self.release={'id':10,'tag_name':q['tag'],'draft':True,'published_at':None,'immutable':False,'assets':[]}
                data=self.release;status=201
            elif path==s.API+'/releases/10/assets':
                number=len(self.assets)
                if scenario=='ambiguous_second_upload' and number==1:raise TimeoutError('synthetic ambiguous second upload')
                if scenario=='fail_second_upload' and number==1:
                    raise HTTPError(request.full_url,500,'synthetic upload failure',{},io.BytesIO(b'{}'))
                name=parse_qs(u.query)['name'][0];asset_id=100+number
                job=next(j for j in q['jobs'] if j['asset_name']==name)
                data=s.expected_asset(q,job,asset_id)
                assert len(raw)==job['archive_bytes'] and hashlib.sha256(raw).hexdigest()==job['archive_sha256']
                if scenario=='starter_second' and number==1:data['state']='starter'
                if scenario=='duplicate_uploaded_id' and number==1:data['id']=100
                self.assets[asset_id]=copy.deepcopy(data);self.bodies[asset_id]=raw;status=201
            elif path==s.API+'/releases/10' and method=='PATCH':
                assert len(self.assets)==len(q['jobs']) and all(self.downloads.get(k,0)>=1 for k in self.assets)
                assert json.loads(raw)=={'draft':False}
                self.published=True;self.release.update(draft=False,published_at='2026-11-13T00:00:00Z',immutable=True)
                data=self.release
            else:raise AssertionError('Forbidden write '+method+' '+path)
        elif path.startswith(s.API+'/actions/runs/'):
            job=next(j for j in q['jobs'] if str(j['origin_run_id'])==path.rsplit('/',1)[1])
            data={'id':job['origin_run_id'],'repository':{'full_name':r.REPO},'head_sha':job['origin_head_sha'],
                'status':'completed','conclusion':'failure' if scenario=='failed_origin' else 'success'}
        elif path.startswith(s.API+'/actions/artifacts/'):
            job=next(j for j in q['jobs'] if str(j['origin_artifact_id'])==path.rsplit('/',1)[1])
            data={'id':job['origin_artifact_id'],'expired':scenario=='expired_origin',
                'workflow_run':{'id':job['origin_run_id'],'head_sha':job['origin_head_sha']},
                'size_in_bytes':job['origin_artifact_zip_bytes'],'digest':'sha256:'+job['origin_artifact_zip_sha256']}
        elif path==s.API+'/commits/'+q['source_revision']:data={'sha':q['source_revision']}
        elif path==s.API+'/git/ref/tags/'+q['tag']:
            data=copy.deepcopy(self.tag)
            if data is None and scenario=='existing_tag':data={'ref':'existing'}
            if data is None:status=404
            elif scenario=='tag_after_publish' and self.published:data['object']['sha']='0'*40
        elif path==s.API+'/releases/tags/'+q['tag']:
            if scenario=='existing_release':data={'id':10}
            else:status=404
        elif path==s.API+'/releases':data=[]
        elif path==s.API+'/releases/10':
            data=copy.deepcopy(self.release)
            # Simulate a truncated embedded list: explicit pagination is authoritative.
            data['assets']=[copy.deepcopy(x) for x in list(self.assets.values())[:1]]
        elif path==s.API+'/releases/10/assets':
            page=int(parse_qs(u.query)['page'][0]);assert parse_qs(u.query)['per_page']==['100']
            values=list(self.assets.values())
            if scenario=='extra_draft_asset' and len(values)==2:
                values.append({**values[0],'id':999,'name':'extra'})
            if scenario=='missing_published_asset' and self.published:values=values[:-1]
            if scenario=='duplicate_published_asset' and self.published:values=values+[values[0]]
            if scenario=='changed_previous_asset' and len(values)>=2:
                values=copy.deepcopy(values);values[0]['digest']='sha256:'+'0'*64
            if scenario=='reordered_list':values=list(reversed(values))
            data=copy.deepcopy(values[(page-1)*100:page*100])
        elif path.startswith(s.API+'/releases/assets/'):
            aid=int(path.rsplit('/',1)[1]);data=copy.deepcopy(self.assets[aid])
            if headers.get('Accept')=='application/octet-stream':
                self.downloads[aid]=self.downloads.get(aid,0)+1;data=self.bodies[aid]
                if scenario=='short_second_draft' and aid==101 and not self.published:data=data[:-1]
                if scenario=='long_second_published' and aid==101 and self.published:data=data+b'!'
                if scenario=='corrupt_last_published' and aid==103 and self.published:data=bytes([data[0]^1])+data[1:]
            else:
                data['download_count']=self.downloads.get(aid,0)
                if scenario=='changed_after_download' and self.published and self.downloads.get(aid,0)>=2:data['size']+=1
        else:raise AssertionError('Unexpected read '+path)
        if status==404:data={'message':'Not Found'}
        raw=data if isinstance(data,bytes) else json.dumps(data).encode()
        response=HTTPResponse(oldtest.MemorySocket(('HTTP/1.1 '+str(status)+' Fixture\r\nContent-Length: '+
            str(len(raw))+'\r\n\r\n').encode()+raw));response.begin()
        if status>=300:raise HTTPError(request.full_url,status,'Fixture',response.headers,response)
        return response


def main():
    parser=argparse.ArgumentParser()
    for name in ['publication-root','plan','artifacts','output']:parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args();out=core.fresh_path(args.output);out.mkdir(parents=True)
    started=time.perf_counter();cases=[]
    def reject(name,fn):
        try:fn()
        except Exception as error:cases.append({'case':name,'rejected':True,'exception_type':type(error).__name__})
        else:raise AssertionError('Accepted '+name)
    plan=p.load(args.plan);artifacts=p.load(args.artifacts)['artifacts']
    archives=out/'actual_archives';archives.mkdir();jobs=[]
    for key in ['RP0000','RP3968','RM0000','RM3968']:
        sub='fourth_download' if key=='RM3968' else 'first_three_downloads'
        source_dir=args.publication_root/sub/key/'job'
        matches=list(source_dir.glob('*.tar.xz'));assert len(matches)==1
        source=matches[0];dest=archives/(key+'.tar.xz');shutil.copyfile(source,dest)
        origin=next(x for x in artifacts if x['name']=='rotating-first4-'+key+'-43354529340-1')
        digest=c.digest(dest)
        jobs.append({'key':key,'archive':dest.name,'archive_sha256':digest,'archive_bytes':dest.stat().st_size,
            'asset_name':'SolitonClassification-'+key+'-'+digest[:16]+'.tar.xz',
            'origin_run_id':43354529340,'origin_head_sha':'cef10f7ef398d1526c03c66f5ef84a71e697b3cb',
            'origin_artifact_id':origin['id'],'origin_artifact_zip_sha256':origin['digest'].removeprefix('sha256:'),
            'origin_artifact_zip_bytes':origin['size_in_bytes']})
    q={'schema':r.SCHEMA,'test_fixture':True,'repository':r.REPO,'scope':'partial','layer':'original-data',
        'source_revision':plan['revision'],'publisher_revision':'f'*40,'plan_sha256':c.digest(args.plan),
        'base_lock_sha256':'dcf9b162c42c30f387803fc9f395fcb1183f0e8179f5b46004782ba4bbf1f10d',
        'tag':'soliton-rotating-'+plan['revision'][:12]+'-original-four-wire-fixture',
        'title':'SYNTHETIC PUBLICATION FIXTURE, ACTUAL ARCHIVE PREFLIGHT','helper_sha256':r.helpers(),'jobs':jobs}
    envelope={'schema':s.SCHEMA,'original_request':q,'publisher_sha256':c.digest(s.__file__),'helper_sha256':s.helpers()}
    request=out/'actual_preflight_request.json';request.write_bytes(core.json_bytes(envelope))
    checked=s.prepare(request,c.digest(request),args.plan,c.digest(args.plan),archives,out/'actual_preflight',True)
    assert len(checked['preflight']['archives'])==4 and all(x['complete_original_archive_validated'] for x in checked['preflight']['archives'])
    for name,change in [('publisher_hash',lambda x:x.update(publisher_sha256='0'*64)),
        ('helper_hash',lambda x:x.update(helper_sha256={})),
        ('duplicate_jobs',lambda x:x['original_request']['jobs'].append(copy.deepcopy(jobs[0]))),
        ('noncanonical_order',lambda x:x['original_request']['jobs'].reverse()),
        ('four_claim_full',lambda x:x['original_request'].update(scope='full')),
        ('zero_jobs',lambda x:x['original_request'].update(jobs=[]))]:
        bad=copy.deepcopy(envelope);change(bad)
        reject(name,lambda bad=bad:s.validate_envelope(bad,plan,True))
    reject('fixture_production_rejected',lambda:s.validate_envelope(envelope,plan))
    wire_root=out/'synthetic_wire_payloads';wire_root.mkdir();wire_q=copy.deepcopy(q)
    for j in wire_q['jobs']:
        f=wire_root/j['archive'];f.write_bytes(('SYNTHETIC '+j['key']+'; NOT A LEAN ARCHIVE\n').encode()*8)
        j.update(archive_sha256=c.digest(f),archive_bytes=f.stat().st_size,
            asset_name='SolitonClassification-'+j['key']+'-'+c.digest(f)[:16]+'.tar.xz')
    # Fixture-only API context: no false numerical preflight report is constructed.
    # It is never accepted by the production CLI, which always calls prepare().
    ctx={'request':wire_q,'request_sha256':'a'*64,'plan_path':args.plan,'plan_sha256':c.digest(args.plan),
        'archive_root':wire_root,'helper_sha256':s.helpers(),'pins':{}}
    outcomes=[]
    for scenario in ['good','reordered_list','failed_origin','expired_origin','existing_tag','existing_release',
        'fail_second_upload','ambiguous_second_upload','starter_second','duplicate_uploaded_id','extra_draft_asset',
        'changed_previous_asset','short_second_draft','tag_after_publish','missing_published_asset',
        'duplicate_published_asset','long_second_published','corrupt_last_published','changed_after_download']:
        journal=w.Journal(out/('wire_'+scenario));client=w.ReleaseHTTP(journal,api='http://127.0.0.1:1',token='fixture-token',fixture=True)
        fixture=Wire(wire_q,scenario);client.opener=fixture
        if scenario in ('good','reordered_list'):
            summary=s.publish(ctx,client,journal)
            assert len(summary['records'])==4 and len(fixture.writes)==7 and all(x==2 for x in fixture.downloads.values())
            assert summary['status']=='fixture_only' and summary['remote_durability_verified'] is False
            for job in wire_q['jobs']:
                raw=(journal.root/'records'/(job['key']+'.json')).read_bytes()
                reject('fixture_record_'+scenario+'_'+job['key'],lambda raw=raw,job=job:p.durable_record(
                    raw,p.sha(raw),wire_q['source_revision'],job['archive_sha256'],job['archive_bytes']))
                # Pure schema compatibility assertion, not a saved production record.
                schema_example=core.strict_json(raw);schema_example.update(status='remote_verified',test_fixture=False)
                sample=core.json_bytes(schema_example)
                p.durable_record(sample,p.sha(sample),wire_q['source_revision'],job['archive_sha256'],job['archive_bytes'])
        else:reject(scenario,lambda:s.publish(ctx,client,journal))
        events=oldtest.verify_journal(journal.root)
        assert events[-1]['event']==('finished' if scenario in ('good','reordered_list') else 'failed')
        assert all(method in ('POST','PATCH') for method,path in fixture.writes)
        if scenario in ('fail_second_upload','ambiguous_second_upload','starter_second','extra_draft_asset',
                        'short_second_draft','changed_previous_asset'):assert not fixture.published
        outcomes.append({'scenario':scenario,'writes':len(fixture.writes),'downloads':sum(fixture.downloads.values()),
                         'published_in_memory':fixture.published,'journal_events':len(events)})
    # Standalone synthetic pagination crosses100. It is a set-check fixture only,
    # not a full request, numerical archive, actual GitHub response or250 proof.
    many=Wire(wire_q);many.tag={'ref':'refs/tags/'+wire_q['tag'],'object':{'type':'commit','sha':wire_q['source_revision']}}
    many.release={'id':10,'tag_name':wire_q['tag'],'draft':True,'published_at':None,'immutable':False,'assets':[]}
    expected={}
    for i in range(250):
        row={**jobs[0],'asset_name':'synthetic'+str(i)+'.tar.xz'}
        wanted=s.expected_asset(wire_q,row,100+i);many.assets[100+i]=wanted;expected[row['asset_name']]=wanted
    journal=w.Journal(out/'wire_pagination250');client=w.ReleaseHTTP(journal,api='http://127.0.0.1:1',token='fixture-token',fixture=True);client.opener=many
    snapshot,_=s.release_snapshot(client,10,wire_q,expected,True);assert len(snapshot['assets'])==250
    many.assets[999]={**many.assets[100],'id':999,'name':'too-many'}
    reject('pagination_251_rejected',lambda:s.release_snapshot(client,10,wire_q,expected,True))
    s.recheck(checked,True)
    report={'schema':'rotating.shard-release-wire-fixture.v1','status':'checked',
        'actual_original_archives_locally_validated':4,'actual_archive_hashes':{j['key']:j['archive_sha256'] for j in jobs},
        'actual_local_preflight_sha256':c.digest(checked['output']/'preflight/dry_run_plan.json'),
        'actual_github_requests':0,'actual_github_writes':0,'actual_network_sockets':0,'new_Lean_elaborations':0,
        'synthetic_pagination_assets':250,'full250_numerical_validation':False,'full_certificate_proved':False,
        'fixture_payloads_are_numerical_archives':False,'platform':os.name,'directory_fsync_exercised':os.name=='posix',
        'sources_sha256':{Path(x).name:c.digest(x) for x in [__file__,s.__file__]},
        'cases':cases,'scenarios':outcomes,'wall_seconds':time.perf_counter()-started}
    (out/'review.json').write_bytes(core.json_bytes(report))
    print(json.dumps({'status':'checked','actual_archive_preflights':4,'rejects':len(cases),
        'wire_scenarios':len(outcomes),'actual_github_writes':0,'wall_seconds':report['wall_seconds']}),flush=True)


if __name__=='__main__':main()
