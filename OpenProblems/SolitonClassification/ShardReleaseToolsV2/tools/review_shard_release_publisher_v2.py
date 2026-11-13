"""Narrow draft-protocol regression; does not repeat the four archive preflights."""
from pathlib import Path
from http.client import HTTPResponse
from urllib.parse import urlsplit
import argparse,ast,copy,io,json,time
import production_shard_release_publisher_v2 as s
import production_shard_release_publisher as legacy
import review_shard_release_publisher as old
import review_core_release_publisher as coretest

w,r,p,c,core=s.w,s.r,s.p,s.c,s.core
old.s=s  # Only this isolated test process; no source or frozen artifact is changed.


class DraftWire(old.Wire):
    def open(self,request,timeout):
        response=super().open(request,timeout)
        if dict(request.header_items()).get('Accept')=='application/octet-stream':return response
        status=response.status;data=json.loads(response.read());response.close()
        slug=self.q['tag'] if self.published or self.scenario=='canonical_draft' else 'untagged-390c5b0e380000cfceb8'
        if self.scenario=='draft_slug_changes' and not self.published and any(self.downloads.values()):slug='untagged-'+'0'*20
        def asset(x):
            x=copy.deepcopy(x);x['url']='https://api.github.com/repos/'+r.REPO+'/releases/assets/'+str(x['id'])
            asset_slug=slug
            if self.scenario=='draft_asset_other_slug' and not self.published:asset_slug='untagged-'+'1'*20
            if self.scenario=='published_asset_keeps_draft' and self.published:asset_slug='untagged-390c5b0e380000cfceb8'
            x['browser_download_url']='https://github.com/'+r.REPO+'/releases/download/'+asset_slug+'/'+x['name']
            return x
        def release(x):
            x=copy.deepcopy(x);x['url']='https://api.github.com/repos/'+r.REPO+'/releases/10'
            x['target_commitish']='0'*40 if self.scenario=='wrong_release_target' else self.q['source_revision']
            release_slug='untagged-390c5b0e380000cfceb8' if self.scenario=='published_nonfinal_html' and self.published else slug
            host='example.invalid' if self.scenario=='draft_foreign_html' and not self.published else 'github.com'
            x['html_url']='https://'+host+'/'+r.REPO+'/releases/tag/'+release_slug
            x['assets']=[asset(a) for a in x.get('assets',[])];return x
        path=urlsplit(request.full_url).path
        if isinstance(data,dict) and path in (s.API+'/releases',s.API+'/releases/10') and 'tag_name' in data:data=release(data)
        elif isinstance(data,dict) and ('/releases/assets/' in path or path.endswith('/releases/10/assets')):data=asset(data)
        elif isinstance(data,list) and path.endswith('/releases/10/assets'):data=[asset(x) for x in data]
        raw=json.dumps(data).encode()
        result=HTTPResponse(coretest.MemorySocket(('HTTP/1.1 '+str(status)+' Fixture\r\nContent-Length: '+
            str(len(raw))+'\r\n\r\n').encode()+raw));result.begin();return result


def main():
    parser=argparse.ArgumentParser()
    for name in ['prior-fixture','plan','output']:parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args();out=core.fresh_path(args.output);out.mkdir(parents=True)
    started=time.perf_counter();prior=args.prior_fixture/'review.json'
    assert c.digest(prior)=='11f9e1ce4e944915cb15babecf870aa4a3f0108a38a2608488adbeabb1c9af59'
    assert c.digest(legacy.__file__)=='59381067b9972974cf3e2fe12a30c22038966075daa8e98c0d4807573a095cda'
    def functions(path):
        return {n.name:ast.dump(n,include_attributes=False) for n in ast.parse(Path(path).read_text(encoding='utf-8')).body
                if isinstance(n,ast.FunctionDef)}
    previous,current=functions(legacy.__file__),functions(s.__file__)
    unchanged=['prepare','archive_path','recheck','checked_tool_revision','validate_envelope']
    assert all(previous[name]==current[name] for name in unchanged)
    envelope=core.strict_json((args.prior_fixture/'actual_preflight_request.json').read_bytes())
    q=copy.deepcopy(envelope['original_request']);plan=p.load(args.plan)
    root=out/'synthetic_payloads';root.mkdir()
    for job in q['jobs']:
        path=root/job['archive'];path.write_bytes(('V2 SYNTHETIC '+job['key']+' NOT A PROOF\n').encode()*8)
        job.update(archive_sha256=c.digest(path),archive_bytes=path.stat().st_size,
            asset_name='SolitonClassification-'+job['key']+'-'+c.digest(path)[:16]+'.tar.xz')
    envelope.update(schema=s.SCHEMA,original_request=q,publisher_sha256=c.digest(s.__file__),helper_sha256=s.helpers())
    s.validate_envelope(envelope,plan,True)
    ctx={'request':q,'request_sha256':'a'*64,'plan_path':args.plan,'plan_sha256':c.digest(args.plan),
        'archive_root':root,'helper_sha256':s.helpers(),'pins':{}}
    cases=[];outcomes=[]
    def reject(name,fn):
        try:fn()
        except Exception as error:cases.append({'case':name,'exception_type':type(error).__name__,'rejected':True})
        else:raise AssertionError('Accepted '+name)
    positives=['good','canonical_draft','reordered_list']
    scenarios=positives+['failed_origin','expired_origin','existing_tag','existing_release',
        'fail_second_upload','ambiguous_second_upload','starter_second','duplicate_uploaded_id','extra_draft_asset',
        'changed_previous_asset','short_second_draft','tag_after_publish','missing_published_asset',
        'duplicate_published_asset','long_second_published','corrupt_last_published','changed_after_download',
        'draft_asset_other_slug','draft_foreign_html','wrong_release_target','draft_slug_changes',
        'published_nonfinal_html','published_asset_keeps_draft']
    for scenario in scenarios:
        journal=w.Journal(out/scenario);client=w.ReleaseHTTP(journal,api='http://127.0.0.1:1',token='fixture-token',fixture=True)
        wire=DraftWire(q,scenario);client.opener=wire
        if scenario in positives:
            summary=s.publish(ctx,client,journal)
            assert len(summary['records'])==4 and all(x==2 for x in wire.downloads.values()) and len(wire.writes)==7
            assert summary['status']=='fixture_only' and summary['remote_durability_verified'] is False
            for job in q['jobs']:
                raw=(journal.root/'records'/(job['key']+'.json')).read_bytes();record=core.strict_json(raw)
                assert '/download/'+q['tag']+'/' in record['asset']['browser_download_url']
                reject('fixture_record_'+scenario+'_'+job['key'],lambda raw=raw,job=job:p.durable_record(
                    raw,p.sha(raw),q['source_revision'],job['archive_sha256'],job['archive_bytes']))
        else:reject(scenario,lambda:s.publish(ctx,client,journal))
        events=coretest.verify_journal(journal.root)
        assert events[-1]['event']==('finished' if scenario in positives else 'failed')
        assert all(method in ('POST','PATCH') for method,path in wire.writes)
        if scenario in ['draft_asset_other_slug','draft_foreign_html','wrong_release_target','draft_slug_changes']:
            assert not wire.published
        outcomes.append({'scenario':scenario,'writes':len(wire.writes),'downloads':sum(wire.downloads.values()),
            'published_in_memory':wire.published,'journal_events':len(events)})
    # New phase-aware snapshot also handles a full250 page set structurally.
    wire=DraftWire(q);wire.tag={'ref':'refs/tags/'+q['tag'],'object':{'type':'commit','sha':q['source_revision']}}
    wire.release={'id':10,'tag_name':q['tag'],'draft':True,'published_at':None,'immutable':False,'assets':[]}
    expected={}
    for n in range(250):
        job={**q['jobs'][0],'asset_name':'synthetic'+str(n)+'.tar.xz'}
        wanted=s.expected_asset(q,job,100+n);wire.assets[100+n]=wanted;expected[job['asset_name']]=wanted
    journal=w.Journal(out/'pagination250');client=w.ReleaseHTTP(journal,api='http://127.0.0.1:1',token='fixture-token',fixture=True);client.opener=wire
    snap,_=s.release_snapshot(client,10,q,expected,True);assert len(snap['assets'])==250
    wire.assets[999]={**wire.assets[100],'id':999,'name':'extra'}
    reject('pagination_251',lambda:s.release_snapshot(client,10,q,expected,True))
    result={'schema':'rotating.shard-publisher-v2-review.v1','status':'checked',
        'source_sha256':c.digest(s.__file__),'protocol_sha256':c.digest(s.protocol.__file__),'test_sha256':c.digest(__file__),
        'prior_four_actual_preflight_report_sha256':c.digest(prior),'unchanged_preflight_function_AST':unchanged,
        'new_actual_archive_preflights':0,'actual_github_requests':0,'actual_github_writes':0,'actual_network_sockets':0,
        'new_Lean_elaborations':0,'full250_numerical_validation':False,'release_published':False,
        'synthetic_pagination_assets':250,'cases':cases,'scenarios':outcomes,'wall_seconds':time.perf_counter()-started}
    (out/'review.json').write_bytes(core.json_bytes(result))
    print(json.dumps({'status':'checked','scenarios':len(outcomes),'rejects':len(cases),
        'new_archive_preflights':0,'actual_github_writes':0,'wall_seconds':result['wall_seconds']}),flush=True)


if __name__=='__main__':main()
