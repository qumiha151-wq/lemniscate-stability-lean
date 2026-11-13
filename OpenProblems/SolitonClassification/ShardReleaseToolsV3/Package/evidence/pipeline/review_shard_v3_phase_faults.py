"""Corrected twelve snapshot faults: E is never confused with nonempty D0."""
from pathlib import Path
from urllib.parse import urlsplit
import argparse,copy,json,traceback
import review_shard_release_publisher_v3 as t
s,w,p,c,core=t.s,t.w,t.p,t.c,t.core


class Wire(t.Wire):
    def __init__(self,q,catalog,scenario):
        super().__init__(q,catalog,scenario);self.fault_applied=0;self.fault_state=None
    def open(self,request,timeout):
        old=super().open(request,timeout);raw=old.read();status=old.status;old.close()
        if urlsplit(request.full_url).path==s.API+'/releases/10/assets' and request.get_method()=='GET':
            n=len(self.q['jobs']);done=sum(self.downloads.values())
            # E has zero uploaded assets. No fault applies there.
            if len(self.assets)==n:
                phase=('p0' if done==n else 'p1') if self.published else ('d0' if done==0 else 'd1')
                if self.scenario.startswith(phase+'_'):
                    assert done=={'d0':0,'d1':n,'p0':n,'p1':2*n}[phase]
                    values=json.loads(raw);assert len(values)==n>0
                    self.fault_applied+=1;assert self.fault_applied==1
                    self.fault_state={'phase':phase,'writes':len(self.writes),'binaries':done,'published':self.published}
                    fault=self.scenario.split('_')[1]
                    if fault=='extra':values.append({**values[0],'id':999,'name':'extra'})
                    elif fault=='missing':values=values[:-1]
                    else:assert fault=='duplicate';values.append(copy.deepcopy(values[0]))
                    raw=json.dumps(values).encode()
        return t.response(raw,status)


def main():
    ap=argparse.ArgumentParser()
    for name in ('prior','plan','output'):ap.add_argument('--'+name,type=Path,required=True)
    args=ap.parse_args();out=core.fresh_path(args.output);out.mkdir(parents=True)
    root=args.prior/'count_4';env=core.strict_json((root/'request.json').read_bytes())
    ctx={'request':env['original_request'],'envelope':env,'request_path':root/'request.json',
        'request_sha256':c.digest(root/'request.json'),'catalog':core.strict_json((root/'catalog.json').read_bytes()),
        'catalog_path':root/'catalog.json','catalog_sha256':c.digest(root/'catalog.json'),
        'plan_path':args.plan,'plan_sha256':c.digest(args.plan),'archive_root':root/'archives',
        'helper_sha256':s.helpers(),'pins':{root/'request.json':c.digest(root/'request.json'),
            root/'catalog.json':c.digest(root/'catalog.json'),args.plan:c.digest(args.plan)}}
    before=s.helpers();test_sha=c.digest(__file__);cases=[]
    for phase in ('d0','d1','p0','p1'):
        for fault in ('extra','missing','duplicate'):
            scenario=phase+'_'+fault;journal=w.Journal(out/scenario)
            client=s.BudgetHTTP(ctx,journal,token='fixture-token',fixture=True,api='http://127.0.0.1:1')
            wire=Wire(ctx['request'],ctx['catalog'],scenario);client.opener=s.budget._ObservedOpener(wire,client)
            try:s._publish(ctx,client,journal)
            except ValueError as error:
                frames=traceback.extract_tb(error.__traceback__)
                assert any(x.name=='release_snapshot' and Path(x.filename).resolve()==Path(s.v.__file__).resolve() for x in frames)
                wanted='Duplicate asset identity/name across pages' if fault=='duplicate' else 'Release contains missing/extra assets'
                assert str(error)==wanted
                assert wire.fault_applied==1
                n=len(ctx['request']['jobs']);published=phase.startswith('p')
                expected={'phase':phase,'writes':n+(3 if published else 2),
                    'binaries':{'d0':0,'d1':n,'p0':n,'p1':2*n}[phase],'published':published}
                assert wire.fault_state==expected and client.writes==expected['writes']
                assert sum(wire.downloads.values())==expected['binaries'] and wire.published is published
                assert not (journal.root/'summary.json').exists()
                cases.append({'case':scenario,'publisher_rejected':True,'exception_type':'ValueError',
                    'message':str(error),'fault_applied':1,**expected})
            else:raise AssertionError('Accepted '+scenario)
    assert before==s.helpers() and test_sha==c.digest(__file__)
    report={'schema':'rotating.v3-corrected-phase-faults.v1','status':'checked','test_sha256':test_sha,
        'runtime_helper_sha256':before,'cases':cases,'supersedes_only_phase_coverage_of':'EB816444522356F1E48DBFD422FE60B796DBF6E554C757A9C8A4485E5864F2E3',
        'old_d0_extra_duplicate_IndexErrors_count_as_protocol_coverage':False,
        'other_prior_Git_quota_pagination_tests_repeated':False,'network_requests':0,'actual_GitHub_writes':0,'new_Lean_calls':0}
    core.write_new(out/'report.json',core.json_bytes(report));print(json.dumps({'status':'checked','publisher_ValueError_rejections':len(cases),
        'report_sha256':c.digest(out/'report.json')}))


if __name__=='__main__':main()
