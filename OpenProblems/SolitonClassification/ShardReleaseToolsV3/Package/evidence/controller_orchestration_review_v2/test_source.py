"""Local orchestration stubs and real local Git identity; no network/Lean."""
from pathlib import Path
import argparse,copy,json,os,shutil,subprocess,sys
import production_shard_release_controller as ct
d,v,w,p,c,core=ct.d,ct.v,ct.w,ct.p,ct.c,ct.core


class Phases:
    def __init__(self,ctx,prior,scenario='good'):
        self.ctx=ctx;self.prior=prior;self.scenario=scenario;self.calls=[];self.tuples=[]
    def outer_prepare(self,*args,**kwargs):
        self.calls.append('outer_prepare');self.tuples.append(args[:6]);return d.prepare(*args,**kwargs)
    def outer_download(self,dc,*,token,environment):
        self.calls.append('outer_download');assert token=='fixture-only-no-production-token' and environment=={}
        if self.scenario=='outer_failure':raise ValueError('fixture outer failure')
        root=dc['output'];journal=w.Journal(root/'journal');journal.event('fixture_outer',{'orchestration_stub_only':True})
        q=dc['request']
        for job in q['jobs']:
            shutil.copyfile(self.prior/'archives'/job['archive'],root/'archives'/job['archive'])
            shutil.copyfile(self.prior/'zips'/(job['key']+'.zip'),root/'zips'/(job['key']+'.zip'))
        report=core.strict_json((self.prior/'receipt.json').read_bytes())
        report.update(request_sha256=dc['request_sha256'],catalog_sha256=dc['catalog_sha256'],
            checked_files=ct.inventory(root),orchestration_stub_only=True)
        if self.scenario=='outer_wrong_hash':report['request_sha256']='0'*64
        w.durable_new(root/'receipt.json',core.json_bytes(report));return report
    def publisher_prepare(self,*args,**kwargs):
        self.calls.append('publisher_prepare');self.tuples.append(args[:6]);assert kwargs=={'allow_fixture':True}
        request,request_sha,plan,plan_sha,catalog,catalog_sha,archives,root=args
        assert args[:6]==ct.arguments(self.ctx) and archives==self.ctx['output']/'download/archives'
        if self.scenario=='preflight_failure':raise ValueError('fixture preflight failure')
        w.durable_directory(root/'preflight');q=self.ctx['request']
        report={'status':'local_preflight_checked','test_fixture':True,'orchestration_stub_only':True,
            'archives':[{**j,'complete_original_archive_validated':True,'original_retained':True} for j in q['jobs']]}
        if self.scenario=='bad_preflight':report['archives']=[]
        w.durable_new(root/'envelope.json',request.read_bytes())
        w.durable_new(root/'original_request.json',core.json_bytes(q))
        w.durable_new(root/'preflight/dry_run_plan.json',core.json_bytes(report))
        return {'request_path':request,'request_sha256':request_sha,'plan_path':plan,'plan_sha256':plan_sha,
            'catalog_path':catalog,'catalog_sha256':catalog_sha,'archive_root':archives,'output':root,'preflight':report}
    def publisher_publish(self,pctx,journal,*,token,environment):
        self.calls.append('publisher_publish');assert token=='fixture-only-no-production-token'
        if self.scenario=='before_mutation':raise ValueError('fixture prewrite gate closed')
        journal.event('fixture_mutation_intent',{'orchestration_stub_only':True,'actual_remote_writes':0})
        if self.scenario=='after_intent':raise ValueError('fixture ambiguous mutation result')
        q=self.ctx['request'];w.durable_directory(journal.root/'records');records=[]
        for job in q['jobs']:
            raw=core.json_bytes({'test_fixture':True,'orchestration_stub_only':True,'key':job['key']})
            w.durable_new(journal.root/'records'/(job['key']+'.json'),raw)
            records.append({'key':job['key'],'record_sha256':p.sha(raw),'record_bytes':len(raw),
                'archive_sha256':job['archive_sha256'],'archive_bytes':job['archive_bytes'],
                'release_id':10,'asset_id':100})
        summary={'schema':'rotating.shard-release-summary.v3','status':'fixture_only','test_fixture':True,
            'remote_durability_verified':False,'scope':'partial','full_certificate_proved':False,
            'actual_http_writes':len(q['jobs'])+3,'request_sha256':self.ctx['request_sha256'],
            'plan_sha256':self.ctx['plan_sha256'],'catalog_sha256':self.ctx['catalog_sha256'],
            'source_revision':q['source_revision'],'base_lock_sha256':q['base_lock_sha256'],'tag':q['tag'],
            'publisher':{'revision':q['publisher_revision'],'script_sha256':c.digest(v.__file__)},
            'release_id':10,'records':records,'orchestration_stub_only':True}
        if self.scenario=='bad_summary':summary['catalog_sha256']='0'*64
        w.durable_new(journal.root/'summary.json',core.json_bytes(summary));journal.event('fixture_finished',{'actual_remote_writes':0})
        if self.scenario=='changed_old_stage':
            path=self.ctx['output']/'download/archives'/q['jobs'][0]['archive'];path.write_bytes(path.read_bytes()+b'!')
        if self.scenario=='changed_request':
            path=self.ctx['request_path'];path.write_bytes(path.read_bytes()+b' ')
        if self.scenario=='changed_record':
            path=journal.root/'records'/(q['jobs'][0]['key']+'.json');path.write_bytes(path.read_bytes()+b' ')
        if self.scenario=='extra_output':(self.ctx['output']/'extra.txt').write_text('unexpected')
        return summary
    def hooks(self):return ct.FixturePhases(self.outer_prepare,self.outer_download,self.publisher_prepare,self.publisher_publish)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prior',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--plan',type=Path,required=True)
    a=ap.parse_args();out=core.fresh_path(a.output);out.mkdir(parents=True);before=ct.helpers();test_sha=c.digest(__file__);rows=[]
    def context(name):
        inputs=out/(name+'_inputs');inputs.mkdir()
        for f in ('request.json','catalog.json'):shutil.copyfile(a.prior/'inputs'/f,inputs/f)
        return ct.prepare(request=inputs/'request.json',request_sha256=c.digest(inputs/'request.json'),
            plan=a.plan,plan_sha256=c.digest(a.plan),catalog=inputs/'catalog.json',
            catalog_sha256=c.digest(inputs/'catalog.json'),output=out/name,helper_sha256=before,_fixture=True)
    ctx=context('success');ph=Phases(ctx,a.prior);result=ct.execute_fixture(ctx,ph.hooks())
    assert result['status']=='fixture_orchestration_only' and not result['remote_durability_verified']
    assert ph.calls==['outer_prepare','outer_download','publisher_prepare','publisher_publish']
    assert ph.tuples==[ct.arguments(ctx)]*2
    success_hash=c.digest(ctx['output']/'receipt.json')
    scenarios=('outer_failure','outer_wrong_hash','preflight_failure','bad_preflight','before_mutation',
        'after_intent','bad_summary','changed_old_stage','changed_request','changed_record','extra_output')
    for scenario in scenarios:
        ctx=context(scenario);ph=Phases(ctx,a.prior,scenario)
        try:ct.execute_fixture(ctx,ph.hooks())
        except ValueError as error:
            assert not (ctx['output']/'receipt.json').exists()
            failure=core.strict_json((ctx['output']/'failure_inventory.json').read_bytes())
            assert failure['status']=='observed_partial_not_verified'
            if scenario.startswith('outer_'):assert 'publisher_prepare' not in ph.calls
            if scenario in ('preflight_failure','bad_preflight'):assert 'publisher_publish' not in ph.calls
            if scenario=='after_intent':assert list((ctx['output']/'release_journal').glob('*fixture_mutation_intent.json'))
            if scenario in ('bad_summary','changed_old_stage','changed_request','changed_record','extra_output'):
                assert (ctx['output']/'release_journal/summary.json').exists()
            assert ph.calls.count('publisher_publish')<=1
            rows.append({'case':scenario,'rejected':True,'error':str(error),'phase':failure['phase'],'calls':ph.calls})
        else:raise AssertionError('Accepted '+scenario)
    ctx=context('production_escape')
    try:ct.execute(ctx,token='not-a-real-token')
    except ValueError as error:rows.append({'case':'fixture_production_entry','error':str(error),'rejected':True})
    else:raise AssertionError('Fixture entered production')
    # Real local committed tool checkout, containing exactly the runtime files.
    root=out/'tools_git';tools=root/'tools';tools.mkdir(parents=True)
    for name,digest in before.items():
        source=Path(p.planner.reference.__file__) if name=='reference.py' else Path(ct.__file__).parent/name
        assert c.digest(source)==digest;shutil.copyfile(source,tools/name)
    env=os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):env.pop(key)
    env.update(GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL=os.devnull)
    def git(path,*args):return subprocess.run(['git','-C',str(path),*args],env=env,check=True,
        stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30).stdout.decode().strip()
    def commit(path):
        git(path,'init','-q');git(path,'add','--','.')
        git(path,'-c','core.hooksPath='+str((out/'empty_hooks').resolve()),'-c','commit.gpgsign=false',
            '-c','user.name=Local fixture','-c','user.email=fixture@example.invalid','commit','-q','-m','Local-only fixture')
        return git(path,'rev-parse','HEAD')
    (out/'empty_hooks').mkdir();prev=commit(root)
    def checktools():return subprocess.run([sys.executable,'-B','-c','import production_shard_release_controller as x; print(x.checked_tools())'],
        cwd=tools,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
    got=checktools();assert got.returncode==0 and got.stdout.decode().strip()==prev
    src=tools/Path(ct.__file__).name;raw=src.read_bytes();src.write_bytes(raw+b'\n# changed controller\n')
    got=checktools();assert got.returncode!=0 and b'actual committed blob' in got.stderr;src.write_bytes(raw)
    (tools/'unexpected.py').write_text('# extra helper')
    got=checktools();assert got.returncode!=0 and b'Extra/missing Python tool helper' in got.stderr
    # Retain tampered evidence in a separate directory; do not hide the failure.
    (tools/'unexpected.py').rename(root/'rejected_extra_helper.py')
    assert checktools().returncode==0
    inputs=out/'input_git';inputs.mkdir()
    for f in ('request.json','plan.json','catalog.json'):shutil.copyfile(a.prior/'inputs'/f,inputs/f)
    shutil.copytree(a.plan.parent/'checkpoints',inputs/'checkpoints')
    envelope=core.strict_json((inputs/'request.json').read_bytes());envelope['original_request']['publisher_revision']=prev
    (inputs/'request.json').write_bytes(core.json_bytes(envelope));qrev=commit(inputs)
    idctx={'input_checkout':inputs,'request':envelope['original_request'],
        'pins':{inputs/f:c.digest(inputs/f) for f in ('request.json','plan.json','catalog.json')}}
    identity=ct.input_identity(idctx,{'GITHUB_SHA':qrev});assert not identity['independent_external_Q_pin_performed_here']
    try:ct.input_identity(idctx,{'GITHUB_SHA':'0'*40})
    except ValueError:rows.append({'case':'wrong_input_Q','rejected':True})
    else:raise AssertionError('Accepted wrong Q')
    path=inputs/'catalog.json';path.write_bytes(path.read_bytes()+b' ')
    try:ct.input_identity(idctx,{'GITHUB_SHA':qrev})
    except ValueError:rows.append({'case':'dirty_input_commit','rejected':True})
    else:raise AssertionError('Accepted dirty input')
    assert ct.helpers()==before and c.digest(__file__)==test_sha
    report={'schema':'rotating.controller-orchestration-fixtures.v1','status':'checked','source_sha256':c.digest(ct.__file__),
        'test_sha256':test_sha,'helper_sha256':before,'success_receipt_sha256':success_hash,'rejections':rows,
        'actual_local_tool_commit':prev,'actual_local_input_commit':qrev,'dirty_controller_child_rejected':True,
        'extra_helper_child_rejected':True,'fixture_phases_are_stubs':True,'actual_full_preflight_run_here':False,
        'actual_protocol_HTTP_run_here':False,'actual_network_requests':0,'actual_remote_mutations':0,
        'actual_Lean_calls':0,'production_catalog_generated':False,'deployment_YAML_generated':False}
    w.durable_new(out/'report.json',core.json_bytes(report));print(json.dumps({'status':'checked',
        'rejections':len(rows),'report_sha256':c.digest(out/'report.json')}))


if __name__=='__main__':main()
