"""Narrow post-inventory tamper and full-plan local Git identity tests."""
from pathlib import Path
import argparse,json,os,shutil,subprocess
import production_shard_release_controller as ct
import review_shard_release_controller as old
d,v,w,p,c,core=ct.d,ct.v,ct.w,ct.p,ct.c,ct.core


def main():
    ap=argparse.ArgumentParser()
    for name in ('prior','plan','output'):ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();out=core.fresh_path(a.output);out.mkdir(parents=True)
    helper=ct.helpers();test_sha=c.digest(__file__);rows=[]
    def context(name):
        inputs=out/(name+'_inputs');inputs.mkdir()
        for f in ('request.json','catalog.json'):shutil.copyfile(a.prior/'inputs'/f,inputs/f)
        shutil.copyfile(a.plan,inputs/'plan.json');shutil.copytree(a.plan.parent/'checkpoints',inputs/'checkpoints')
        ctx=ct.prepare(request=inputs/'request.json',request_sha256=c.digest(inputs/'request.json'),
            plan=inputs/'plan.json',plan_sha256=c.digest(inputs/'plan.json'),catalog=inputs/'catalog.json',
            catalog_sha256=c.digest(inputs/'catalog.json'),output=out/name,helper_sha256=helper,_fixture=True)
        assert len(ctx['pins'])==253
        return ctx,inputs
    original=ct.exact_files
    for which in ('request','checkpoint'):
        ctx,inputs=context('late_'+which);phases=old.Phases(ctx,a.prior);state={'fault_applied':0,'long_walk_completed':False}
        def inject(root,expected):
            result=original(root,expected)
            if root==ctx['output']:
                assert state['fault_applied']==0
                state['long_walk_completed']=True
                target=ctx['request_path'] if which=='request' else inputs/'checkpoints/p_0032.json'
                target.write_bytes(target.read_bytes()+b' ');state['fault_applied']+=1
            return result
        ct.exact_files=inject
        try:
            try:ct.execute_fixture(ctx,phases.hooks())
            except ValueError as error:
                assert str(error)=='Controller input/helper changed' and state=={'fault_applied':1,'long_walk_completed':True}
                assert phases.calls==['outer_prepare','outer_download','publisher_prepare','publisher_publish']
                assert (ctx['output']/'release_journal/summary.json').exists()
                assert not (ctx['output']/'receipt.json').exists() and not (ctx['output']/'checked_files.json').exists()
                fail=core.strict_json((ctx['output']/'failure_inventory.json').read_bytes())
                assert fail['phase']=='final_postcheck'
                rows.append({'case':'late_'+which,**state,'error':str(error),'publication_summary_retained':True,
                    'successful_receipt_written':False})
            else:raise AssertionError('Accepted late '+which)
        finally:ct.exact_files=original
    # Actual local Git Q containing the full exact 253-file prepare closure.
    ctx,inputs=context('full_Q_identity');env=os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):env.pop(key)
    env.update(GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL=os.devnull)
    hooks=out/'empty_hooks';hooks.mkdir()
    def git(*args):return subprocess.run(['git','-C',str(inputs),*args],env=env,check=True,
        stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30).stdout.decode().strip()
    git('init','-q');git('add','--','.')
    git('-c','core.hooksPath='+str(hooks.resolve()),'-c','commit.gpgsign=false','-c','user.name=Local fixture',
        '-c','user.email=fixture@example.invalid','commit','-q','-m','Local full 250 checkpoint input fixture')
    qrev=git('rev-parse','HEAD');ctx['input_checkout']=inputs
    identity=ct.input_identity(ctx,{'GITHUB_SHA':qrev})
    assert identity['input_revision']==qrev and identity['independent_external_Q_pin_performed_here'] is False
    checkpoint=inputs/'checkpoints/p_0032.json';assert checkpoint in ctx['pins']
    checkpoint.write_bytes(checkpoint.read_bytes()+b' ')
    try:ct.input_identity(ctx,{'GITHUB_SHA':qrev})
    except ValueError as error:
        assert str(error)=='Input is not its actual workflow-commit blob'
        rows.append({'case':'dirty_checkpoint_actual_Git','error':str(error),'full_prepare_pin_count':len(ctx['pins'])})
    else:raise AssertionError('Accepted dirty committed checkpoint')
    assert ct.helpers()==helper and c.digest(__file__)==test_sha
    report={'schema':'rotating.controller-final-recheck-tests.v1','status':'checked','source_sha256':c.digest(ct.__file__),
        'test_sha256':test_sha,'old_fixture_source_sha256':c.digest(old.__file__),'helper_sha256':helper,
        'cases':rows,'actual_clean_full_Q_identity':identity,'checkpoint_pin_count':250,'total_prepare_pins':253,
        'orchestration_phases_are_stubs':True,'actual_remote_mutations':0,'actual_network_requests':0,
        'actual_full_preflight_calls':0,'actual_Lean_calls':0,'new_production_catalog':False,
        'existing_43832_report_unchanged':True}
    w.durable_new(out/'report.json',core.json_bytes(report));print(json.dumps({'status':'checked',
        'cases':len(rows),'report_sha256':c.digest(out/'report.json')}))


if __name__=='__main__':main()
