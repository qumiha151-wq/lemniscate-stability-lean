"""Synthetic evidence format tests and a rejected real isolated CLI call.

The synthetic success receipt is intentionally fabricated for a local format
test. It is never a real controller/HTTP success or a production catalog.
"""
from pathlib import Path
import argparse,copy,json,os,shutil,subprocess,sys
import shard_release_v3_launch as launch
import production_shard_release_controller as controller


def main():
    ap=argparse.ArgumentParser()
    for name in ('formal-root','package','tool-checkout','output'):ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();formal=a.formal_root.resolve();out=a.output.resolve();assert not out.exists();out.mkdir(parents=True)
    before={str(Path(x.__file__)):launch.digest(Path(x.__file__)) for x in (launch,controller)};test_sha=launch.digest(Path(__file__))
    package=a.package.resolve();msha=launch.digest(package/'package_manifest.json');verified=launch.verify_package(package,msha)
    original=formal/'controller_orchestration_review_v2/success';inputs=formal/'controller_orchestration_review_v2/success_inputs'
    plan=formal/'production_pipeline_package_v1/plan/plan.json';q=launch.strict((inputs/'request.json').read_bytes())['original_request']
    pins={inputs/'request.json':launch.digest(inputs/'request.json'),inputs/'catalog.json':launch.digest(inputs/'catalog.json'),plan:launch.digest(plan)}
    for row in launch.strict(plan.read_bytes())['jobs']:pins[plan.parent/row['output_node']]=row['output_node_sha256']
    def synthetic(name):
        root=out/name;shutil.copytree(original,root)
        receipt=launch.strict((root/'receipt.json').read_bytes())
        receipt.update(status='checked',test_fixture=False,helper_sha256=launch.FROZEN_RUNTIME,
            synthetic_evidence_only=True,not_an_actual_controller_success=True)
        (root/'receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n',encoding='utf-8')
        return {'output':root,'input_checkout':formal,'pins':dict(pins),'request':q}
    ctx=synthetic('SYNTHETIC_SUCCESS_NOT_A_PROOF')
    result=launch.evidence(controller,ctx,verified,out/'synthetic_compact',True)
    table=launch.strict((out/'synthetic_compact/inventory.json').read_bytes())
    assert result['originals_copied']==0 and len(table['files'])==result['compact_files']
    for name,row in table['files'].items():
        path=out/'synthetic_compact/files'/name
        assert launch.digest(path)==row['sha256'] and path.stat().st_size==row['bytes']
    assert not list((out/'synthetic_compact').rglob('*.tar.xz')) and not list((out/'synthetic_compact').rglob('*.zip'))
    cases=[]
    for fault in ('changed_file','missing_file','extra_file','receipt_pin'):
        ctx=synthetic('synthetic_'+fault);root=ctx['output'];fault_count=0
        target=next((root/'controller').glob('*_started.json'))
        if fault=='changed_file':target.write_bytes(target.read_bytes()+b' ');fault_count+=1
        elif fault=='missing_file':target.rename(out/('preserved_'+fault+'.json'));fault_count+=1
        elif fault=='extra_file':(root/'unexpected.json').write_text('{}');fault_count+=1
        else:
            receipt=launch.strict((root/'receipt.json').read_bytes());receipt['inventory_sha256']='0'*64
            (root/'receipt.json').write_text(json.dumps(receipt)+'\n',encoding='utf-8');fault_count+=1
        expected='Wrong controller inventory' if fault=='receipt_pin' else 'Controller evidence differs after completion'
        try:launch.evidence(controller,ctx,verified,out/('rejected_'+fault),True)
        except ValueError as error:
            assert str(error)==expected and fault_count==1
            assert not (out/('rejected_'+fault)/'inventory.json').exists()
            cases.append({'case':fault,'fault_count':fault_count,'exception_type':'ValueError','message':str(error),'rejected':True})
        else:raise AssertionError('Accepted '+fault)
    # Existing real local committed package from the prior isolation fixture.
    committed=a.tool_checkout.resolve();tool_package=committed/'package'
    env=os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):env.pop(key)
    env.update(GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL=os.devnull)
    revision=subprocess.run(['git','-C',str(committed),'rev-parse','HEAD'],env=env,check=True,
        stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30).stdout.decode().strip()
    launch.verify_package(tool_package,msha,revision,True)
    fake_inputs=out/'explicit_fixture_inputs';fake_inputs.mkdir()
    for name in ('request.json','catalog.json'):shutil.copyfile(inputs/name,fake_inputs/name)
    shutil.copyfile(plan,fake_inputs/'plan.json');shutil.copytree(plan.parent/'checkpoints',fake_inputs/'checkpoints')
    assert launch.strict((fake_inputs/'request.json').read_bytes())['original_request']['test_fixture'] is True
    env.update(GH_TOKEN='NONSECRET-LOCAL-FIXTURE-NOT-A-TOKEN',GITHUB_ACTIONS='true',
        GITHUB_REPOSITORY='qumiha151-wq/lemniscate-stability-lean',GITHUB_SHA='e'*40,GITHUB_EVENT_NAME='push',GITHUB_RUN_ID='1')
    args=[str(tool_package/'launcher/launch.py'),'--package-root',str(tool_package),'--manifest-sha256',msha,
        '--expected-tools-revision',revision,'--execute','--input-checkout',str(fake_inputs),
        '--request','request.json','--request-sha256',launch.digest(fake_inputs/'request.json'),
        '--catalog','catalog.json','--catalog-sha256',launch.digest(fake_inputs/'catalog.json'),
        '--plan','plan.json','--plan-sha256',launch.digest(fake_inputs/'plan.json'),'--output',str(out/'forbidden_execution')]
    trace_path=out/'isolated_cli_trace.json'
    # Real isolated interpreter, actual argv/main entry, with audit events
    # blocking DNS/socket attempts before they could access a network.
    probe='''import sys,runpy,json,pathlib
events=[];network=[]
def audit(event,args):
 if event in ('socket.connect','socket.getaddrinfo','socket.gethostbyname','socket.gethostbyaddr'):
  network.append(event);raise RuntimeError('NETWORK FORBIDDEN BY LOCAL TEST')
sys.addaudithook(audit)
def trace(frame,event,arg):
 module=frame.f_globals.get('__name__','')
 if module in ('production_shard_release_controller','production_release_preflight'):
  if event=='call' and frame.f_code.co_name in ('prepare','execute','validate_request'):
   events.append({'event':'call','module':module,'function':frame.f_code.co_name})
  if event=='exception' and isinstance(arg[1],ValueError):
   events.append({'event':'ValueError','module':module,'function':frame.f_code.co_name,'message':str(arg[1])})
 return trace
sys.argv=ARGS
sys.settrace(trace)
code=0
try:runpy.run_path(sys.argv[0],run_name='__main__')
except SystemExit as error:code=error.code
finally:
 sys.settrace(None)
 pathlib.Path(TRACE).write_text(json.dumps({'exit_code':code,'events':events,'network_attempts':network},indent=2)+'\\n',encoding='utf-8')
raise SystemExit(code)
'''.replace('sys.argv=ARGS','sys.argv='+repr(args)).replace('pathlib.Path(TRACE)','pathlib.Path('+repr(str(trace_path))+')')
    actual=subprocess.run([sys.executable,'-I','-S','-B','-c',probe],env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
    (out/'isolated_cli.stdout').write_bytes(actual.stdout);(out/'isolated_cli.stderr').write_bytes(actual.stderr)
    trace=launch.strict(trace_path.read_bytes())
    assert actual.returncode==1 and trace['exit_code']==1 and trace['network_attempts']==[]
    assert any(x['event']=='call' and x['module']=='production_shard_release_controller' and x['function']=='prepare' for x in trace['events'])
    assert not any(x['event']=='call' and x['function']=='execute' for x in trace['events'])
    assert any(x.get('message')=='Test-only request forbidden in production' for x in trace['events'])
    assert not (out/'forbidden_execution').exists()
    assert all(launch.digest(Path(path))==sha for path,sha in before.items()) and launch.digest(Path(__file__))==test_sha
    report={'schema':'rotating.launcher-evidence-edge-fixtures.v1','status':'checked','launcher_sha256':before[str(Path(launch.__file__))],
        'test_sha256':test_sha,'package_manifest_sha256':msha,'synthetic_success_format_result':result,
        'synthetic_success_is_not_actual_controller_or_HTTP_success':True,'cases':cases,
        'actual_isolated_execute_rejection':{'exit_code':actual.returncode,'trace_sha256':launch.digest(trace_path),
            'controller_prepare_reached':True,'controller_execute_reached':False,'socket_DNS_attempts':0,
            'reason':'Test-only request forbidden in production','publication_output_exists':False},
        'actual_network_requests':0,'actual_remote_mutations':0,'actual_full_preflight_calls':0,'actual_Lean_calls':0,
        'actual_positive_production_execute_tested':False,'production_catalog_generated':False,'deployment_YAML_generated':False}
    launch.write_new(out/'report.json',report);print(json.dumps({'status':'checked','negative_cases':len(cases),
        'isolated_execute_exit':actual.returncode,'report_sha256':launch.digest(out/'report.json')}))


if __name__=='__main__':main()
