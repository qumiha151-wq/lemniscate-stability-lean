"""Actual isolated Python/local Git tests; zero live publication or requests."""
from pathlib import Path
import argparse,copy,importlib.util,json,os,shutil,subprocess,sys
import shard_release_v3_launch as launch
import production_shard_release_controller as controller


def main():
    ap=argparse.ArgumentParser()
    for name in ('package','output','formal-root'):ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();out=a.output.resolve();launch.require(not out.exists(),'Fresh review output required');out.mkdir(parents=True)
    test_sha=launch.digest(Path(__file__));source_sha=launch.digest(Path(launch.__file__))
    root=out/'local_git';root.mkdir();package=root/'package';shutil.copytree(a.package,package)
    msha=launch.digest(package/'package_manifest.json');original_manifest=(package/'package_manifest.json').read_bytes()
    verified=launch.verify_package(package,msha);env=os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):env.pop(key)
    env.update(GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL=os.devnull)
    hooks=out/'empty_hooks';hooks.mkdir()
    def git(*args):return subprocess.run(['git','-C',str(root),*args],env=env,check=True,
        stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30).stdout.decode().strip()
    git('init','-q');git('add','--','package')
    git('-c','core.hooksPath='+str(hooks),'-c','commit.gpgsign=false','-c','user.name=Local fixture',
        '-c','user.email=fixture@example.invalid','commit','-q','-m','Local-only v3 launcher package fixture')
    revision=git('rev-parse','HEAD');calls=[];rejects=[]
    base=[sys.executable,'-I','-S','-B',str(package/'launcher/launch.py'),'--package-root',str(package),
        '--manifest-sha256',msha,'--expected-tools-revision',revision,'--verify-package-only']
    def run(name,args=None,runenv=None,expected=0):
        result=subprocess.run(args or base,env=runenv or env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
        (out/(name+'.stdout')).write_bytes(result.stdout);(out/(name+'.stderr')).write_bytes(result.stderr)
        record={'case':name,'argv':args or base,'exit_code':result.returncode,'stdout_sha256':launch.digest(out/(name+'.stdout')),
            'stderr_sha256':launch.digest(out/(name+'.stderr'))};calls.append(record)
        assert result.returncode==expected,(name,result.returncode,result.stderr.decode(errors='replace'))
        return result
    result=run('clean_isolated');data=json.loads(result.stdout)
    assert data['status']=='package_and_isolated_import_checked' and data['runtime_helpers']==18 and data['tool_revision']==revision
    # Actual isolated interpreter ignores a malicious PYTHONPATH fallback.
    poison=out/'poison';poison.mkdir();(poison/'production_shard_release_controller.py').write_text("raise RuntimeError('POISON EXECUTED')")
    poisoned=env.copy();poisoned['PYTHONPATH']=str(poison);run('ignored_PYTHONPATH',runenv=poisoned)
    wrong=list(base);wrong[wrong.index('--expected-tools-revision')+1]='0'*40;run('wrong_P',wrong,expected=1)
    wrong=list(base);wrong[wrong.index('--manifest-sha256')+1]='0'*64;run('wrong_manifest_sha',wrong,expected=1)
    for name,relative in [('dirty_launcher','launcher/launch.py'),('dirty_helper','runtime/production_bulk_origin.py'),
        ('dirty_manifest','package_manifest.json')]:
        path=package/relative;raw=path.read_bytes();path.write_bytes(raw+b'\n ')
        try:run(name,expected=1)
        finally:path.write_bytes(raw)
    for name,relative in [('extra_helper','runtime/unexpected.py'),('nested_helper','runtime/nested/unexpected.py')]:
        path=package/relative;path.parent.mkdir(parents=True,exist_ok=True);path.write_text('# forbidden extra')
        try:run(name,expected=1)
        finally:
            if name=='nested_helper':path.parent.rename(root/'rejected_nested')
            else:path.rename(root/'rejected_extra.py')
    # Coherently updated local manifest does not override the committed P.
    path=package/'launcher/launch.py';raw=path.read_bytes();path.write_bytes(raw+b'\n# coherent local edit\n')
    changed=json.loads(original_manifest)
    row=next(x for x in changed['files'] if x['path']=='launcher/launch.py');row.update(bytes=path.stat().st_size,sha256=launch.digest(path))
    (package/'package_manifest.json').write_text(json.dumps(changed,sort_keys=True,indent=2)+'\n',encoding='utf-8')
    wrong=list(base);wrong[wrong.index('--manifest-sha256')+1]=launch.digest(package/'package_manifest.json')
    try:run('coherent_uncommitted_edit',wrong,expected=1)
    finally:path.write_bytes(raw);(package/'package_manifest.json').write_bytes(original_manifest)
    flags=[x for x in base if x!='-I'];run('missing_isolation',flags,expected=1)
    flags=[x for x in base if x!='-S'];run('site_enabled',flags,expected=1)
    probe="import sys,runpy;sys.path.insert(0,"+repr(str(poison))+");sys.argv="+repr(base[4:])+";runpy.run_path(sys.argv[0],run_name='__main__')"
    run('actual_contaminated_path',[sys.executable,'-I','-S','-B','-c',probe],expected=1)
    # Structural verifier rejects known malformed inputs with ValueError only.
    def reject(name,fn):
        try:fn()
        except ValueError as error:rejects.append({'case':name,'error':str(error),'rejected':True})
        else:raise AssertionError('Accepted '+name)
    for name in ('../escape','/absolute','x\\y','x:y','a//b'):
        reject('path_'+name,lambda n=name:launch.safe_relative(n))
    # Actual symlink if the local Windows account allows creation; no fake pass.
    target=package/'README.txt';raw=target.read_bytes();backup=root/'readme_original';target.rename(backup);link_status=None
    try:
        try:target.symlink_to(backup)
        except OSError as error:link_status={'actual_link_created':False,'not_exercised_error_type':type(error).__name__};backup.rename(target)
        else:
            try:run('actual_symlink',expected=1);link_status={'actual_link_created':True,'rejected':True}
            finally:target.unlink();backup.rename(target)
    finally:assert target.read_bytes()==raw
    run('clean_final')
    # Byte-only failure evidence from already completed explicit stub fixture.
    formal=a.formal_root.resolve();failure=formal/'controller_orchestration_review_v2/after_intent'
    inputs=formal/'controller_orchestration_review_v2/after_intent_inputs';plan=formal/'production_pipeline_package_v1/plan/plan.json'
    envelope=launch.strict((inputs/'request.json').read_bytes());q=envelope['original_request']
    pins={inputs/'request.json':launch.digest(inputs/'request.json'),inputs/'catalog.json':launch.digest(inputs/'catalog.json'),plan:launch.digest(plan)}
    for job in launch.strict(plan.read_bytes())['jobs']:pins[plan.parent/job['output_node']]=job['output_node_sha256']
    ctx={'output':failure,'input_checkout':formal,'pins':pins,'request':q}
    evidence=launch.evidence(controller,ctx,launch.verify_package(package,msha),out/'failure_compact',False)
    assert evidence['originals_copied']==0
    recovery=launch.strict((out/'failure_compact/recovery_original_paths.json').read_bytes())
    assert len(recovery['files'])==1 and recovery['files'][0]['matches_pinned_raw_archive'] and not recovery['files'][0]['source_copy_performed']
    assert not list((out/'failure_compact').rglob('*.tar.xz')) and not list((out/'failure_compact').rglob('*.zip'))
    bad=dict(ctx);bad['output']=formal/'controller_orchestration_review_v2/success'
    reject('stub_receipt_not_real_success',lambda:launch.evidence(controller,bad,launch.verify_package(package,msha),out/'bad_success',True))
    assert launch.digest(Path(launch.__file__))==source_sha and launch.digest(Path(__file__))==test_sha
    final=launch.verify_package(package,msha,revision,True)
    report={'schema':'rotating.v3-launcher-local-review.v1','status':'checked','launcher_sha256':source_sha,
        'test_sha256':test_sha,'package_manifest_sha256':msha,'actual_local_tool_commit':revision,'actual_subprocesses':calls,
        'structural_rejections':rejects,'actual_symlink_test':link_status,'failure_evidence':evidence,
        'runtime_helpers':len(final['manifest']['runtime_helper_sha256']),'actual_network_requests':0,
        'actual_remote_mutations':0,'actual_full_preflight_calls':0,'actual_Lean_calls':0,
        'production_catalog_generated':False,'deployment_YAML_generated':False,
        'actual_positive_production_execute_tested':False,'retained_old_failure_evidence_is_stub_orchestration':True}
    launch.write_new(out/'report.json',report);print(json.dumps({'status':'checked','subprocesses':len(calls),
        'structural_rejections':len(rejects),'report_sha256':launch.digest(out/'report.json')}))


if __name__=='__main__':main()
