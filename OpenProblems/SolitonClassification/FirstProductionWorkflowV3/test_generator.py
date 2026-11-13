"""Synthetic protocol tests only; never write a final workflow or run CI/Lean."""
from pathlib import Path
import argparse, copy, hashlib, json, os, tempfile
import generate_workflow as g


def fixture():
    index = {'schema':'rotating.production-core-pack.v1','status':'checked','revision':g.SOURCE,
        'full_certificate_proved':False,'source_inventory_sha256':g.CORE_INVENTORY,
        'archive_sha256':'a'*64,'base_lock_sha256':'b'*64,'header_sha256':'c'*64,
        'archive_bytes':1234567,'payload_bytes':4567890,'payload_files':123}
    restore = {**index,'schema':'rotating.production-core-restore.v1',
        'stdlib_before_after_checked':True,'complete_restored_base_twice_checked':True}
    imports = {**index,'schema':'rotating.restored-core-import.v1',
        'complete_base_before_after_checked':True,'actual_fresh_private_audit':True,'actual_arctan_import':True,
        'used_lake_or_mathlib_cache':False,'output_on_library_search_path':False,'numerical_leaves_checked':0,
        'modules':[{'name':'SolitonClassification.Rotating.ModuleFullGenericAudit','exit_code':0,
                    'declarations':1704,'private_declarations':331},
                   {'name':'RestoredArctanProbe','exit_code':0}]}
    run = {'id':g.CORE_RUN,'head_sha':g.SOURCE,'status':'completed','conclusion':'success',
        'repository':{'full_name':'example/research'},'run_attempt':1}
    artifact = {'id':123456,'expired':False,'name':f'rotating-core-full-{g.CORE_RUN}-1',
        'workflow_run':{'id':g.CORE_RUN,'head_sha':g.SOURCE},'size_in_bytes':1235000}
    return {'run':run,'artifact':artifact,'index':index,'restore':restore,'imports':imports}


def tests():
    original=fixture();cases=[]
    def reject(name,path,value,tool=g.TOOLS):
        data=copy.deepcopy(original);part=data
        for key in path[:-1]:part=part[key]
        if path:part[path[-1]]=value
        try:g.validate_evidence(data,'example/research',tool)
        except (ValueError,KeyError) as error:
            cases.append({'name':name,'rejected':True,'reason':str(error)})
        else:raise AssertionError('Invalid synthetic evidence accepted: '+name)
    reject('pending_original_run',['run','status'],'in_progress')
    reject('failed_original_run',['run','conclusion'],'failure')
    reject('wrong_original_run',['run','id'],g.CORE_RUN+1)
    reject('source_equals_new_tool_revision',['run','head_sha'],g.TOOLS)
    reject('wrong_repository',['run','repository','full_name'],'injected/research')
    reject('wrong_attempt',['run','run_attempt'],2)
    reject('expired_artifact',['artifact','expired'],True)
    reject('wrong_artifact_name',['artifact','name'],'other')
    reject('wrong_artifact_source',['artifact','workflow_run','head_sha'],g.TOOLS)
    reject('wrong_artifact_run',['artifact','workflow_run','id'],1)
    reject('invalid_artifact_id',['artifact','id'],0)
    reject('nonpositive_observed_size',['index','payload_bytes'],0)
    reject('unchecked_pack',['index','status'],'running')
    reject('changed_archive_identity',['restore','archive_sha256'],'d'*64)
    reject('changed_base_identity',['restore','base_lock_sha256'],'e'*64)
    reject('missing_whole_restore_check',['restore','complete_restored_base_twice_checked'],False)
    reject('failed_restore',['restore','status'],'failed')
    reject('failed_import_report',['imports','status'],'failed')
    reject('missing_Arctan_import',['imports','actual_arctan_import'],False)
    reject('wrong_private_count',['imports','modules',0,'private_declarations'],330)
    reject('actual_Lean_failure',['imports','modules',1,'exit_code'],1)
    reject('fallback_cache_used',['imports','used_lake_or_mathlib_cache'],True)
    reject('injected_output_on_search_path',['imports','output_on_library_search_path'],True)
    reject('wrong_core_inventory',['imports','source_inventory_sha256'],'d'*64)
    reject('tool_revision_reused_as_core',[],None,tool=g.SOURCE)
    try:g.validate_evidence({k:v for k,v in original.items() if k!='restore'},'example/research',g.TOOLS)
    except ValueError as error:cases.append({'name':'missing_actual_restore_evidence','rejected':True,'reason':str(error)})
    else:raise AssertionError('Missing restore evidence accepted')

    pins=g.validate_evidence(original,'example/research',g.TOOLS)
    workflow=g.workflow(pins,'rotating-first-production.yml')
    job=workflow['jobs']['checked'];steps=job['steps']
    assert list(workflow['jobs'])==['checked']
    assert job['strategy']['max-parallel']==4 and job['strategy']['fail-fast'] is False
    assert job['strategy']['matrix']['include']==[
        *({'kind':'shard','key':key,'timeout':120} for key in g.KEYS),
        {'kind':'final48','key':'final48','timeout':90}]
    assert workflow['permissions']=={'contents':'read','actions':'read'}
    assert 'WORK' not in job['env'] and '"$RUNNER_TEMP" >> "$GITHUB_ENV"' in steps[0]['run']
    assert steps[1]['with']['ref']==g.SOURCE and steps[2]['with']['ref']==g.TOOLS
    assert steps[1]['with']['path']=='core-source' and steps[2]['with']['path']=='tool-source'
    for bad in ('${{ runner.temp }}/bad','${{runner.temp}}/bad','${{ runner["temp"] }}'):
        injected=copy.deepcopy(workflow);injected['jobs']['checked']['env']['WORK']=bad
        try:g.validate_contexts(injected)
        except ValueError:cases.append({'name':'invalid_job_env_runner_context:'+bad,'rejected':True})
        else:raise AssertionError('Invalid runner context accepted in job env')
    download=next(s for s in steps if s.get('uses')=='actions/download-artifact@v4')['with']
    assert download['artifact-ids']=='123456' and 'name' not in download
    assert download['run-id']==str(g.CORE_RUN) and download['github-token']=='${{ github.token }}'
    assert download['repository']=='example/research'
    lean=next(s for s in steps if s.get('uses','').startswith('leanprover/lean-action'))['with']
    assert lean['build']==lean['use-mathlib-cache']==lean['use-github-cache']=='false'
    runs=[s for s in steps if 'run' in s]
    installed=next(s for s in runs if 'elan which lean' in s['run'])['run']
    assert '(cd "$CORE_PROJECT" && elan which lean)' in installed
    assert '"$LEAN_BIN" --version' in installed and 'LEAN_BIN=%s' in installed
    assert 'p.is_absolute()' in installed and 'os.access(p,os.X_OK)' in installed
    restore=next(s for s in runs if 'production_core_artifact.py' in s['run'] and ' restore ' in s['run'])['run']
    assert '--lean "$LEAN_BIN"' in restore
    for label,script in (
        ('bare_lean_version','lean --version'),
        ('bare_lean_after_shell_operator','true && lean --version'),
        ('bare_restore_argument','python3 production_core_artifact.py restore --lean lean\n'),
        ('global_stable_default','elan default stable\n')):
        injected=copy.deepcopy(workflow)
        injected['jobs']['checked']['steps'].append({'name':'synthetic unsafe toolchain','run':script})
        try:g.validate_toolchain_usage(injected)
        except ValueError:cases.append({'name':label,'rejected':True})
        else:raise AssertionError('Unsafe toolchain command accepted: '+label)
    injected=copy.deepcopy(workflow)
    for s in injected['jobs']['checked']['steps']:
        if 'elan which lean' in s.get('run',''):
            s['run']=s['run'].replace('(cd "$CORE_PROJECT" && elan which lean)','(elan which lean)')
    try:g.validate_toolchain_usage(injected)
    except ValueError:cases.append({'name':'wrong_toolchain_selection_directory','rejected':True})
    else:raise AssertionError('Selection outside core project accepted')
    numeric=[s for s in runs if 'production_job.py' in s['run']]
    assert len(numeric)==2 and all(s['if']=="matrix.kind == 'shard'" for s in numeric)
    assert ' prepare ' in numeric[0]['run'] and ' compile-pack ' in numeric[1]['run']
    consume=next(s for s in runs if 'production_public_consumer.py' in s['run'])
    assert '--manifest "$WORK/job/generated/manifest.json"' in consume['run']
    assert consume['if']=="matrix.kind == 'shard'"
    final=next(s for s in runs if 'production_compile_final_supplement.py' in s['run'])
    assert final['if']=="matrix.kind == 'final48'" and '--setup-extra' not in final['run']
    upload=next(s for s in steps if s.get('uses')=='actions/upload-artifact@v4')
    assert upload['if']=='always()' and upload['with']['retention-days']==30
    assert 'job/generated' in upload['with']['path'] and 'job/*.tar.xz' in upload['with']['path']
    assert 'public_consumer' in upload['with']['path'] and 'final48' in upload['with']['path']
    for name in ('API_CHECK','DISK_CHECK','RECEIPT_CHECK','DOWNLOAD_CHECK','FINAL_REPORT_CHECK'):
        compile(getattr(g,name),'<embedded '+name+'>','exec')
    installed_python=installed.split("<<'PY'\n",1)[1].split('\nPY\n',1)[0]
    compile(installed_python,'<installed-lean-path-check>','exec')
    text='\n'.join(g.yaml_lines(workflow))+'\n'
    # These are serializer structure assertions, not an independent YAML parser.
    assert '"on":\n' in text and '"max-parallel": 4\n' in text
    assert '"run": |\n' in text and '"timeout-minutes": "${{ matrix.timeout }}"' in text
    assert all(s in text for s in ('"retention-days": 30','"actions": "read"',g.SOURCE,g.TOOLS))
    for bad in ('../../injected.yml','x.yaml','x.yml\nfoo','X.yml'):
        try:g.workflow(pins,bad)
        except ValueError:cases.append({'name':'unsafe_workflow_name:'+repr(bad),'rejected':True})
        else:raise AssertionError('Unsafe name accepted')
    # Execute just the summary guard against synthetic report files. This never
    # invokes a compiler, command, network endpoint or the workflow generator.
    with tempfile.TemporaryDirectory(prefix='workflow-summary-test-') as temp:
        root=Path(temp);(root/'evidence').mkdir();(root/'final48').mkdir()
        good={'status':'checked','supplementary_modules_checked':48,'conditional_geometry_audit_count':2205,
            'full_certificate_proved':False,'base_lock_sha256':pins['core_base_lock_sha256'],
            'supplement_manifest_sha256':pins['final_manifest_sha256'],
            'core_inventory_sha256':pins['core_inventory_sha256'],'full_path_instances_checked':False,
            'fresh_public_only_audit_checked':True,'private_project_input_files':0,'extra_external_setup_modules':[],
            'modules':[{'name':'Synthetic'+str(i),'exit_code':0,'termination':'completed'} for i in range(48)],
            'fresh_audit':{'name':'SolitonClassification.Rotating.FinalSupplementFreshAudit',
                           'exit_code':0,'termination':'completed'}}
        env_before=dict(os.environ)
        try:
            os.environ.update(WORK=str(root),PINS=json.dumps(pins),KIND='final48',KEY='final48')
            def check_report(report):
                (root/'final48/compile_report.json').write_text(json.dumps(report))
                exec(compile(g.FINAL_REPORT_CHECK,'<synthetic-summary>','exec'),{})
            check_report(good)
            for label,path,value in (
                ('wrong_final_base',['base_lock_sha256'],'d'*64),
                ('wrong_final_manifest',['supplement_manifest_sha256'],'d'*64),
                ('false_full_path_claim',['full_path_instances_checked'],True),
                ('nonzero_final_module',['modules',7,'exit_code'],1),
                ('timed_out_final_module',['modules',7,'termination'],'timeout'),
                ('failed_fresh_audit',['fresh_audit','exit_code'],1),
                ('wrong_fresh_audit',['fresh_audit','name'],'Other'),
                ('private_project_input',['private_project_input_files'],1),
                ('unapproved_Arctan_override',['extra_external_setup_modules'],['Mathlib.Override'])):
                bad=copy.deepcopy(good);target=bad
                for key in path[:-1]:target=target[key]
                target[path[-1]]=value
                try:check_report(bad)
                except AssertionError:cases.append({'name':label,'rejected':True})
                else:raise AssertionError('Bad final report accepted: '+label)
        finally:
            os.environ.clear();os.environ.update(env_before)
    return {'schema':'rotating.first-production-workflow-tests.v1','status':'passed',
        'synthetic_fixtures_only':True,'rejections':cases,'matrix_entries':5,'max_parallel':4,
        'embedded_Python_compiled':6,'synthetic_summary_execution_checked':True,'independent_YAML_parser_used':False,
        'in_memory_synthetic_render_sha256':hashlib.sha256(text.encode()).hexdigest(),
        'final_workflow_file_written':False,'actual_core_PASS_inferred':False,
        'Lean_calls':0,'numeric_generation_calls':0,'network_calls':0,'workflow_installed':False,
        'workflow_executed':False,'full_certificate_proved':False}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--report',type=Path,required=True)
    args=p.parse_args();assert not args.report.exists()
    report=tests()
    report['generator_sha256']=g.sha(Path(g.__file__))
    report['test_source_sha256']=g.sha(Path(__file__))
    args.report.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'status':report['status'],'rejections':len(report['rejections']),
                      'final_workflow_file_written':False,'Lean_calls':0}),flush=True)


if __name__=='__main__':main()
