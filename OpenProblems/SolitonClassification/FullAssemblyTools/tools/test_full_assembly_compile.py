"""Real tiny modules through the new compiler path; never production full250."""
from pathlib import Path
import argparse,copy,json,os
import production_full_assembly_compile as build


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();v=build.load_validator();_,runner,_=v.load_helpers();compiler=runner.compiler
    root=v.plain(a.output,must_exist=False);v.require(not root.exists(),'New fixture output required');root.mkdir(parents=True)
    old=Path(__file__).resolve().parent.parent/'assembly_plan_fixture_v2'
    old_report=v.pinned(old/'report.json','5f46f37581aac06e69de04d6f7943fd4d37ef6648583df8b3ddc171b72d89cc7')
    std=v.read(old/'stdlib_lock.json')
    lean,identity=compiler.lean_identity(a.lean)
    import subprocess
    lib=Path(subprocess.check_output([str(lean),'--print-libdir'],text=True).strip()).resolve()
    assert std['lean']==identity
    lock=root/'base_lock.json';args=root/'base_args.json'
    v.save(lock,dict(schema='rotating.production-base.v1',lean=identity,root_order=['stdlib'],files=std['files']))
    v.save(args,['--lean',str(lean),'--base-root','stdlib='+str(lib)])
    my_hash=build.digest(__file__);tool_hash=build.digest(build.__file__)
    ctx=runner.base_context(args,lock,build.digest(lock))
    planned=[];graph={}
    for rec in old_report['actual_tiny_lean_modules']:
        name=rec['name'];source=old/'source'/(v.module_path(name)[:-6]+'.lean')
        assert build.record(v,source)==rec['source']
        imports=compiler.header_imports(source)
        planned.append(dict(name=name,source_path=str(source),sha256=rec['source']['sha256'],imports=imports))
        graph[name]=[x for x in imports if x.startswith('ClosureFixture.')]
    assert len(planned)==4
    name='ClosureFixture.FreshCompileAudit';alias=name+'.result';marker='TINY_SEQUENCE_ACTUAL_STANDARD3'
    text=build.audit_source(name,['ClosureFixture.D'],alias,'ClosureFixture.c = 9','ClosureFixture.result',
        ['ClosureFixture'],['ClosureFixture.a_eq','ClosureFixture.b_eq','ClosureFixture.c_eq','ClosureFixture.result'],marker)
    audit=dict(name=name,alias=alias,imports=['ClosureFixture.D'],text=text,marker=marker,
        concrete_checks=['ClosureFixture.a_eq','ClosureFixture.b_eq','ClosureFixture.c_eq','ClosureFixture.result'])
    checks=[]
    def checkpoint():
        assert build.digest(__file__)==my_hash and build.digest(build.__file__)==tool_hash
    checked=build.compile_sequence(ctx,{},planned,graph,audit,root/'positive','ClosureFixture',
        'tiny_fixture',60,2048,checkpoint)
    assert checked['status']=='kernel_sequence_checked' and len(checked['modules'])==4
    assert [len(r['project_closure']) for r in checked['modules']]==[0,1,2,3]
    assert len(checked['fresh_audit']['project_closure'])==4
    assert checked['fresh_hypothesis_free_alias_checked'] is True and checked['full_certificate_proved'] is False
    def rejected(label,fn):
        try:fn()
        except (ValueError,RuntimeError) as e:checks.append(dict(name=label,rejected=True,reason=str(e)))
        else:raise AssertionError('Accepted '+label)
    wrong=copy.deepcopy(planned);wrong[0]['sha256']='0'*64
    rejected('changed_actual_source',lambda:build.compile_sequence(ctx,{},wrong,graph,audit,
        root/'wrong_source','ClosureFixture','tiny_fixture',60,2048,checkpoint))
    assert not (root/'wrong_source/logs/ClosureFixture_A.log').exists()
    wrong=copy.deepcopy(planned);wrong[0]['imports']=['Lean']
    rejected('source_manifest_header_mismatch',lambda:build.compile_sequence(ctx,{},wrong,graph,audit,
        root/'wrong_header','ClosureFixture','tiny_fixture',60,2048,checkpoint))
    assert not (root/'wrong_header/logs/ClosureFixture_A.log').exists()
    # Actual Lean negative: alias is genuinely universally quantified, so the
    # same final type-checking metaprogram must fail even though its proof exists.
    initial={r['name']:dict(path=str(root/'positive/checked'/v.module_path(r['name'])),**r['artifacts'][''])
        for r in checked['modules']}
    badname='ClosureFixture.BadBinderAudit';badalias=badname+'.result'
    badtext=build.audit_source(badname,['ClosureFixture.D'],badalias,'(n : Nat) → n = n',
        'fun _ => rfl',['ClosureFixture'],[],'BAD_BINDER_MUST_NOT_PASS')
    badaudit=dict(name=badname,alias=badalias,imports=['ClosureFixture.D'],text=badtext,
        marker='BAD_BINDER_MUST_NOT_PASS',concrete_checks=[])
    rejected('actual_forall_alias',lambda:build.compile_sequence(ctx,initial,[],graph,badaudit,
        root/'bad_binder','ClosureFixture','tiny_fixture',60,2048,checkpoint))
    badreport=v.read(root/'bad_binder/compile_report.json')
    assert badreport['status']=='failed' and badreport['failed_module']['exit_code']==1
    badlog=root/'bad_binder/logs/ClosureFixture_BadBinderAudit.log'
    assert 'Final alias has an additional binder' in badlog.read_text(encoding='utf-8')
    # Public inventory and setup probes use the actual successfully compiled pool.
    pool=root/'positive/public_inputs';names=set(initial)
    names.update(r['name'] for r in checked['modules'])
    sidecar=pool/'ClosureFixture/A.olean.private';sidecar.write_bytes(b'synthetic forbidden sidecar')
    rejected('private_sidecar_in_public_pool',lambda:build.scan_public_names(v,pool,names))
    sidecar.unlink()
    setup=v.read(root/'positive/setups/ClosureFixture_D.json');bad=copy.deepcopy(setup)
    del bad['importArts']['ClosureFixture.A']
    rejected('incomplete_recursive_setup',lambda:v.validate_setup(bad,setup))
    bad=copy.deepcopy(setup);bad['imports']=[]
    rejected('source_import_override',lambda:v.validate_setup(bad,setup))
    prod=build.production_audit()
    assert len(prod['concrete_checks'])==10 and len(set(prod['concrete_checks']))==10
    assert all('#check '+n in prod['text'] and '#print axioms '+n in prod['text'] for n in prod['concrete_checks'])
    assert 'theorem result : ∃ c' in prod['text'] and 'FullCandidate.exists_closed_rotating_elastic_flow' in prod['text']
    assert 'if info.type.isForall' in prod['text'] and 'unless count ==' not in prod['text']
    checkpoint();runner.base_final_check(ctx)
    result=dict(schema='rotating.full-assembly-compiler-tiny-test.v1',status='passed',
        compiler_sha256=tool_hash,fixture_sha256=my_hash,validator_sha256=build.VALIDATOR_SHA,
        original_actual_tiny_report_sha256=build.digest(old/'report.json'),
        positive_sequence_report_sha256=build.digest(root/'positive/compile_report.json'),
        actual_successful_Lean_calls=5,actual_expected_failing_Lean_calls=1,
        actual_fresh_audit_count=checked['actual_standard3_declaration_count'],
        recursive_project_map_counts=[0,1,2,3,4],rejections=checks,
        standard_library_before_after_checked=True,actual_full250_validation=False,
        actual_fullgrid_Lean_calls=0,full_certificate_proved=False,
        production_audit_text_checked_as_text_only=True,production_audit_text_sha256=
        __import__('hashlib').sha256(prod['text'].encode()).hexdigest())
    v.save(root/'report.json',result);print(json.dumps(result),flush=True)


if __name__=='__main__':main()

