"""Fresh concrete assembly compilation after the complete frozen D509 gate.

No production pilot, resume, supplied dependency graph or proof stub is accepted.
The generic internal sequence is exposed only for small explicitly scoped tests.
"""
from pathlib import Path
from types import SimpleNamespace
import argparse,copy,hashlib,importlib,json,os,re,shutil,subprocess,time

VALIDATOR_SHA='d50998d092942c3cb60d24632d446d9e4d4108269bc6bc1a35b3c7fc505cb0e4'
LINUX48_SHA='23e73ccbac0d8d374ff23634eb67967ac41ae3f8bc5594e24e3f53fb3b26d9af'
SCHEMA='rotating.full-assembly-build.v1'


def require(ok,message):
    if not ok:raise ValueError(message)


def digest(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()


def load_validator():
    path=Path(__file__).resolve().parent/'production_full_assembly_plan.py'
    require(digest(path)==VALIDATOR_SHA,'Frozen D509 validator changed')
    v=importlib.import_module('production_full_assembly_plan')
    require(Path(v.__file__).resolve()==path,'Validator imported from another origin')
    return v


def tools_now(v):
    v.load_helpers()
    root=Path(__file__).resolve().parent
    return {str(Path(__file__).resolve()):digest(__file__),str(Path(v.__file__).resolve()):digest(v.__file__),
            **{str((root/n).resolve()):digest(root/n) for n in v.HELPERS}}


def record(v,path):
    v.plain(path);return {'sha256':digest(path),'bytes':Path(path).stat().st_size}


def check_record(v,path,expected):
    require(record(v,path)==expected,'Changed pinned file: '+str(path))


def scan_public_names(v,directory,names):
    v.plain(directory);actual=set()
    for path in directory.rglob('*'):
        v.plain(path)
        if path.is_file():actual.add(path.relative_to(directory).as_posix())
    require(actual=={v.module_path(n) for n in names},'Extra/missing public project artifact or private sidecar')


def stop_owned(child):
    if child.poll() is None:
        child.terminate()
        try:child.wait(timeout=10)
        except subprocess.TimeoutExpired:child.kill();child.wait()
    return child.returncode


def audit_source(name,imports,alias,proposition,proof,prefixes,checks,marker):
    """Only production's fixed call or an explicitly tiny internal fixture uses this."""
    pre='\n'.join('public import '+n for n in imports)
    statements='\n'.join('#check '+n+'\n#print axioms '+n for n in checks)
    guard=' || '.join('('+chr(96)+p+').isPrefixOf userName' for p in prefixes)
    return f'''module
{pre}

@[expose] public section
namespace {name}
noncomputable section
set_option Elab.async false
theorem result : {proposition} := {proof}
end
end {name}

{statements}
#check {alias}
#print axioms {alias}
open Lean Elab Command in
run_cmd do
  let info ← getConstInfo {chr(96)+alias}
  if info.type.isForall then throwError "Final alias has an additional binder"
  unless info.levelParams.isEmpty do throwError "Final alias has universe parameters"
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    let userName := privateToUserName name
    if {guard} then
      for ax in (← collectAxioms name) do
        unless #[{chr(96)}propext, {chr(96)}Classical.choice, {chr(96)}Quot.sound].contains ax do
          throwError "Unexpected axiom: {{name}} depends on {{ax}}"
      count := count + 1
  logInfo m!"{marker} {{count}}"
'''


def production_audit():
    prefix='SolitonClassification.Rotating'
    name=prefix+'.FullAssemblyFreshAudit';alias=name+'.result';main=prefix+'.FullCandidate'
    checks=[prefix+'.'+n for n in [
        'FullGridP.certificate','FullGridM.certificate',
        'FullGridP.state_start','FullGridP.matrix_start','FullGridM.state_start','FullGridM.matrix_start',
        'FullGridPActual.terminal_state','FullGridPActual.terminal_matrix',
        'FullGridMActual.terminal_state','FullGridMActual.terminal_matrix']]
    proposition='''∃ c : SolitonClassification.Rotating.Parameters,
    ∃ X Y : ℝ → ℝ → ℝ,
      SolitonClassification.Rotating.CandidateFinalAssembly.GeometricConclusion c X Y'''
    marker='FULL_ASSEMBLY_ACTUAL_STANDARD3'
    text=audit_source(name,[main],alias,proposition,main+'.exists_closed_rotating_elastic_flow',
        [prefix,'ClosedSimilarity'],checks,marker)
    return dict(name=name,imports=[main],alias=alias,text=text,marker=marker,
                concrete_checks=checks,no_hypothesis_alias=True)


def validated_plan(v,index,execution):
    require(index['schema']=='rotating.assembly-public-index.v1'
            and execution['schema']=='rotating.assembly-execution-plan.v1'
            and execution['status']=='inputs_and_source_graph_validated'
            and execution['public_index_digest']==v.data_sha(index),'Wrong freshly validated execution objects')
    require(execution['new_Lean_elaborations']==0 and execution['full_certificate_proved'] is False,
            'Unexpected input-plan scope')
    rows=[{'name':n,'imports':deps} for n,deps in execution['graph'].items()]
    graph,closures=v.graph_index(rows,'SolitonClassification')
    planned=execution['planned_modules']
    require(len(index['modules'])==11885 and len(planned)==502,'Wrong actual input/source counts')
    require(set(graph)==set(index['modules'])|{r['name'] for r in planned},'Graph has unbound module rows')
    for r in planned:
        require(r['project_closure']==closures[r['name']] and
                r['closure_name_digest']==v.data_sha(closures[r['name']]),'Unbound or changed closure')
    v.validate_order(index['modules'],planned,graph)
    return graph,closures


def compile_sequence(ctx,initial,planned,graph,audit,output,project_prefix,scope,
                     seconds,memory_mb,checkpoint):
    """Actual kernel path shared by production and explicitly scoped tiny tests.

    Caller supplies already validated production data or genuine tiny modules.
    There is no CLI route from a synthetic graph into the production result.
    """
    require(scope in ('full_production','tiny_fixture'),'Unknown sequence scope')
    require(type(seconds) is int and seconds>0 and type(memory_mb) is int and memory_mb>0,'Invalid resource bound')
    v=load_validator();_,runner,_=v.load_helpers();compiler=runner.compiler
    output=v.plain(output,must_exist=False);require(not output.exists(),'Compilation output must be new')
    for path in ctx['roots'].values():
        require(not output.is_relative_to(path.resolve()) and not path.resolve().is_relative_to(output),'Output overlaps base')
    for row in initial.values():
        source=v.plain(row['path'])
        require(not source.is_relative_to(output),'Initial input is in new output')
    names=[r['name'] for r in planned]
    require(audit['name'] not in graph and audit['name'] not in names,'Fresh audit collides with a source')
    require(all(n not in ctx['primary'] for n in [*names,audit['name']]),'New module already exists in base')
    newgraph={**graph,audit['name']:[d for d in audit['imports'] if d.startswith(project_prefix+'.')]}
    _,closures=v.graph_index([dict(name=n,imports=d) for n,d in newgraph.items()],project_prefix)
    v.validate_order(initial,planned,newgraph)
    core_labels={ctx['primary'][n][2] for n in initial if n in ctx['primary']}
    external=[p for label,p in ctx['roots'].items() if label not in core_labels]
    v.validate_external_roots(external,project_prefix)
    require(external,'Empty external library search path')
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(str(p) for p in external);env['LC_ALL']='C'
    output.mkdir(parents=True)
    pool=output/'public_inputs';checked=output/'checked';sources=output/'source'
    setups=output/'setups';logs=output/'logs';temporary=output/'temporary'
    for directory in (pool,checked,sources,setups,logs,temporary):directory.mkdir()
    tools=tools_now(v);public={};produced={};evidence={}
    report=dict(schema=SCHEMA,status='running',scope=scope,modules=[],fresh_audit=None,
        source_header_override_used=False,project_private_inputs=0,
        source_and_setup_closure_checked=True,temporary_artifacts_on_search_path=False,
        promoted_proof_layers=['','.private','.server'],
        tools_sha256=tools,base_lock_sha256=digest(ctx['base_lock']),lean=ctx['identity'],
        full_path_instances_checked=False,full_certificate_proved=False,
        classification_claimed=False,cpu_seconds=None,peak_memory_bytes=None)
    report_path=output/'compile_report.json'
    def save():compiler.atomic_json(report_path,report)
    def recheck_tools():
        require(tools_now(v)==tools,'Compiler/validator/helpers changed during run')
        checkpoint()
    def selected_records(selection):
        return {n:public[n] for n in selection}
    def verify_selected(selection):
        scan_public_names(v,pool,public)
        for n in selection:check_record(v,pool/v.module_path(n),public[n])
    def verify_all():
        recheck_tools();v.validate_public_tree(pool,public);runner.validate_outputs(checked,produced)
        for p,wanted in evidence.items():check_record(v,p,wanted)
        for n,r in initial.items():check_record(v,Path(r['path']),{k:r[k] for k in ('sha256','bytes')})
        for r in planned:require(digest(v.plain(r['source_path']))==r['sha256'],'Original planned source changed')
    try:
        recheck_tools()
        for name,row in initial.items():
            wanted={k:row[k] for k in ('sha256','bytes')}
            source=Path(row['path']);check_record(v,source,wanted)
            destination=pool/v.module_path(name);destination.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(source,destination);check_record(v,destination,wanted);public[name]=wanted
        v.validate_public_tree(pool,public)
        for index,item in enumerate([*planned,audit]):
            fresh=index==len(planned);name=item['name'];relative=Path(*name.split('.')).with_suffix('.lean')
            if fresh:raw=item['text'].encode('utf-8')
            else:
                original=v.plain(item['source_path']);raw=original.read_bytes()
                require(hashlib.sha256(raw).hexdigest()==item['sha256'],'Frozen source changed before copy')
            source=sources/relative;source.parent.mkdir(parents=True,exist_ok=True);source.write_bytes(raw)
            source_rec=record(v,source)
            require(compiler.header_imports(source)==item['imports'],'Copied source header differs')
            for dep in item['imports']:
                require(dep in public if dep.startswith(project_prefix+'.') else dep in ctx['primary'],
                        'Unproved project or unpinned external direct import')
            selection=closures[name]
            require(all(n in public for n in selection),'Missing uncompiled transitive project dependency')
            recheck_tools();verify_selected(selection)
            parse_log=logs/(name.replace('.','_')+'.imports.json')
            parsed=runner.parse_header(ctx['lean'],source,env,runner.expected_header(item['imports']),parse_log)
            setup=v.closure_setup(name,closures,public,pool)
            setup_path=setups/(name.replace('.','_')+'.json');compiler.atomic_json(setup_path,setup)
            v.validate_setup(v.read(setup_path),setup)
            setup_rec=record(v,setup_path);parse_rec=record(v,parse_log)
            log=logs/(name.replace('.','_')+'.log');temp=temporary/(str(index)+'.olean')
            command=[str(ctx['lean']),'--setup',str(setup_path),'-j','1','-M',str(memory_mb),
                     '-o',str(temp),str(relative)]
            before=selected_records(selection);started=time.monotonic();termination='completed';code=None
            with log.open('wb') as stream:
                child=subprocess.Popen(command,cwd=sources,env=env,stdout=stream,stderr=subprocess.STDOUT,
                    creationflags=subprocess.CREATE_NO_WINDOW if os.name=='nt' else 0)
                try:
                    compiler.atomic_json(output/'owned_child.json',dict(pid=child.pid,module=name,command=command,
                        status='running',scope=scope))
                    code=child.wait(timeout=seconds)
                except subprocess.TimeoutExpired:termination='wall_limit';code=stop_owned(child)
                except BaseException:stop_owned(child);raise
            compiler.atomic_json(output/'owned_child.json',dict(pid=child.pid,module=name,
                status='exited',exit_code=code,termination=termination,scope=scope))
            row=dict(name=name,exit_code=code,termination=termination,wall_seconds=time.monotonic()-started,
                command=command,source_sha256=source_rec['sha256'],source_record=source_rec,
                setup=str(setup_path),setup_record=setup_rec,log=str(log),log_record=record(v,log),
                parsed_header=parsed,parsed_header_record=parse_rec,parsed_header_log=str(parse_log),
                project_closure=selection,closure_name_digest=v.data_sha(selection),
                public_input_hashes_before=before,public_input_hashes_after=selected_records(selection))
            text=log.read_text(encoding='utf-8',errors='strict')
            require(code==0 and termination=='completed' and 'error:' not in text and 'warning:' not in text,
                    'Lean did not pass: '+name)
            check_record(v,source,source_rec);check_record(v,setup_path,setup_rec)
            v.validate_setup(v.read(setup_path),setup);verify_selected(selection);recheck_tools()
            require(row['public_input_hashes_before']==row['public_input_hashes_after'],'Input metadata changed')
            artifacts=compiler.bundle(temp)
            require(set(artifacts)==set(compiler.SIDE),'Missing public/private/server checked output')
            target=checked/v.module_path(name);target.parent.mkdir(parents=True,exist_ok=True)
            for suffix,wanted in artifacts.items():
                src=Path(str(temp)+suffix);dest=Path(str(target)+suffix)
                require(not dest.exists(),'New output would overwrite an existing proof artifact')
                src.replace(dest);check_record(v,dest,wanted)
            row['artifacts']=artifacts;produced[name]=row
            evidence.update({source:source_rec,setup_path:setup_rec,log:row['log_record'],parse_log:parse_rec})
            if fresh:
                matches=re.findall(r'^'+re.escape(audit['marker'])+r' ([1-9][0-9]*)$',text,re.MULTILINE)
                require(len(matches)==1,'Missing/duplicate actual fresh axiom-audit count')
                row['actual_declaration_count']=int(matches[0]);row['alias']=audit['alias']
                row['concrete_checked_terms']=audit['concrete_checks'];report['fresh_audit']=row
            else:
                destination=pool/v.module_path(name);destination.parent.mkdir(parents=True,exist_ok=True)
                require(not destination.exists(),'New primary collides with existing public input')
                shutil.copyfile(target,destination);public[name]=artifacts[''];check_record(v,destination,public[name])
                report['modules'].append(row)
            save();print('ACTUAL',scope,name,'EXIT 0',flush=True)
        verify_all();runner.base_final_check(ctx)
        report.update(status='kernel_sequence_checked',actual_source_modules=len(planned),
            fresh_hypothesis_free_alias_checked=True,
            actual_standard3_declaration_count=report['fresh_audit']['actual_declaration_count'],
            complete_input_output_evidence_checked=True,whole_base_after_checked=True)
        save();return report
    except BaseException as error:
        report.update(status='failed',exception_type=type(error).__name__,error=str(error))
        if 'row' in locals() and row.get('name') not in produced:report['failed_module']=row
        save();raise


def production(args):
    v=load_validator();v.load_helpers()
    code=digest(__file__);initial_tools=tools_now(v)
    require(args.final_report_sha256==LINUX48_SHA,'Require the independently reviewed actual Linux48 report')
    output=v.plain(args.output,must_exist=False);require(not output.exists(),'Require new assembly output')
    before_args=SimpleNamespace(**vars(args));before_args.output=output/'validation_before'
    # No assembly child process is possible before this complete production gate.
    result=v.validate(before_args)
    require(result['status']=='inputs_and_source_graph_validated','Full validator did not complete')
    require(digest(__file__)==code and tools_now(v)==initial_tools,'Assembly tools changed during initial validation')
    index_path=before_args.output/'public_input_index.json';plan_path=before_args.output/'execution_plan.json'
    index=v.pinned(index_path,result['public_input_index_sha256'])
    execution=v.pinned(plan_path,result['execution_plan_sha256'])
    graph,_=validated_plan(v,index,execution)
    audit=production_audit();_,runner,_=v.load_helpers()
    ctx=runner.base_context(args.base_args,args.base_lock,v.BASE_SHA)
    report_path=output/'assembly_report.json'
    require(digest(__file__)==code and tools_now(v)==initial_tools,'Assembly tools changed during base check')
    manifest=dict(schema='rotating.assembly-run-manifest.v1',scope='full_production',
        source_revision=v.SOURCE_REVISION,production_plan_sha256=v.PLAN_SHA,
        public_index_sha256=result['public_input_index_sha256'],execution_plan_sha256=result['execution_plan_sha256'],
        ledger_sha256=args.ledger_sha256,merge_receipt_sha256=args.merge_receipt_sha256,
        actual_Linux48_report_sha256=args.final_report_sha256,base_lock_sha256=v.BASE_SHA,
        sources=execution['planned_modules'],fresh_audit={**audit,'source_sha256':hashlib.sha256(audit['text'].encode()).hexdigest()},
        tools_sha256=initial_tools,source_module_count=502,new_Lean_call_count=503,
        classification_claimed=False)
    manifest_path=output/'run_manifest.json';require(not manifest_path.exists(),'Manifest exists')
    v.save(manifest_path,manifest);manifest_sha=digest(manifest_path)
    pinned={index_path:result['public_input_index_sha256'],plan_path:result['execution_plan_sha256'],
            manifest_path:manifest_sha,Path(args.ledger):args.ledger_sha256,
            Path(args.merged)/'merge_receipt.json':args.merge_receipt_sha256,
            Path(args.final_output)/'compile_report.json':args.final_report_sha256}
    def checkpoint():
        require(digest(__file__)==code and tools_now(v)==initial_tools,'Assembly tools changed')
        for path,wanted in pinned.items():require(digest(v.plain(path))==wanted,'Pinned run input changed')
    report=dict(schema=SCHEMA,status='running',scope='full_production',run_manifest_sha256=manifest_sha,
        input_validation_before=result,full_path_instances_checked=False,full_certificate_proved=False,
        classification_claimed=False)
    v.save(report_path,report)
    try:
        checked=compile_sequence(ctx,index['modules'],execution['planned_modules'],graph,audit,
            output/'compiled','SolitonClassification','full_production',args.seconds,args.memory_mb,checkpoint)
        sequence_path=output/'compiled/compile_report.json';sequence_record=record(v,sequence_path)
        require(v.read(sequence_path)==checked,'Actual sequence report differs from its returned evidence')
        after_args=SimpleNamespace(**vars(args));after_args.output=output/'validation_after'
        after=v.validate(after_args)
        require(v.read(after_args.output/'public_input_index.json')==index and
                v.read(after_args.output/'execution_plan.json')==execution,'Input origins/source graph changed during assembly')
        checkpoint()
        require(checked['status']=='kernel_sequence_checked' and len(checked['modules'])==502,
                'Incomplete actual assembly sequence')
        # D509 validates original inputs; repeat the newly produced evidence after
        # that potentially lengthy read-only pass before reporting final success.
        _,runner,_=v.load_helpers()
        produced={r['name']:r for r in [*checked['modules'],checked['fresh_audit']]}
        runner.validate_outputs(output/'compiled/checked',produced)
        for row in produced.values():
            name=row['name']
            check_record(v,output/'compiled/source'/Path(*name.split('.')).with_suffix('.lean'),row['source_record'])
            for key,rec in [('setup','setup_record'),('log','log_record'),('parsed_header_log','parsed_header_record')]:
                check_record(v,Path(row[key]),row[rec])
        pool={n:{k:r[k] for k in ('sha256','bytes')} for n,r in index['modules'].items()}
        pool.update({r['name']:r['artifacts'][''] for r in checked['modules']})
        v.validate_public_tree(output/'compiled/public_inputs',pool)
        runner.base_final_check(ctx);checkpoint();check_record(v,sequence_path,sequence_record)
        report.update(status='concrete_candidate_kernel_checked',input_validation_after=after,
            sequence_report_sha256=sequence_record['sha256'],
            actual_source_modules=502,actual_fresh_audit_count=checked['actual_standard3_declaration_count'],
            final_theorem=audit['alias'],full_path_instances_checked=True,full_certificate_proved=True,
            classification_claimed=False)
        v.save(report_path,report);return report
    except BaseException as error:
        report.update(status='failed',exception_type=type(error).__name__,error=str(error))
        v.save(report_path,report);raise


def positive(value):
    n=int(value)
    if n<=0:raise argparse.ArgumentTypeError('Expected positive integer')
    return n


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('ledger','merged','pipeline-package','core-project','final-package','final-output',
                 'assembly-root','endpoint-root','candidate-source','census','base-lock','base-args','output'):
        p.add_argument('--'+name,type=Path,required=True)
    for name in ('ledger-sha256','merge-receipt-sha256','final-report-sha256','base-lock-sha256'):
        p.add_argument('--'+name,required=True)
    p.add_argument('--seconds',type=positive,default=600);p.add_argument('--memory-mb',type=positive,default=4096)
    result=production(p.parse_args())
    print(json.dumps({k:result[k] for k in ['status','actual_source_modules','actual_fresh_audit_count',
        'full_path_instances_checked','full_certificate_proved','classification_claimed']}),flush=True)


if __name__=='__main__':main()

