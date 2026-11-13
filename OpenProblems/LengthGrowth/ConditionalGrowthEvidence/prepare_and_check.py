"""Local four-leaf LengthGrowth integration; reuse all frozen leaf artifacts.
Only the entry point and unchanged recursive axiom audit are compiled.
No output synchronization, network call, GitHub write or other-project edit.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,time
sys.stdout.reconfigure(encoding='utf-8')
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=HERE/'stage_v1';PROJECT=OUT/'project';BUILD=OUT/'build'
OLD=ROOT/'outputs/open-problems/LengthGrowth'
PRIOR=ROOT/'work/arclength_publication/stage_v1'
FLOW=ROOT/'work/length_flow_formal'
BASE='527358449e05089b9d67e3527169b3c8da517332'
MATH=Path('C:/Users/17815/Desktop/论文/lean_deps/mathlib4-4.33.1')
LEAN=Path('C:/Users/17815/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean.exe')

def digest(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
def info(path):return dict(sha256=digest(path),bytes=Path(path).stat().st_size)
def save(path,value):Path(path).write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
def snapshot(folder):return {p.relative_to(folder).as_posix():info(p) for p in sorted(folder.rglob('*')) if p.is_file()}
def imports(path):return re.findall(r'^(?:public )?import\s+([A-Za-z0-9_.]+)\s*$',Path(path).read_text(encoding='utf-8-sig'),re.M)

def main():
    assert not OUT.exists(),'Fresh stage required'
    config_path=HERE/'InputPins.json';config=json.loads(config_path.read_text())
    assert config['base_commit']==BASE
    assert set(config['new_modules'])=={'LengthGrowth.EnergyDecay','LengthGrowth.WeightedLengthComparison',
        'LengthGrowth.ActualFlow.ConditionalQuarterGrowth','LengthGrowth.ActualFlow.ProductWindow'}
    assert digest(PRIOR/'entries_manifest.json')=='ccae7bcbde081da5ee9ca0dcf7d77a954753c49aa9991613a2c1f390b2b023cf'
    prior_entries=json.loads((PRIOR/'entries_manifest.json').read_text())
    baseline=snapshot(OLD)
    assert baseline==prior_entries['project_inventory'],'Published project differs from pinned prior stage'
    previous=json.loads((PRIOR/'project/ArclengthEvidence/Integration.json').read_text())
    assert digest(PRIOR/'project/ArclengthEvidence/Integration.json')=='18ce36b1cbe9cc9f39ae0c0a97e6de6f0ba9351b5b14587f4181efcce0aeb47f'
    assert previous['status']=='PASS' and previous['actual_recursive_audit_count']==679
    previous_rows=json.loads((PRIOR/'project/ArclengthEvidence/Modules.json').read_text())['leaves']
    assert len(previous_rows)==40
    other_before={p.name:snapshot(p) for p in (ROOT/'outputs/open-problems').iterdir() if p.is_dir() and p!=OLD}
    selected={str(p):info(p) for p in [Path(__file__).resolve(),config_path,LEAN,
        PRIOR/'entries_manifest.json',PRIOR/'project/ArclengthEvidence/Integration.json',
        PRIOR/'project/ArclengthEvidence/Modules.json']}
    leaves=[]
    for row in previous_rows:
        module=row['module'];relative=Path(*module.split('.'))
        src=OLD/relative.with_suffix('.lean');obj=PRIOR/'build'/relative.with_suffix('.olean')
        assert info(src)==row['source_info'] and info(obj)==row['artifact_info'],module
        selected[str(src)]=info(src);selected[str(obj)]=info(obj)
        leaves.append(dict(module=module,source=str(src),source_info=info(src),artifact=str(obj),
            artifact_info=info(obj),new=False,imports=imports(src)))
    for module,pin in config['new_modules'].items():
        src=FLOW/Path(*module.split('.')).with_suffix('.lean')
        author=FLOW/pin['build_directory'];obj=author/(module.rsplit('.',1)[1]+'.olean')
        result=json.loads((author/'result.json').read_text())
        assert digest(src)==pin['source_sha256']==result['source_sha256']
        assert digest(obj)==pin['artifact_sha256']
        assert result['exit_code']==0 and result['source_unchanged'] and result['dependency_outputs_unchanged']
        assert result.get('dependency_sources_unchanged',True)
        assert digest(author/'setup.json')==result['setup_sha256']
        stdout=(author/'stdout.txt').read_bytes();stderr=(author/'stderr.txt').read_bytes()
        assert stdout.strip() and not stderr and not re.search(rb'\b(?:warning|error|sorryAx)\b',stdout)
        for key in ['dependency_pins','dependency_artifact_pins','dependency_source_pins']:
            for path,sha in result.get(key,{}).items():
                assert digest(path)==sha,path
                selected[path]=info(path)
        for p in [src,obj,*[p for p in author.iterdir() if p.suffix=='.json' or p.name in ['stdout.txt','stderr.txt']]]:
            selected[str(p)]=info(p)
        leaves.append(dict(module=module,source=str(src),source_info=info(src),artifact=str(obj),
            artifact_info=info(obj),new=True,imports=imports(src),author_evidence=str(author),
            author_result_sha256=digest(author/'result.json')))
    for name,sha in config['reviews'].items():
        p=FLOW/name;assert digest(p)==sha,name;selected[str(p)]=info(p)
    for name,sha in config['author_freezes'].items():
        p=FLOW/name;assert digest(p)==sha,name;selected[str(p)]=info(p)
    scope=HERE/'ProductWindowAndConditionalGrowthScope.txt';selected[str(scope)]=info(scope)
    modules={row['module']:row for row in leaves};assert len(modules)==44
    order=[]
    while len(order)<44:
        available=[m for m in sorted(modules) if m not in order and all(dep in order
            for dep in modules[m]['imports'] if dep.startswith('LengthGrowth.'))]
        assert available,'Missing dependency or import cycle'
        order.extend(available)
    OUT.mkdir(parents=True);shutil.copytree(OLD,PROJECT)
    evidence=PROJECT/'ConditionalGrowthEvidence';evidence.mkdir()
    arts={}
    for module in order:
        row=modules[module];relative=Path(*module.split('.'))
        obj=BUILD/relative.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(row['artifact'],obj);arts[module]=[[str(obj)],[]]
        if row['new']:
            shutil.copyfile(row['source'],PROJECT/relative.with_suffix('.lean'))
            dest=evidence/module.rsplit('.',1)[1];dest.mkdir()
            for p in Path(row['author_evidence']).iterdir():
                if p.suffix=='.json' or p.name in ['stdout.txt','stderr.txt']:shutil.copyfile(p,dest/p.name)
    math_report=FLOW/'symmetric_dependency/build_v1/report.json'
    assert digest(math_report)=='7ec7dae9256c3ca68d0519a323938eaeb5d1c5783565be5972f1fdb9ea39e7f4'
    for module,layers in json.loads(math_report.read_text())['importArts'].items():
        arts[module]=layers
        for group in layers:
            for path in group:selected[path]=info(path)
    selected[str(math_report)]=info(math_report);assert len(arts)==46
    root=PROJECT/'LengthGrowth.lean'
    root.write_text('import LengthGrowth.ActualFlow.ProductWindow\nimport LengthGrowth.ActualFlow.ConditionalQuarterGrowth\n'+
        root.read_text(encoding='utf-8')+'''\n/-!
ProductWindow proves a physical-time dissipation estimate for actual forward
normal FEF using only endpoint gain of e=EL and the actual budget U=int E^4.
For Z=int D/E and U<e(t)^2 it proves (e(t)^2-U)Z<=2U.

ConditionalQuarterGrowth separately assumes a UNIFORM bound A(t)<=A0 for
the actual total absolute curvature. It derives explicit energy decay and
L(t)+sqrt(t)E(t)<=L(0)+64 A0 sqrt(A0) fourthRoot(t).
No uniform A bound is proved. Unrestricted quarter-power growth remains open.
See ProductWindowAndConditionalGrowthScope.txt for precise scope.
-/\n''',encoding='utf-8')
    status=PROJECT/'STATUS.txt'
    status.write_text(status.read_text(encoding='utf-8')+'''\nPRODUCT WINDOW AND CONDITIONAL QUARTER-POWER ADDITION
Four new modules prove an actual physical-time window estimate and a
SEPARATELY CONDITIONAL fourth-root length bound. For e=EL, U=int_s^t E^4,
Z=int_s^t D/E, endpoint gain e(s)<=e(t) and U<e(t)^2 imply
(e(t)^2-U)Z<=2U. No first-record maximum or energy-clock inverse is assumed.

The quarter-power result REQUIRES the additional global hypothesis
actual total absolute curvature A(t)<=A0 for every t>=0. This hypothesis is
NOT proved here. Under it, actual geometric coercivity and normal FEF imply
E(t)<=[E(0)^(-4)+t/(65536 A0^6)]^(-1/4), and
L(t)+sqrt(t)E(t)<=L(0)+64 A0 sqrt(A0) fourthRoot(t).
The scalar helper premises are discharged by the genuine position-flow
adapter. No monotone-length assumption or limiting-energy-zero premise is
used. Initial time is included by continuity, without backward FEF.

The unrestricted quarter-power question remains unresolved. There is no
new arbitrary-data existence, ancient-limit, uniform A or uniform EL theorem.
The project now contains 44 mathematical leaves, its entry point, and the
unchanged recursive audit. See ProductWindowAndConditionalGrowthScope.txt
and ConditionalGrowthEvidence for the exact assumptions and validation.
''',encoding='utf-8')
    shutil.copyfile(scope,PROJECT/scope.name)
    for name in config['reviews']:shutil.copyfile(FLOW/name,evidence/name)
    for name in config['author_freezes']:shutil.copyfile(FLOW/name,evidence/name)
    save(evidence/'Modules.json',dict(schema='conditional-product-four-leaves-v1',leaves=leaves,
        topological_order=order,new_leaf_count=4,prior_leaf_count=40,
        author_leaf_recompilations_in_this_integration=0,base_commit_reported_by_root=BASE))
    closure=set()
    def visit(m):
        if m in closure:return
        assert m in modules,m
        closure.add(m)
        for dep in modules[m]['imports']:
            if dep.startswith('LengthGrowth.'):visit(dep)
    for m in imports(root):
        if m.startswith('LengthGrowth.'):visit(m)
    assert closure==set(modules)
    assert digest(PROJECT/'LengthGrowth/AxiomAudit.lean')==digest(OLD/'LengthGrowth/AxiomAudit.lean')
    staged=snapshot(PROJECT);build_before=snapshot(BUILD)
    save(OUT/'baseline_project.json',baseline);save(OUT/'other_projects_before.json',other_before)
    save(OUT/'selected_inputs_before.json',selected);save(OUT/'staged_sources_before.json',staged)
    deps=[MATH/'.lake/build/lib/lean']+sorted(p/'.lake/build/lib/lean' for p in
        (MATH/'.lake/packages').iterdir() if (p/'.lake/build/lib/lean').is_dir())
    env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,deps)));checks=[]
    for module,src in [('LengthGrowth',root),('LengthGrowth.AxiomAudit',PROJECT/'LengthGrowth/AxiomAudit.lean')]:
        setup=dict(name=module,isModule=False,package=None,plugins=[],dynlibs=[],options={},importArts=dict(arts))
        setup_path=OUT/(module+'.setup.json');save(setup_path,setup)
        target=BUILD/Path(*module.split('.')).with_suffix('.olean')
        argv=[str(LEAN),'--setup',str(setup_path),'-M','4096','-j','1','-o',str(target),str(src)]
        print('Compiling '+module,flush=True);start=time.monotonic()
        run=subprocess.run(argv,cwd=PROJECT,env=env,capture_output=True,timeout=300)
        stdout=evidence/(module+'.stdout.txt');stderr=evidence/(module+'.stderr.txt')
        stdout.write_bytes(run.stdout);stderr.write_bytes(run.stderr)
        row=dict(module=module,argv=argv,exit_code=run.returncode,seconds=time.monotonic()-start,
            source=info(src),setup=info(setup_path),stdout=info(stdout),stderr=info(stderr))
        checks.append(row);save(OUT/'progress.json',checks)
        print(run.stdout.decode('utf-8',errors='replace'),end='',flush=True)
        print(run.stderr.decode('utf-8',errors='replace'),end='',flush=True)
        assert run.returncode==0 and not re.search(rb'\b(?:warning|error|sorryAx)\b',run.stdout+run.stderr)
        row['output']=info(target);arts[module]=[[str(target)],[]]
        shutil.copyfile(setup_path,evidence/setup_path.name)
    count=int(re.search(r'Length-growth audit passed: (\d+) declarations; standard axioms only',
        (evidence/'LengthGrowth.AxiomAudit.stdout.txt').read_text()).group(1))
    assert count>679
    assert snapshot(OLD)==baseline
    assert {p.name:snapshot(p) for p in (ROOT/'outputs/open-problems').iterdir() if p.is_dir() and p!=OLD}==other_before
    assert all(info(p)==data for p,data in selected.items())
    assert all(info(PROJECT/p)==data for p,data in staged.items())
    assert all(info(BUILD/p)==data for p,data in build_before.items())
    verification=dict(schema='conditional-product-project-integration-v1',status='PASS',
        base_commit_reported_by_root=BASE,actual_integration_calls=checks,
        prior_mathematical_leaves=40,new_mathematical_leaves=4,reused_mathematical_leaves=44,
        leaf_recompilations=0,original_audit_source_unchanged=True,prior_evidence_unchanged=True,
        actual_recursive_audit_count=count,allowed_axioms=['propext','Classical.choice','Quot.sound'],
        selected_inputs_unchanged=True,base_outputs_unchanged=True,other_projects_unchanged=True,
        staged_sources_unchanged=True,reused_artifacts_unchanged=True,explicit_root_importArts=46,
        no_project_LEAN_PATH=True,ordinary_mathlib_roots=list(map(str,deps)),
        whole_mathlib_cache_snapshot_performed=False,old_evidence_rewritten=False,
        actual_physical_product_window_proved=True,quarter_growth_requires_uniform_absolute_curvature_cap=True,
        uniform_absolute_curvature_bound_proved=False,general_quarter_power_growth_proved=False,
        energy_clock_formalized=False,ancient_window_formalized=False,
        runner_sha256=digest(__file__),selected_inputs_sha256=digest(OUT/'selected_inputs_before.json'),
        staged_before_sha256=digest(OUT/'staged_sources_before.json'))
    save(evidence/'Integration.json',verification)
    shutil.copyfile(OUT/'selected_inputs_before.json',evidence/'SelectedInputs.json')
    shutil.copyfile(__file__,evidence/'prepare_and_check.py');shutil.copyfile(config_path,evidence/config_path.name)
    final=snapshot(PROJECT)
    changed_old={p for p,data in baseline.items() if final.get(p)!=data}
    assert changed_old=={'LengthGrowth.lean','STATUS.txt'},changed_old
    assert not any(p.suffix in ['.olean','.ilean','.ir'] for p in PROJECT.rglob('*') if p.is_file())
    entries=[dict(path=p,repository_path='OpenProblems/LengthGrowth/'+p,local_path=str(PROJECT/p),
        **data,action='update' if p in baseline else 'add',previous_sha256=baseline.get(p,{}).get('sha256'))
        for p,data in final.items() if baseline.get(p)!=data]
    save(OUT/'entries_manifest.json',dict(schema='conditional-product-four-publication-entries-v1',
        publication_performed=False,outputs_synced=False,base_commit_reported_by_root=BASE,
        entries=entries,entry_count=len(entries),total_entry_bytes=sum(e['bytes'] for e in entries),
        project_inventory=final,independent_review_pins=config['reviews']))
    print(json.dumps(dict(status='PASS',audit_count=count,entries=len(entries),
        entries_manifest_sha256=digest(OUT/'entries_manifest.json'))),flush=True)

if __name__=='__main__':main()
