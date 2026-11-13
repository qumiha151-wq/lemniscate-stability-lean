"""Stage six frozen additions and compile only the root and original audit.

No GitHub operation, outputs synchronization, leaf recompilation, or changes
to the other independent projects are performed by this script.
"""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys, time

sys.stdout.reconfigure(encoding='utf-8')
ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OUT = HERE / 'stage_v1'
PROJECT = OUT / 'project'
BUILD = OUT / 'build'
OLD = ROOT / 'outputs/open-problems/LengthGrowth'
PRIOR = ROOT / 'work/actual_flow_publication/stage_v1'
FLOW = ROOT / 'work/length_flow_formal'
MATH = Path('C:/Users/17815/Desktop/论文/lean_deps/mathlib4-4.33.1')
LEAN = Path('C:/Users/17815/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean.exe')
BASE_COMMIT = '79e178475d7d813f047a71b57da0c7f6c2585e0e'
NEW = {
 'ArclengthCoordinate': ('e318ec6a58f5b7ff7cc626818d80b59067ab9ee7065dbd365b72d9ff5bbee019',
  'arclength_owned_build/ArclengthCoordinate/1794552966728900600',
  '396b62c054a3e58078ba4e25515c672461286fba10b7f9f318fa18990e86384c'),
 'ArclengthSmooth': ('4acb3ad93ff88eb488319e4904af1c5b7d664b2fe4048ad5d60aee258d9060b4',
  'arclength_owned_build/ArclengthSmooth/1794553061747135500',
  'cda832bf32641654709d7073e50ccd23b7f0950b5e918c0e2febe1ce2d740534'),
 'ArclengthTransport': ('64b963a6615410798db670643f210f99a43f990c54a2deae0a280d5be90985a4',
  'arclength_transport_build/1794553040816468400',
  'd9329019ef509e9a3dae971d7762261ef8a06580839e2a723053dc19bca6ad48'),
 'ArclengthIntegrals': ('05a09dc220fca02a59a99c109421071f2508925226adfd2fcc8e9e8e87dfd122',
  'arclength_integrals_build/1794553324690988100',
  '03bd5b149ef0635cccb167abd1adcda0db7732a8d67791ff9de2f189b3d818e9'),
 'ArclengthCoercivity': ('1676e62c2448a8249eca499418a20acee6583574279233a1552566f13ac37514',
  'arclength_coercivity_build/1794553464003301300',
  'e1c4fc1908c57ec96b2b4fc97ede03c7e3b7b8ed3e0819d9003463de20d1b9b6'),
 'NormalizedProduct': ('ab826f872a5e30ce4852c1de3f668719aae42bd5de1d016493cccbcde1aab5b5',
  'normalized_product_build/1794553603161595200',
  'a0fe258ab6e145cff4b8ce8b57ad4b95ec21487219de8a81570a83a21adb13d1'),
}
REVIEWS = {
 'ArclengthCoordinateSmoothRootReview.txt': 'd72f4c55179fba013f26c00e06632196c6028b848f929bc1781024ae8fcba4f2',
 'ArclengthTransportIndependentReview.txt': '0939445d48ea3e1f020579c767958ace772f63c9c6e265b93568943570d5a71e',
 'ArclengthFinalAdapterIndependentReview.txt': '12bee80c09951ef3e198384709cc4aa8f1d505e8d9456f11712cea59b32d1dc4',
 'NormalizedProductRootReview.txt': '579da37b0664c3a872382bdbae9259dd863ca1bb105943b27f96f001580c3e31',
}

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024), b''): h.update(chunk)
    return h.hexdigest()
def info(path):
    p=Path(path)
    return {'sha256':digest(p),'bytes':p.stat().st_size}
def write_json(path, obj):
    Path(path).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
def snapshot(folder):
    return {p.relative_to(folder).as_posix():info(p) for p in sorted(folder.rglob('*')) if p.is_file()}
def imports(path):
    return re.findall(r'^(?:public )?import\s+([A-Za-z0-9_.]+)\s*$',Path(path).read_text(encoding='utf-8-sig'),re.M)
def clean_log(path):
    text=Path(path).read_text(encoding='utf-8-sig')
    assert text.strip() and not re.search(r'\b(?:error|warning|sorryAx)\b',text),path
    return text

def main():
    assert not OUT.exists(), 'Refusing to reuse a stage directory'
    baseline=snapshot(OLD)
    other_before={p.name:snapshot(p) for p in (ROOT/'outputs/open-problems').iterdir()
                  if p.is_dir() and p!=OLD}
    selected={str(Path(__file__).resolve()):info(__file__),str(LEAN):info(LEAN)}
    previous=json.loads((PRIOR/'project/ActualFlowEvidence/Integration.json').read_text())
    assert previous['status']=='PASS' and previous['actual_recursive_audit_count']==570
    assert digest(PRIOR/'selected_inputs_before.json')==previous['selected_input_manifest_sha256']
    assert digest(PRIOR/'staged_project_before.json')==previous['source_project_sha256']
    previous_sources=json.loads((PRIOR/'staged_project_before.json').read_text())
    previous_inputs=json.loads((PRIOR/'selected_inputs_before.json').read_text())
    previous_modules=json.loads((PRIOR/'project/ActualFlowEvidence/Modules.json').read_text())
    old_expected={r['module']:r['artifact']['sha256'] for r in previous_modules['new_modules']}
    old_leaves=[p for p in sorted((OLD/'LengthGrowth').rglob('*.lean')) if p.name!='AxiomAudit.lean']
    assert len(old_leaves)==34
    leaves=[]
    for src in old_leaves:
        relative=src.relative_to(OLD)
        assert info(src)==previous_sources[relative.as_posix()],relative
        module='.'.join(relative.with_suffix('').parts)
        obj=PRIOR/'build'/relative.with_suffix('.olean')
        if module not in old_expected:
            origin=ROOT/'work/next_research/circle_backtracking_root_audit_v2'/relative.with_suffix('.olean')
            old_expected[module]=previous_inputs[str(origin)]['sha256']
        assert digest(obj)==old_expected[module],module
        selected[str(src)]=info(src); selected[str(obj)]=info(obj)
        leaves.append(dict(module=module,source=str(src),source_info=info(src),
          artifact=str(obj),artifact_info=info(obj),new=False,imports=imports(src)))
    # All six source/object hashes are anchored in the author freeze messages.
    for name,(source_sha,folder,object_sha) in NEW.items():
        src=FLOW/f'LengthGrowth/ActualFlow/{name}.lean'
        evidence=FLOW/folder
        obj=evidence/f'{name}.olean'
        report=json.loads((evidence/'result.json').read_text())
        assert digest(src)==source_sha==report['source_sha256'],name
        assert digest(obj)==object_sha,name
        assert report['exit_code']==0 and report['source_unchanged'] and report['dependency_outputs_unchanged'],name
        if 'dependency_sources_unchanged' in report: assert report['dependency_sources_unchanged']
        assert digest(evidence/'setup.json')==report['setup_sha256'],name
        clean_log(evidence/'stdout.txt'); assert (evidence/'stderr.txt').read_bytes()==b''
        for key in ('dependency_pins','dependency_artifact_pins','dependency_source_pins'):
            for path,sha in report.get(key,{}).items():
                assert digest(path)==sha,path
                selected[path]=info(path)
        for p in (src,obj,*[p for p in evidence.iterdir() if p.suffix=='.json' or p.name in ('stdout.txt','stderr.txt')]):
            selected[str(p)]=info(p)
        leaves.append(dict(module=f'LengthGrowth.ActualFlow.{name}',source=str(src),source_info=info(src),
          artifact=str(obj),artifact_info=info(obj),new=True,imports=imports(src),
          author_evidence=str(evidence),author_result_sha256=digest(evidence/'result.json')))
    for name,sha in REVIEWS.items():
        path=FLOW/name
        assert digest(path)==sha,name
        selected[str(path)]=info(path)
    scope=HERE/'ArclengthAndProductScope.txt'
    selected[str(scope)]=info(scope)
    by_module={row['module']:row for row in leaves}
    assert len(by_module)==40
    order=[]
    while len(order)<40:
        choices=[m for m in sorted(by_module) if m not in order and all(
          dep in order for dep in by_module[m]['imports'] if dep.startswith('LengthGrowth.'))]
        assert choices, 'Cycle or absent project dependency'
        order.extend(choices)
    OUT.mkdir(parents=True)
    shutil.copytree(OLD,PROJECT)
    evidence=PROJECT/'ArclengthEvidence'; evidence.mkdir()
    arts={}
    for module in order:
        row=by_module[module]
        relative=Path(*module.split('.'))
        obj=BUILD/relative.with_suffix('.olean'); obj.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(row['artifact'],obj)
        arts[module]=[[str(obj)],[]]
        if row['new']:
            shutil.copyfile(row['source'],PROJECT/relative.with_suffix('.lean'))
            author=evidence/module.rsplit('.',1)[1]; author.mkdir()
            for p in Path(row['author_evidence']).iterdir():
                if p.suffix=='.json' or p.name in ('stdout.txt','stderr.txt'):
                    shutil.copyfile(p,author/p.name)
    # Reuse the two officially built missing Mathlib-cache modules unchanged.
    sr_path=FLOW/'symmetric_dependency/build_v1/report.json'
    assert digest(sr_path)=='7ec7dae9256c3ca68d0519a323938eaeb5d1c5783565be5972f1fdb9ea39e7f4'
    sr=json.loads(sr_path.read_text())
    for module,layers in sr['importArts'].items():
        arts[module]=layers
        for group in layers:
            for p in group: selected[p]=info(p)
    selected[str(sr_path)]=info(sr_path)
    assert len(arts)==42
    root=PROJECT/'LengthGrowth.lean'
    root_text=root.read_text(encoding='utf-8')
    root_text='import LengthGrowth.ActualFlow.ArclengthCoercivity\nimport LengthGrowth.ActualFlow.NormalizedProduct\n'+root_text
    root_text += '''\n/-!
The actual arclength adapter constructs a global smooth parameter inverse
from arbitrary-speed position and transports curvature, force, E, D and A.
It supplies the legacy static coercivity bounds for the actual material
integrals of each forward slice, including time zero. It also proves E>0
and the coarse bound A>=1; it does not prove a uniform-in-time A bound.

For actual forward normal FEF, NormalizedProduct defines e=E L and proves
e'=E ell-L D, (e^2)'<=E^4, and
e(t)^2-e(s)^2<=integral_s^t E(r)^4 dr for 0<=s<=t.
No energy-clock or ancient-limit theorem is included. The unrestricted
fourth-root growth question remains open. See ArclengthAndProductScope.txt.
-/\n'''
    root.write_text(root_text,encoding='utf-8')
    status=PROJECT/'STATUS.txt'; text=status.read_text(encoding='utf-8')
    text += '''\nACTUAL ARCLENGTH AND ENERGY-LENGTH PRODUCT ADDITION
Six new modules now construct the global smooth arclength inverse from an
actual arbitrary-speed periodic immersion and transport its intrinsic force
and material E/D/A integrals. The existing static coercivity estimates now
apply directly to those actual material quantities, including forward time
zero. The coarse A>=1 and E>0 statements are also proved on each slice.
NormalizedProduct defines e=E L for the actual flow and proves e'=E ell-L D,
(e^2)'<=E^4 and e(t)^2-e(s)^2<=integral_s^t E^4, for 0<=s<=t.
This batch contains no time-uniform A or EL bound, energy-clock theorem,
ancient-limit theorem, or arbitrary-data existence theorem. General
quarter-power growth remains unresolved. The project now has 40 mathematical
leaves, plus its entry point and unchanged recursive audit. See
ArclengthAndProductScope.txt and ArclengthEvidence for exact scope and checks.
'''
    text=text.replace('General-speed arclength reparameterization and dynamic A(t) bounds are\noutside this addition; unrestricted length growth remains unresolved.',
      'That earlier unit-speed addition did not include general-speed arclength\nreparameterization; the new six-module addition below now supplies it.\nDynamic A(t) bounds and unrestricted length growth remain unresolved.')
    text=text.replace('quadratic envelope. Geometric PDE identities and unrestricted quarter-power\ngrowth remain unresolved. See SubsqrtGrowthScope.txt and its frozen manifest.',
      'quadratic envelope. The later ActualFlow chain supplies the geometric PDE\nidentities; unrestricted quarter-power growth remains unresolved. See\nSubsqrtGrowthScope.txt for the original scalar-only addition and its manifest.')
    status.write_text(text,encoding='utf-8')
    shutil.copyfile(scope,PROJECT/scope.name)
    for name in REVIEWS: shutil.copyfile(FLOW/name,evidence/name)
    write_json(evidence/'Modules.json',dict(schema='arclength-product-six-leaves-v1',
      leaves=leaves,topological_order=order,new_leaf_count=6,prior_leaf_count=34,
      author_leaf_recompilations_in_this_integration=0,base_commit_reported_by_root=BASE_COMMIT))
    root_imports=imports(root)
    closure=set()
    def visit(module):
        if module in closure: return
        assert module in by_module,module
        closure.add(module)
        for dep in by_module[module]['imports']:
            if dep.startswith('LengthGrowth.'): visit(dep)
    for dep in root_imports:
        if dep.startswith('LengthGrowth.'): visit(dep)
    assert closure==set(by_module)
    assert digest(PROJECT/'LengthGrowth/AxiomAudit.lean')==digest(OLD/'LengthGrowth/AxiomAudit.lean')
    staged_before=snapshot(PROJECT); build_before=snapshot(BUILD)
    write_json(OUT/'baseline_project.json',baseline)
    write_json(OUT/'other_projects_before.json',other_before)
    write_json(OUT/'selected_inputs_before.json',selected)
    write_json(OUT/'staged_sources_before.json',staged_before)
    dependencies=[MATH/'.lake/build/lib/lean']+sorted(p/'.lake/build/lib/lean'
      for p in (MATH/'.lake/packages').iterdir() if (p/'.lake/build/lib/lean').is_dir())
    env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,dependencies)))
    checks=[]
    for module,src in [('LengthGrowth',root),('LengthGrowth.AxiomAudit',PROJECT/'LengthGrowth/AxiomAudit.lean')]:
        setup=dict(name=module,isModule=False,package=None,plugins=[],dynlibs=[],options={},importArts=dict(arts))
        setup_path=OUT/(module+'.setup.json'); write_json(setup_path,setup)
        output=BUILD/Path(*module.split('.')).with_suffix('.olean')
        argv=[str(LEAN),'--setup',str(setup_path),'-M','4096','-j','1','-o',str(output),str(src)]
        print('Compiling '+module,flush=True); start=time.monotonic()
        p=subprocess.run(argv,cwd=PROJECT,env=env,capture_output=True,timeout=300)
        stdout=evidence/(module+'.stdout.txt'); stderr=evidence/(module+'.stderr.txt')
        stdout.write_bytes(p.stdout); stderr.write_bytes(p.stderr)
        row=dict(module=module,argv=argv,exit_code=p.returncode,seconds=time.monotonic()-start,
          source=info(src),setup=info(setup_path),stdout=info(stdout),stderr=info(stderr))
        checks.append(row); write_json(OUT/'progress.json',checks)
        print(p.stdout.decode('utf-8',errors='replace'),end='',flush=True)
        print(p.stderr.decode('utf-8',errors='replace'),end='',flush=True)
        assert p.returncode==0 and not re.search(rb'\b(?:error|warning|sorryAx)\b',p.stdout+p.stderr)
        row['output']=info(output); arts[module]=[[str(output)],[]]
        shutil.copyfile(setup_path,evidence/setup_path.name)
    audit_text=clean_log(evidence/'LengthGrowth.AxiomAudit.stdout.txt')
    count=int(re.search(r'Length-growth audit passed: (\d+) declarations; standard axioms only',audit_text).group(1))
    assert count>570
    assert snapshot(OLD)==baseline, 'Published base changed during staging'
    assert {p.name:snapshot(p) for p in (ROOT/'outputs/open-problems').iterdir()
            if p.is_dir() and p!=OLD}==other_before, 'Other project changed during staging'
    assert all(info(p)==data for p,data in selected.items()),'Selected frozen input changed'
    assert all(info(PROJECT/p)==data for p,data in staged_before.items()),'Staged input changed'
    assert all(info(BUILD/p)==data for p,data in build_before.items()),'Reused object changed'
    verification=dict(schema='arclength-product-project-integration-v1',status='PASS',
      base_commit_reported_by_root=BASE_COMMIT,actual_integration_calls=checks,
      prior_mathematical_leaves=34,new_mathematical_leaves=6,reused_mathematical_leaves=40,
      leaf_recompilations=0,original_audit_source_unchanged=True,prior_evidence_unchanged=True,
      actual_recursive_audit_count=count,allowed_axioms=['propext','Classical.choice','Quot.sound'],
      selected_inputs_unchanged=True,base_outputs_unchanged=True,other_projects_unchanged=True,
      staged_sources_unchanged=True,reused_artifacts_unchanged=True,
      explicit_root_importArts=42,no_project_LEAN_PATH=True,ordinary_mathlib_roots=list(map(str,dependencies)),
      whole_mathlib_cache_snapshot_performed=False,old_evidence_rewritten=False,
      actual_arclength_and_material_coercivity_proved=True,actual_normalized_product_bound_proved=True,
      energy_clock_formalized=False,ancient_window_formalized=False,general_quarter_power_growth_proved=False,
      runner_sha256=digest(__file__),selected_inputs_sha256=digest(OUT/'selected_inputs_before.json'),
      staged_before_sha256=digest(OUT/'staged_sources_before.json'))
    write_json(evidence/'Integration.json',verification)
    shutil.copyfile(OUT/'selected_inputs_before.json',evidence/'SelectedInputs.json')
    shutil.copyfile(__file__,evidence/'prepare_and_check.py')
    final=snapshot(PROJECT)
    # The only existing repository files allowed to change are root and STATUS.
    changed_old={p for p,data in baseline.items() if final.get(p)!=data}
    assert changed_old=={'LengthGrowth.lean','STATUS.txt'},changed_old
    assert not any(p.suffix in ('.olean','.ilean','.ir') for p in PROJECT.rglob('*') if p.is_file())
    entries=[dict(path=p,repository_path='OpenProblems/LengthGrowth/'+p,local_path=str(PROJECT/p),
      **data,action='update' if p in baseline else 'add',previous_sha256=baseline.get(p,{}).get('sha256'))
      for p,data in final.items() if baseline.get(p)!=data]
    write_json(OUT/'entries_manifest.json',dict(schema='arclength-product-six-publication-entries-v1',
      publication_performed=False,outputs_synced=False,base_commit_reported_by_root=BASE_COMMIT,
      entries=entries,entry_count=len(entries),total_entry_bytes=sum(e['bytes'] for e in entries),
      project_inventory=final,independent_review_pins=REVIEWS))
    print(json.dumps(dict(status='PASS',audit_count=count,entries=len(entries),
      entries_manifest_sha256=digest(OUT/'entries_manifest.json'))),flush=True)

if __name__=='__main__': main()
