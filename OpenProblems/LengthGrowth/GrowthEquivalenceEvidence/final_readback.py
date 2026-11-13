"""Post-check immutable prior source/object anchors and finalize text entries.
No Lean call, output synchronization, network access or remote writes.
"""
from pathlib import Path
import hashlib,json,re,shutil
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=HERE/'stage_v1';PROJECT=OUT/'project';BUILD=OUT/'build'
PRIOR=ROOT/'work/conditional_publication/stage_v1'
OLD=ROOT/'outputs/open-problems/LengthGrowth'
EVIDENCE=PROJECT/'GrowthEquivalenceEvidence'

def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def info(path):return dict(sha256=digest(path),bytes=Path(path).stat().st_size)
def snapshot(folder):return {p.relative_to(folder).as_posix():info(p) for p in sorted(folder.rglob('*')) if p.is_file()}
def read(path):return json.loads(Path(path).read_text(encoding='utf-8'))
def save(path,value):Path(path).write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8')

assert not (EVIDENCE/'FinalReadback.json').exists()
self_before=info(__file__)
prior_manifest=PRIOR/'entries_manifest.json'
assert digest(prior_manifest)=='19b46e65ecf2da0b0a952fc26fe94cdf524520ec1ca6ca6b7edca97b5e75f562'
prior=read(prior_manifest);prior_inventory=prior['project_inventory']
assert snapshot(OLD)==prior_inventory==read(OUT/'baseline_project.json')
assert snapshot(PRIOR/'project')==prior_inventory
module_rel='ConditionalGrowthEvidence/Modules.json'
module_path=PRIOR/'project'/module_rel
assert info(module_path)==prior_inventory[module_rel]
assert digest(module_path)=='8eaf918c60e0aace27af6717163b3f9324fa80454d6461193df4dc904b1c5628'
prior_rows=read(module_path)['leaves'];assert len(prior_rows)==44
prior_setup_path=PRIOR/'LengthGrowth.setup.json'
setup_rel='ConditionalGrowthEvidence/LengthGrowth.setup.json'
assert info(prior_setup_path)==prior_inventory[setup_rel]
assert info(PRIOR/'project'/setup_rel)==prior_inventory[setup_rel]
prior_arts=read(prior_setup_path)['importArts']
assert {k for k in prior_arts if k.startswith('LengthGrowth.')}=={r['module'] for r in prior_rows}
anchors=[]
for row in prior_rows:
    module=row['module'];rel=Path(*module.split('.'))
    source_rel=rel.with_suffix('.lean').as_posix()
    assert row['source_info']==prior_inventory[source_rel]
    assert info(OLD/source_rel)==row['source_info']
    assert info(PRIOR/'project'/source_rel)==row['source_info']
    groups=prior_arts[module]
    assert len(groups)==2 and len(groups[0])==1 and groups[1]==[]
    object_path=Path(groups[0][0])
    assert object_path.resolve()==(PRIOR/'build'/rel.with_suffix('.olean')).resolve()
    assert info(object_path)==row['artifact_info']
    assert info(BUILD/rel.with_suffix('.olean'))==row['artifact_info']
    anchors.append(dict(module=module,published_source=prior_inventory[source_rel],
        prior_setup_object=str(object_path),object_info=info(object_path)))

integration=read(EVIDENCE/'Integration.json')
assert integration['status']=='PASS' and integration['actual_recursive_audit_count']==802
assert integration['leaf_recompilations']==0 and integration['reused_mathematical_leaves']==48
assert integration['base_commit_reported_by_root']=='d713b33de6e6498f9ac1260ed9a3d041aff02042'
for row in integration['actual_integration_calls']:
    assert row['exit_code']==0
    name=row['module'];relative=Path(*name.split('.'))
    assert info(PROJECT/relative.with_suffix('.lean'))==row['source']
    assert info(OUT/(name+'.setup.json'))==row['setup']
    assert info(EVIDENCE/(name+'.stdout.txt'))==row['stdout']
    assert info(EVIDENCE/(name+'.stderr.txt'))==row['stderr']
    assert info(BUILD/relative.with_suffix('.olean'))==row['output']
    assert not (EVIDENCE/(name+'.stderr.txt')).read_bytes()
    assert not re.search(rb'\b(?:warning|error|sorryAx)\b',(EVIDENCE/(name+'.stdout.txt')).read_bytes())
assert (EVIDENCE/'LengthGrowth.AxiomAudit.stdout.txt').read_text().strip()==(
    'Length-growth audit passed: 802 declarations; standard axioms only.')
assert digest(PROJECT/'LengthGrowth/AxiomAudit.lean')==digest(OLD/'LengthGrowth/AxiomAudit.lean')
for p,pin in read(OUT/'selected_inputs_before.json').items():assert info(p)==pin,p
for rel,pin in read(OUT/'staged_sources_before.json').items():assert info(PROJECT/rel)==pin,rel
assert {p.name:snapshot(p) for p in (ROOT/'outputs/open-problems').iterdir() if p.is_dir() and p!=OLD}==read(OUT/'other_projects_before.json')

old_entries_path=OUT/'entries_manifest.json';old_entries=read(old_entries_path)
assert snapshot(PROJECT)==old_entries['project_inventory']
old_entries_sha=digest(old_entries_path)
shutil.copyfile(old_entries_path,OUT/'entries_manifest.pre_readback.json')
shutil.copyfile(__file__,EVIDENCE/'final_readback.py')
report=dict(schema='growth-equivalence-final-readback-v1',status='PASS',
    base_commit='d713b33de6e6498f9ac1260ed9a3d041aff02042',
    prior_entries_manifest=info(prior_manifest),prior_published_inventory_exact=True,
    prior_modules_table=info(module_path),prior_modules_anchored_in_published_inventory=True,
    prior_root_setup=info(prior_setup_path),prior_root_setup_anchored_in_published_inventory=True,
    prior_leaf_source_object_correspondences=anchors,prior_leaf_count=44,
    actual_integrator=info(HERE/'prepare_and_check.py'),integration=info(EVIDENCE/'Integration.json'),
    pre_readback_entries_sha256=old_entries_sha,actual_recursive_audit_count=802,
    current_selected_inputs_rehashed=True,current_all_project_files_rehashed=True,
    current_outputs_unchanged=True,other_projects_unchanged=True,
    original_axiom_audit_source_unchanged=True,prior_evidence_unchanged=True,
    lean_calls_in_postcheck=0,leaf_recompilations=0,
    publication_performed=False,outputs_synced=False,
    whole_mathlib_cache_rehashed=False,postchecker=self_before)
save(EVIDENCE/'FinalReadback.json',report)
final=snapshot(PROJECT)
changed_old={p for p,data in prior_inventory.items() if final.get(p)!=data}
assert changed_old=={'LengthGrowth.lean','STATUS.txt'}
assert not any(p.suffix in ['.olean','.ilean','.ir'] for p in PROJECT.rglob('*') if p.is_file())
entries=[dict(path=p,repository_path='OpenProblems/LengthGrowth/'+p,local_path=str(PROJECT/p),
    **data,action='update' if p in prior_inventory else 'add',previous_sha256=prior_inventory.get(p,{}).get('sha256'))
    for p,data in final.items() if prior_inventory.get(p)!=data]
old_entries.update(entries=entries,entry_count=len(entries),total_entry_bytes=sum(e['bytes'] for e in entries),
    project_inventory=final,final_readback=info(EVIDENCE/'FinalReadback.json'))
save(old_entries_path,old_entries)
assert snapshot(PROJECT)==final
assert snapshot(OLD)==prior_inventory
assert info(__file__)==self_before
summary=dict(status='PASS',integration_session=51100,actual_recursive_audit_count=802,
    entries=len(entries),entry_bytes=sum(e['bytes'] for e in entries),
    project_files=len(final),prior_files=len(prior_inventory),
    old_entries_unchanged=len(prior_inventory)-2,
    changed_old=sorted(changed_old),final_entries_manifest=info(old_entries_path),
    final_readback=info(EVIDENCE/'FinalReadback.json'),
    scope=info(PROJECT/'GrowthEquivalenceScope.txt'),
    integration=info(EVIDENCE/'Integration.json'),postchecker=self_before,
    source_modules=48,actual_lean_calls=2,leaf_recompilations=0,
    remote_actions=0,outputs_synced=False)
save(OUT/'FinalStageSummary.json',summary)
print(json.dumps(summary,indent=2))
