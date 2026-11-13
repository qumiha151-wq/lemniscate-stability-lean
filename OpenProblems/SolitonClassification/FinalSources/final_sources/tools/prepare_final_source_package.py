"""Build a separate, byte-locked source supplement; never modify the core project.

This packages already checked conditional theorems. It performs no compilation,
grid instantiation, upload, or unconditional existence proof.
"""
from pathlib import Path
import argparse,csv,hashlib,io,json,re

ROOT=Path(__file__).resolve().parent
CORE=ROOT/'pipeline/module_production_project_v4'
CORE_INVENTORY_SHA='2c252cf849e22e027ca2630b836e5227b8ff8390cf45f36a6b467db64580c924'
BASE_MANIFEST_SHA='6aaac204087174daa047c18c5592752cc56a3724f91b483f4697568c705bb792'
FROZEN={
 'CertifiedPiFrozenManifest.csv':'7c51f4c663e29860ec0bceb4bb562531eec63d455e28f48a5866452db64b3b30',
 'Endpoint4000FrozenManifest.csv':'be3732b4123731ba98d053dd0aed63cf99c41dcec3bc6b48679a3619168fdc61',
 'FullPathFinalInputsFrozenManifest.csv':'21e0914ca42b2045755db0d6534d839817420c6dec5e13970cae2af1a5d41d98',
 'FullPathFinalGeometryFrozenManifest.csv':'e27f01acf7d5636d0e3ccc58e7ca339cdb11e599fcd2538332a82f0f68979a88',
}
IMPORT=re.compile(r'^(?:public )?import (?:all )?([A-Za-z0-9_.]+)\s*$',re.M)
sha=lambda data:hashlib.sha256(data).hexdigest()
def require(condition,message):
    if not condition: raise ValueError(message)
def read_json(path):return json.loads(path.read_text(encoding='utf-8-sig'))
def csv_rows(path):return list(csv.DictReader(io.StringIO(path.read_text(encoding='utf-8-sig'))))
def safe_relative(text):
    require('\\' not in text and ':' not in text and not text.startswith('/'),'Invalid package path')
    parts=text.split('/')
    require(all(x not in ('','.','..') for x in parts),'Unsafe package path')
    return Path(*parts)
def check_core():
    inventory_path=CORE/'ModuleProductionSourceInventory.json'
    require(sha(inventory_path.read_bytes())==CORE_INVENTORY_SHA,'Core inventory changed')
    inventory=read_json(inventory_path)
    require(len(inventory['files'])==108,'Expected unchanged 108-file core inventory')
    for name,rec in inventory['files'].items():
        data=(CORE/safe_relative(name)).read_bytes()
        require(len(data)==rec['bytes'] and sha(data)==rec['sha256'],'Core file changed: '+name)
    actual={p.relative_to(CORE).as_posix() for p in (CORE/'SolitonClassification').rglob('*.lean')}
    expected={r['source'] for r in inventory['topological_modules']}
    require(actual==expected and len(actual)==88,'Core module tree is not exactly the frozen 88')
    require(sha((ROOT/'ModuleProductionBaseFrozenManifest.csv').read_bytes())==BASE_MANIFEST_SHA,
            'Frozen core manifest changed')
    base=csv_rows(ROOT/'ModuleProductionBaseFrozenManifest.csv')
    require(len(base)==88,'Expected 87 core modules plus one core audit')
    for row,entry in zip(base,inventory['topological_modules'],strict=True):
        require(row['name']==entry['name'] and row['sha256']==entry['sha256'],'Core mapping mismatch')
        require(sha((ROOT/row['source']).read_bytes())==row['sha256'],'Frozen core source changed')
    return inventory,base[:-1]

def role(name):
    short=name.rsplit('.',1)[-1]
    return {
      'CertifiedPi':'certified_constant_enclosure',
      'Endpoint4000Data':'proposed_rational_endpoint_data_not_actual_trajectory',
      'Endpoint4000Finite':'kernel_checked_finite_endpoint_arithmetic',
      'Endpoint4000Meaning':'exact_coordinate_and_matrix_semantics',
      'Endpoint4000ActualComparison':'conditional_actual_endpoint_comparison',
      'Endpoint4000Audit':'recursive_axiom_audit',
      'FullPathBlockEndpoints':'conditional_genuine_grid_to_actual_endpoints',
      'FullPathFinalInputs':'conditional_two_genuine_grids_to_actual_shooting_inputs',
      'FullPathFinalGeometry':'conditional_two_genuine_grids_to_actual_geometry_and_pde',
      'CandidateFinalAssembly':'conditional_actual_shooting_inputs_to_geometry_and_pde',
    }.get(short,'proof_preserving_analytic_module_copy')

def inspect_sources():
    inventory,base=check_core();core={r['name']:r for r in base}
    selected={};manifest_hashes={}
    for manifest,expected in FROZEN.items():
        data=(ROOT/manifest).read_bytes();fingerprint=sha(data)
        require(fingerprint==expected,'Frozen supplement manifest changed: '+manifest)
        manifest_hashes[manifest]=fingerprint
        for row in csv_rows(ROOT/manifest):
            name=row['Module'];source=ROOT/row['Source'];raw=source.read_bytes()
            require(name not in selected,'Duplicate supplemental module: '+name)
            require(name not in core,'Supplement collides with frozen core module: '+name)
            require(sha(raw)==row['SHA256'].lower(),'Frozen supplemental source changed: '+name)
            require(raw.decode('utf-8-sig').startswith('module\n') or
                    raw.decode('utf-8-sig').startswith('module\r\n'),'Expected default module source: '+name)
            selected[name]=dict(name=name,source='final_sources/'+name.replace('.','/')+'.lean',
                origin_source=source.relative_to(ROOT).as_posix(),origin_manifest=manifest,
                sha256=sha(raw),bytes=len(raw),role=role(name),
                imports=IMPORT.findall(raw.decode('utf-8-sig')))
    require(len(selected)==48,'Expected 48 distinct supplemental modules')
    compat={}
    for filename in ['manifest.json','fullpath_manifest.json','finalgeometry_manifest.json']:
        for row in read_json(ROOT/'endpoint4000_compat_source'/filename):
            name=row['module'];require(name not in compat,'Duplicate compatibility provenance')
            require(name in selected,'Compatibility source not selected')
            original=Path(row['original_source']) if 'original_source' in row else ROOT/Path(*name.split('.')).with_suffix('.lean')
            original_raw=original.read_bytes()
            require(sha(original_raw)==row['original_sha256'],'Original analytic source changed: '+name)
            require(selected[name]['sha256']==row['module_sha256'],'Compatibility module hash mismatch')
            converted=(ROOT/selected[name]['origin_source']).read_text(encoding='utf-8-sig')
            restored=converted.removeprefix('module\n\n').replace('\n@[expose] public section\n','',1)
            restored=re.sub(r'^public import ','import ',restored,flags=re.M)
            require(restored==original_raw.decode('utf-8-sig').replace('\r\n','\n'),
                    'Mathematical body differs from original: '+name)
            compat[name]=dict(original_source=str(original.relative_to(ROOT.parent)).replace('\\','/'),
                original_sha256=row['original_sha256'],module_sha256=row['module_sha256'],
                proof_body_unchanged=True)
    require(len(compat)==40,'Expected 40 proof-preserving compatibility copies')
    order=[];active=set();done=set();direct_core=set()
    def visit(name):
        if name in done:return
        require(name not in active,'Cyclic supplemental dependency: '+name);active.add(name)
        rec=selected[name];deps=[];reuse=[]
        for dep in rec['imports']:
            require(not dep.startswith(('CentroidEscape','Migration','OpenTranslators','LengthGrowth')),
                    'Cross-open-problem import: '+dep)
            if dep.startswith('SolitonClassification.'):
                if dep in selected:deps.append(dep);visit(dep)
                else:
                    require(dep in core,'Unresolved project import: '+dep)
                    reuse.append(dep);direct_core.add(dep)
        rec['supplement_dependencies']=deps;rec['core_dependencies']=reuse
        if name in compat:rec['compatibility']=compat[name]
        active.remove(name);done.add(name);order.append(rec)
    for name in selected:visit(name)
    main='SolitonClassification.Rotating.FullPathFinalGeometry'
    main_closure=set()
    def main_visit(name):
        if name in main_closure:return
        main_closure.add(name)
        for dep in selected[name]['supplement_dependencies']:main_visit(dep)
    main_visit(main)
    core_used=set()
    def core_visit(name):
        if name in core_used:return
        core_used.add(name)
        for dep in IMPORT.findall((ROOT/core[name]['source']).read_text(encoding='utf-8-sig')):
            if dep.startswith('SolitonClassification.'):
                require(dep in core,'Core depends on noncore module: '+dep);core_visit(dep)
    for name in direct_core:core_visit(name)
    mapping=[dict(name=r['name'],core_relative_source=r['name'].replace('.','/')+'.lean',
        sha256=r['sha256'],required_transitively=r['name'] in core_used) for r in base]
    return dict(schema='rotating.final-source-supplement.v1',source_only=True,
        full_path_blocks_instantiated=False,unconditional_rotating_example_proved=False,
        core_inventory_sha256=CORE_INVENTORY_SHA,core_inventory_file_count=108,
        core_source_count=88,reused_generic_mapping_count=87,
        reused_generic_required_count=len(core_used),noncore_module_count=len(order),
        final_geometry_dependency_closure_count=len(main_closure),
        auxiliary_modules=sorted(set(selected)-main_closure),
        duplicate_module_sources=0,compatibility_bodies_verified=len(compat),
        lean_toolchain='leanprover/lean4:v4.33.1',mathlib_revision=inventory['mathlib_revision'],
        source_manifests=manifest_hashes,reused_core_modules=mapping,topological_modules=order,
        certificate_boundary=dict(inputs=['genuine +1 4000-step block','genuine -1 4000-step block',
            'four exact initial-state/matrix identities','four exact nominal-endpoint identities'],
            supplied_in_package=False,
            conditional_output='actual unique shooting zero, nonconstant closed rotating profile and pure-normal elastic evolution',
            compilation_order_is_not_grid_instantiation_order=True))

def verify_package(output,core_path=None):
    output=output.resolve();manifest=output/'FinalSourcesManifest.json'
    data=manifest.read_bytes()
    require((output/'FinalSourcesManifest.sha256').read_text().strip()==sha(data),
            'Supplement manifest digest mismatch')
    report=json.loads(data)
    require(report['schema']=='rotating.final-source-supplement.v1','Unknown supplement schema')
    require(report['core_inventory_sha256']==CORE_INVENTORY_SHA and
            report['source_manifests']==FROZEN,'Package does not use the pinned frozen inputs')
    expected=set(report['files'])|{'FinalSourcesManifest.json','FinalSourcesManifest.sha256'}
    actual={p.relative_to(output).as_posix() for p in output.rglob('*') if p.is_file()}
    require(actual==expected,'Missing or unexpected package files')
    for name,row in report['files'].items():
        path=output/safe_relative(name)
        require(not path.is_symlink() and path.resolve().is_relative_to(output),
                'Package symlink or escaping path is forbidden')
        raw=path.read_bytes()
        require(len(raw)==row['bytes'] and sha(raw)==row['sha256'],'Packaged file changed: '+name)
    sources={r['name']:r for r in report['topological_modules']}
    require(len(sources)==len(report['topological_modules'])==48==report['noncore_module_count'],
            'Duplicate or wrong supplement module count')
    locked_sources={}
    for filename,expected_sha in FROZEN.items():
        raw=(output/'final_sources/provenance'/filename).read_bytes()
        require(sha(raw)==expected_sha,'Packaged frozen manifest changed: '+filename)
        for row in csv.DictReader(io.StringIO(raw.decode('utf-8-sig'))):
            require(row['Module'] not in locked_sources,'Duplicate locked source')
            locked_sources[row['Module']]=row['SHA256'].lower()
    require(set(locked_sources)==set(sources),'Packaged module names differ from frozen sources')
    for name,rec in sources.items():
        require(rec['sha256']==locked_sources[name],'Packaged source differs from frozen proof: '+name)
        require(rec['role']==role(name),'Misleading module role: '+name)
    actual_lean={name for name in report['files'] if name.endswith('.lean')}
    require(actual_lean=={r['source'] for r in sources.values()},'Unexpected supplementary Lean source')
    require(not any('.olean' in name or name.endswith(('.exe','.dll','.so'))
                    for name in report['files']),'Source package contains compiled artifacts')
    core={r['name']:r for r in report['reused_core_modules']}
    require(len(core)==len(report['reused_core_modules'])==87 and not (sources.keys()&core.keys()),
            'Duplicate or wrong core mapping')
    base_raw=(output/'final_sources/provenance/ReferencedCoreManifest.csv').read_bytes()
    require(sha(base_raw)==BASE_MANIFEST_SHA,'Packaged reference core manifest changed')
    base_rows=list(csv.DictReader(io.StringIO(base_raw.decode('utf-8-sig'))))
    require(set(core)=={r['name'] for r in base_rows[:-1]},'Wrong reused core module names')
    for row in base_rows[:-1]:
        require(core[row['name']]['sha256']==row['sha256'] and
                core[row['name']]['core_relative_source']==row['name'].replace('.','/')+'.lean',
                'Wrong reused core module hash/path')
    seen=set(core)
    for rec in report['topological_modules']:
        require(rec['source']=='final_sources/'+rec['name'].replace('.','/')+'.lean','Module/source mismatch')
        raw=(output/safe_relative(rec['source'])).read_bytes()
        require(sha(raw)==rec['sha256'],'Module bytes do not match topology entry')
        imports=IMPORT.findall(raw.decode('utf-8-sig'))
        require(imports==rec['imports'],'Module imports do not match dependency graph')
        require(all(d in seen for d in imports if d.startswith('SolitonClassification.')),
                'Unresolved or non-topological project dependency')
        seen.add(rec['name'])
    require(report['full_path_blocks_instantiated'] is False and
            report['unconditional_rotating_example_proved'] is False and
            report['certificate_boundary']['supplied_in_package'] is False,
            'Package overstates the conditional result')
    if core_path is not None:
        core_path=core_path.resolve()
        core_data=(core_path/'ModuleProductionSourceInventory.json').read_bytes()
        require(sha(core_data)==report['core_inventory_sha256'],'Wrong core project inventory')
        inv=json.loads(core_data)
        for name,row in inv['files'].items():
            raw=(core_path/safe_relative(name)).read_bytes()
            require(len(raw)==row['bytes'] and sha(raw)==row['sha256'],'Core file changed: '+name)
        module_paths={r['source'] for r in inv['topological_modules']}
        actual_modules={p.relative_to(core_path).as_posix()
                        for p in (core_path/'SolitonClassification').rglob('*.lean')}
        require(module_paths==actual_modules and len(module_paths)==88,'Core glob changed')
        core_lookup={r['name']:r for r in inv['topological_modules']}
        for name,row in core.items():
            require(core_lookup[name]['sha256']==row['sha256'],'Reused core version differs')
    return report

def generate_package(output,report):
    output=output.resolve()
    protected=[CORE,ROOT/'pipeline/module_experiment',ROOT/'SolitonClassification',
               ROOT/'endpoint4000_compat_source',ROOT.parent/'classification_new']
    require(not any(output.is_relative_to(p.resolve()) for p in protected),'Protected output directory')
    require(not output.exists(),'Output directory must be new')
    blobs={};records={}
    def add(name,data,kind):
        safe_relative(name);require(name not in blobs,'Duplicate output path: '+name)
        blobs[name]=data;records[name]=dict(sha256=sha(data),bytes=len(data),role=kind)
    for rec in report['topological_modules']:
        raw=(ROOT/rec['origin_source']).read_bytes()
        require(sha(raw)==rec['sha256'],'Selected source changed during preparation')
        add(rec['source'],raw,rec['role'])
        short=rec['name'].rsplit('.',1)[-1]
        log=ROOT/'CertifiedPi.check.log' if short=='CertifiedPi' else ROOT/'endpoint4000_build'/(short+'.log')
        add('final_sources/verification/'+short+'.log',log.read_bytes(),'prior_local_compiler_log')
    provenance=list(FROZEN)+[
        'CertifiedPiFrozenStatus.txt','Endpoint4000FrozenStatus.txt',
        'FullPathFinalInputsFrozenStatus.txt','FullPathFinalGeometryFrozenStatus.txt',
        'Endpoint4000FrozenEvidence.json','FullPathFinalInputsFrozenEvidence.json',
        'FullPathFinalGeometryFrozenEvidence.json',
    ]
    for filename in provenance:
        add('final_sources/provenance/'+filename,(ROOT/filename).read_bytes(),'prior_frozen_evidence')
    for filename in ['manifest.json','fullpath_manifest.json','finalgeometry_manifest.json']:
        add('final_sources/provenance/compat_'+filename,
            (ROOT/'endpoint4000_compat_source'/filename).read_bytes(),'proof_body_conversion_bindings')
    add('final_sources/provenance/ReferencedCoreInventory.json',
        (CORE/'ModuleProductionSourceInventory.json').read_bytes(),'unchanged_core_inventory_copy')
    add('final_sources/provenance/ReferencedCoreManifest.csv',
        (ROOT/'ModuleProductionBaseFrozenManifest.csv').read_bytes(),'unchanged_core_manifest_copy')
    add('final_sources/tools/prepare_final_source_package.py',Path(__file__).read_bytes(),'source_preparation_and_verification_tool')
    add('final_sources/.gitattributes',b'* -text\n','byte_preserving_checkout')
    scope='''SUPPLEMENTAL ROTATING CERTIFICATE SOURCES — CONDITIONAL SCOPE

This source-only supplement contains 48 distinct default-module Lean files:
47 form the final geometry theorem's noncore dependency closure and one is
the separate Endpoint4000Audit. Forty compatibility copies have exactly the
same mathematical bodies as their frozen originals; only module/export
headers differ. The eight other sources are the new pi, endpoint and final
composition modules. The source manifest gives the actual dependency order,
roles, hashes, origins and complete mapping to the reused 87 generic modules.
Only 83 of those 87 modules are required transitively by this supplement.

The directory final_sources/SolitonClassification is deliberately outside the
existing project's top-level SolitonClassification source tree. Nothing here
changes its default Lake glob, 88 core source modules, 108-file inventory,
lakefile, base lock, production generator or numeric shard sources. Do not
silently merge these sources into the default core target. A later explicit
build/staging configuration may select this independent manifest.

NO COMPLETE GRID INSTANCE IS INCLUDED. Endpoint4000Data contains proposed
rational endpoint states and full 6-by-6 matrices. Finite arithmetic and pi
bounds are checked, but those data become actual endpoints only through the
explicit genuine signed-grid premises. FullPathFinalGeometry proves:
  two genuine 4000-step signed PolynomialPointGridBlock certificates,
  four exact initial state/matrix identities and four exact nominal endpoint
  identities imply an actual unique shooting zero, nonconstant closed rotating
  profile, and future-global pure-normal elastic evolution.
It does not construct either complete block. A conditional theorem may be
compiled before its premises are instantiated; this order is NOT a claim
that the numeric grid or the unconditional rotating example is certified.
The closing period is 114*c2 and total curvature is -56*(2*pi). No minimal
period, embeddedness or full-classification claim is made.

The sources have prior local Lean 4.33.1 checks with standard-three axioms.
The final geometry audit covered 2205 imported Rotating/ClosedSimilarity
declarations. Logs and frozen evidence are included as provenance. This
packaging run performs no Lean compile, Linux validation, numerical grid
verification, archive transport test, or publication. It contains no .olean,
private/server artifact, native executable, or generated numeric shard.
Mathlib is pinned to revision 0df444a360eaa60ab8c11dca51a86af692955474.
CertifiedPi imports the ordinary upstream Complex.Arctan module; no patched
Mathlib source is included. Ordinary dependency compilation may need to build
that module if its cache is absent.

To verify this package without accessing the original workspace:
  python final_sources/tools/prepare_final_source_package.py \\
    --verify-package . --core-path PATH_TO_UNCHANGED_MODULE_PRODUCTION
The optional --core-path also verifies every original core inventory file and
its 88-module source tree. Without it, package bytes, module dependency order
and explicit conditional scope are still verified. This is a packaging check,
not a substitute for Lean or the missing complete numeric certificates.

To reproduce packaging, run the original prepare_final_source_package.py from
its frozen workspace with --output NEW_DIRECTORY. Its --plan mode performs
the exact-source/core/body inventory checks without copying a package.
'''
    add('final_sources/Scope.txt',scope.encode('utf-8'),'scope_and_reproduction_boundary')
    report=dict(report,preparer_sha256=sha(Path(__file__).read_bytes()),files=records,
                packaging_did_not_compile=True,linux_supplement_rebuild_completed=False)
    manifest=(json.dumps(report,indent=2,ensure_ascii=False)+'\n').encode('utf-8')
    output.mkdir(parents=True)
    for name,data in blobs.items():
        path=output/safe_relative(name);path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
    (output/'FinalSourcesManifest.json').write_bytes(manifest)
    (output/'FinalSourcesManifest.sha256').write_text(sha(manifest)+'\n',encoding='ascii')
    require(inspect_sources()=={k:v for k,v in report.items() if k not in
        {'preparer_sha256','files','packaging_did_not_compile','linux_supplement_rebuild_completed'}},
        'Input snapshot changed during packaging')
    verify_package(output,CORE)
    return report,sha(manifest)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan',action='store_true')
    parser.add_argument('--output',type=Path)
    parser.add_argument('--verify-package',type=Path)
    parser.add_argument('--core-path',type=Path)
    args=parser.parse_args()
    if args.verify_package is not None:
        report=verify_package(args.verify_package,args.core_path)
        print('Verified source package:',report['noncore_module_count'],'noncore modules; no grid instantiation.')
        return
    report=inspect_sources()
    if args.plan:
        print(json.dumps({k:report[k] for k in ['noncore_module_count',
            'final_geometry_dependency_closure_count','auxiliary_modules','duplicate_module_sources',
            'compatibility_bodies_verified','reused_generic_required_count']},indent=2))
        for i,rec in enumerate(report['topological_modules'],1):print(i,rec['name'],rec['role'])
        return
    require(args.output is not None,'Specify --plan or --output')
    report,fingerprint=generate_package(args.output,report)
    print('Prepared',report['noncore_module_count'],'noncore modules,',len(report['files']),
          'inventoried files; manifest SHA256',fingerprint)

if __name__=='__main__':main()
