"""Read-only full-assembly input validation and recursive public closure index.

No Lean elaboration or full-grid stub is produced. The production CLI accepts
only externally pinned complete250 inputs and the actual same-base Linux48.
Pure graph helpers also support explicitly synthetic and tiny local tests.
"""
from pathlib import Path, PurePosixPath
from types import SimpleNamespace
from functools import lru_cache
import argparse, hashlib, importlib, json, os, re, shutil, stat, sys

SOURCE_REVISION='cff971bcac7ac2d83aba04596ce09e44fda1ac29'
PIPELINE_SHA='598bee6a58a1d0531944f229fd1a7a1c6522f2bfcb06e61a96ee7cc5e7ff4b57'
CORE_SHA='2c252cf849e22e027ca2630b836e5227b8ff8390cf45f36a6b467db64580c924'
FINAL_SHA='51e1abe4b94640773e1fe66f93cfc1ad58a57fafbd050a260eba53da0f61fd72'
ASSEMBLY_SHA='93675bac7479a6fdcde5c247ef21fa568f4971c5c114078a7fb5f4c976e5c492'
ENDPOINT_SHA='9b559bff52f049ffe627982256f5ec2d4a732ebcc4518ba491e4d2834f26ebb0'
CANDIDATE_SHA='697b53e7bd0546a26c2dc10769a9b93c5d5082a386644d6f9ac908d53f28bb70'
CENSUS_SHA='1b445de33e2fdcb97676b22c5a50f014845c616c7bd845d880bd74f6672ce116'
BASE_SHA='dcf9b162c42c30f387803fc9f395fcb1183f0e8179f5b46004782ba4bbf1f10d'
PLAN_SHA='a62ef654ec4f2fd01d55b6dae19c28483dba137c424c3068a372c514b89559c1'
# Exact UTF-8 bytes of the deterministic audit text in the pinned final runner.
# Also matched against the actually compiled portable source in the patch test.
FINAL_AUDIT_SOURCE_SHA='596379ef8a531b49d8f13feaf198706a7304807d45d8a82dcbac67cd339c8cfb'
HELPERS={
 'production_projection_merge.py':'b0508cb0168b01077f2d90bc341daeca756cb6c3b43aec3c7ebbf2013c5f5625',
 'production_projection_transport.py':'784bf78a8cf0d0be458553f4ed82eb9b096d36681fcda2622e152fd92f5adf34',
 'production_public_projection.py':'b206b8a43a3e1b9a47a31ab33b038ca2ac351a461b810d9265f183019c56708d',
 'production_compile_shard.py':'f0abd2db3d6b8db32707d33e8ebb8a6aaee7da0c6f2332c9c4da8e931c64310b',
 'production_artifact.py':'ddb448165391a04ab1ffcd9e4b572f9945f29fab5e1fa6ec981adad4b56323b5',
 'production_core_artifact.py':'1ead0d5ced187dbf2d9847f7b08ea7f7a1e8931fe88ce8461c284fa277c73ea6',
 'stage_public_archives.py':'44f7407c525d4882b2efde128eed23477e06d5e94dbef06673743476e6d4cbb9',
 'plan_production_grid.py':'61ea4ae11174cffa51dd5b4fc3c1caba05838b54b05d14c4793f4846ca864cca',
 'propose_grid42x22.py':'dcd5024d5d182763cf91ca552080065dbe7dab6cec18bb1f49f7b07a5911c183',
 '../performance/reference.py':'e586dcd92c56567232ce7751765eec5a55377d1e7f6398291606d674aa5568b4',
 'verify_production_pipeline.py':'1787d96c83e97a12233d3c5bfa35c4b9a8788ee9213bc61a608c06c452d3a63a',
 'production_compile_final_supplement.py':'14c9360c15517658200649cafff904948184ac4b23194ab60aac15926dba8dd5'}


def require(ok,message):
    if not ok: raise ValueError(message)
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def strict_json(raw):
    def pairs(items):
        result={}
        for key,value in items:
            require(key not in result,'Duplicate JSON key: '+key);result[key]=value
        return result
    return json.loads(raw,object_pairs_hook=pairs)
def read(path): return strict_json(Path(path).read_bytes())
def data_sha(value): return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def record(path): return {'sha256':sha(path),'bytes':Path(path).stat().st_size}
def save(path,value): Path(path).write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8',newline='\n')
def pinned(path,digest):
    require(re.fullmatch('[0-9a-f]{64}',digest or '') is not None and sha(path)==digest,
            'Externally pinned bytes differ: '+str(path))
    return read(path)
def module_path(name):
    require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',name) is not None,'Invalid module name')
    return name.replace('.','/')+'.olean'


def plain(path,must_exist=True):
    path=Path(os.path.abspath(path))
    for part in [*reversed(path.parents),path]:
        if os.path.lexists(part):
            st=part.lstat()
            require(not stat.S_ISLNK(st.st_mode) and not getattr(st,'st_file_attributes',0)&0x400,
                    'Linked/reparse path component: '+str(part))
    require(not must_exist or path.exists(),'Missing input: '+str(path))
    return path


def relative_path(root,name):
    require(isinstance(name,str) and re.fullmatch(r'[A-Za-z0-9_./-]+',name) is not None,
            'Unsafe evidence path')
    p=PurePosixPath(name)
    require(not p.is_absolute() and p.as_posix()==name and all(x not in ('.','..') for x in p.parts),
            'Noncanonical evidence path')
    result=plain(Path(root)/name,must_exist=False)
    require(result.is_relative_to(plain(root)),'Evidence path escaped root')
    return result


def graph_index(rows,project_prefix):
    """Conservative all-header-edge graph; does not certify arbitrary input rows."""
    graph={};folded=set()
    for row in rows:
        name=row['name'];module_path(name)
        require(name.startswith(project_prefix+'.') and name.casefold() not in folded,
                'Duplicate/case-fold or foreign project module: '+name)
        require(isinstance(row['imports'],list) and len(row['imports'])==len(set(row['imports'])),
                'Duplicate or malformed source imports')
        for dep in row['imports']:module_path(dep)
        folded.add(name.casefold());graph[name]=[d for d in row['imports'] if d.startswith(project_prefix+'.')]
    active=set()
    @lru_cache(None)
    def closure(name):
        require(name in graph,'Missing transitive project module: '+name)
        require(name not in active,'Cyclic project imports: '+name)
        active.add(name);found=set(graph[name])
        for dep in graph[name]:found.update(closure(dep))
        active.remove(name)
        return tuple(sorted(found))
    closures={name:list(closure(name)) for name in graph}
    return graph,closures


def validate_order(initial_names,planned,graph):
    seen=set(initial_names)
    for row in planned:
        name=row['name']
        require(name not in seen and all(d in seen for d in graph[name]),
                'Collision or non-topological planned import: '+name)
        seen.add(name)


def validate_public_tree(root,available):
    root=plain(root);actual=set()
    for path in root.rglob('*'):
        require(not path.is_symlink() and not (hasattr(path,'is_junction') and path.is_junction()),'Linked public tree')
        if path.is_file():actual.add(path.relative_to(root).as_posix())
    require(actual=={module_path(n) for n in available},'Extra/missing primary or private/server/IR project artifact')
    for name,row in available.items():
        require(record(root/module_path(name))==row,'Changed public primary: '+name)


def validate_external_roots(roots,project_prefix):
    for root in roots:
        path=Path(root)
        require(not (path/project_prefix).exists() and not (path/(project_prefix+'.olean')).exists(),
                'Project namespace exposed in fallback root')


def closure_setup(name,closures,available,public_root):
    require(name in closures,'Unknown target')
    selected=closures[name]
    require(all(n in available for n in selected),'An actual transitive primary has not been supplied')
    arts={n:[[str((Path(public_root)/module_path(n)).resolve())],[]] for n in selected}
    return {'name':name,'isModule':True,'package':None,'plugins':[],'dynlibs':[],'options':{},'importArts':arts}


def validate_setup(actual,expected):
    require(actual==expected and 'imports' not in actual,'Setup changed/overrides source imports/private map')


def full_scope(ledger,merge,plan_sha,base_sha):
    require(ledger['mode']=='full' and merge['mode']=='full','Pilot is not complete250 evidence')
    require(ledger['source_revision']==merge['revision']==SOURCE_REVISION,'Foreign source revision')
    require(ledger['plan_sha256']==merge['plan_sha256']==plan_sha
            and ledger['base_lock_sha256']==merge['base_lock_sha256']==base_sha,'Mixed plan/base identities')
    expected=[(f'R{tag}{start:04d}',sign,start,32) for tag,sign in [('P',1),('M',-1)] for start in range(0,4000,32)]
    require([(r['key'],r['sign'],r['start'],r['count']) for r in ledger['jobs']]==expected,'Incomplete or reordered full250 coverage')
    require(isinstance(ledger['publication_revision'],str)
            and re.fullmatch('[0-9a-f]{40}',ledger['publication_revision']) is not None,'Missing publication revision')
    require(all(isinstance(j['durable_record_sha256'],str)
                and re.fullmatch('[0-9a-f]{64}',j['durable_record_sha256']) is not None for j in ledger['jobs']),
            'Full ledger requires durable original proof bindings')
    require(merge['status']=='inputs_prepared' and merge['all_250_projections_validated'] is True
            and merge['actual_lean_import_checked'] is False and merge['inter_shard_seams_proved'] is False
            and merge['full_certificate_proved'] is False,'Invalid merge status/scope')


def load_helpers():
    root=Path(__file__).resolve().parent
    for relative,digest in HELPERS.items():require(sha(root/relative)==digest,'Frozen helper changed: '+relative)
    merge=importlib.import_module('production_projection_merge')
    runner=importlib.import_module('production_compile_final_supplement')
    package=importlib.import_module('verify_production_pipeline')
    for relative in HELPERS:
        name=Path(relative).stem;module=sys.modules.get(name)
        if module is not None:
            require(Path(module.__file__).resolve()==(root/relative).resolve(),'Imported helper from unpinned origin')
    return merge,runner,package


def checked_tree(root,files,extra=()):
    actual=set();root=Path(root)
    for path in root.rglob('*'):
        require(not path.is_symlink() and not (hasattr(path,'is_junction') and path.is_junction()),'Linked evidence tree')
        if path.is_file():actual.add(path.relative_to(root).as_posix())
    require(actual==set(files)|set(extra),'Extra/missing merged evidence file')
    for relative,wanted in files.items():require(record(relative_path(root,relative))==wanted,'Changed merged evidence: '+relative)


def validate_final_report(report,base_sha):
    require(report['schema']=='rotating.final-supplement-build.v1' and report['status']=='checked'
            and report['base_lock_sha256']==base_sha and report['supplement_manifest_sha256']==FINAL_SHA
            and report['core_inventory_sha256']==CORE_SHA,'Wrong actual48 report/source/base')
    require(report['supplementary_modules_checked']==48 and report['conditional_geometry_audit_count']==2205
            and report['fresh_public_only_audit_checked'] is True and report['private_project_input_files']==0
            and report['extra_external_setup_modules']==[] and report['extra_external_setup_bindings']==[]
            and report['full_path_instances_checked'] is False and report['full_certificate_proved'] is False,
            'Actual48 report overstates scope or has extra project inputs')
    require('linux' in report['lean']['version'].lower(),'Actual48 must be from the same Linux captured core')
    rows=report['modules'];audit=report['fresh_audit']
    require(len(rows)==48 and len({r['name'] for r in rows})==48
            and audit['name']=='SolitonClassification.Rotating.FinalSupplementFreshAudit', 'Wrong actual48/audit modules')
    require(all(r['exit_code']==0 and r['termination']=='completed' for r in [*rows,audit]),'An actual48/audit call failed')
    helpers={Path(n.replace('\\','/')).name:v for n,v in report['helper_sha256'].items()}
    require(len(report['helper_sha256'])==2 and helpers=={n:HELPERS[n] for n in
        ['production_compile_final_supplement.py','production_compile_shard.py']},'Actual48 runner identity differs')


def validate_final_setup(setup,name,public):
    """Check archived absolute mappings without using their old filesystem paths."""
    metadata={k:v for k,v in setup.items() if k!='importArts'}
    require(metadata=={'name':name,'isModule':True,'package':None,'plugins':[],'dynlibs':[],'options':{}},
            'Actual48 setup changes imports/plugins/options')
    require(set(setup['importArts'])==set(public),'Actual48 setup does not map precisely its proven inputs')
    origins=set()
    for dep,entry in setup['importArts'].items():
        require(isinstance(entry,list) and len(entry)==2 and isinstance(entry[0],list)
                and len(entry[0])==1 and entry[1]==[] and isinstance(entry[0][0],str),
                'Actual48 setup includes private/server/IR or invalid mapping')
        value=entry[0][0].replace('\\','/');suffix='/public_inputs/'+module_path(dep)
        require(value.endswith(suffix) and (value.startswith('/') or re.match(r'^[A-Za-z]:/',value)),
                'Actual48 setup path is not its canonical public primary')
        origins.add(value[:-len(suffix)])
    require(len(origins)==1,'Actual48 setup mixes input origins')


def check_final_row(output,row,imports,public,runner):
    name=row['name'];stem=name.replace('.','_')
    require(row['public_input_hashes']==public,'Actual48 public input hashes differ from prior checked origins')
    files={'source/'+module_path(name)[:-6]+'.lean':row['source_record'],
           'setups/'+stem+'.json':row['setup_record'],'logs/'+stem+'.log':row['log_record'],
           'logs/'+stem+'.imports.json':row['parsed_header_record']}
    require(row['source_record']['sha256']==row['source_sha256']
            and row['setup_record']['sha256']==row['setup_sha256']
            and row['parsed_header_record']['sha256']==row['parsed_header_sha256'],'Actual48 duplicate digest mismatch')
    require(set(row['artifacts'])=={'','.private','.server'},'Incomplete actual48 output bundle')
    files.update({'checked/'+module_path(name)+s:r for s,r in row['artifacts'].items()})
    for rel,wanted in files.items():require(record(relative_path(output,rel))==wanted,'Changed actual48 evidence: '+rel)
    parsed=read(output/('logs/'+stem+'.imports.json'))
    require(parsed==row['parsed_header'] and parsed=={'imports':[{'errors':[],
            'result':runner.expected_header(imports)}]},'Actual48 parsed flags/errors differ')
    validate_final_setup(read(output/('setups/'+stem+'.json')),name,public)
    contents=(output/('logs/'+stem+'.log')).read_text(encoding='utf-8')
    require('error:' not in contents and 'warning:' not in contents,'Actual48 contains a diagnostic')
    return files


def validate_fresh_audit(source,contents):
    require(sha(source)==FINAL_AUDIT_SOURCE_SHA,'Fresh actual48 audit differs from the fixed checked runner source')
    require('FINAL_SUPPLEMENT_CONDITIONAL_AUDIT 2205' in contents,'Fresh actual48 audit marker is absent')


def validate(args):
    # Full-scope pins precede any base inspection, scratch directory or Lean call.
    for name in ('ledger','merged','pipeline_package','core_project','final_package','final_output',
                 'assembly_root','endpoint_root','candidate_source','census','base_lock','base_args'):
        setattr(args,name,plain(getattr(args,name)))
    args.output=plain(args.output,must_exist=False)
    ledger=pinned(args.ledger,args.ledger_sha256)
    merge_record=pinned(args.merged/'merge_receipt.json',args.merge_receipt_sha256)
    final_report=pinned(args.final_output/'compile_report.json',args.final_report_sha256)
    require(merge_record['schema']=='rotating.public-merge-receipt.v1','Wrong merged receipt schema')
    require(args.base_lock_sha256==BASE_SHA,'Wrong exact production core lock')
    full_scope(ledger,merge_record,PLAN_SHA,BASE_SHA);validate_final_report(final_report,BASE_SHA)
    require(merge_record['ledger_sha256']==args.ledger_sha256,'Merge receipt not bound to supplied ledger')
    merger,runner,package=load_helpers();compiler=merger.compiler;core=merger.core;projector=merger.p
    package.verify(args.pipeline_package,PIPELINE_SHA,args.core_project)
    plan_path=args.pipeline_package/'plan/plan.json';plan=pinned(plan_path,PLAN_SHA)
    merger.validate_ledger(ledger,plan,'full')
    require(merge_record['helper_sha256']==merger.helpers(),'Wrong merged-input helper closure')
    require(merge_record['jobs']==[{k:j[k] for k in ('key','receipt_sha256','full_archive_sha256')}
            for j in ledger['jobs']] and merge_record['original_archives_deleted'] is False,
            'Merged job receipts/original retention differ from ledger')
    require((args.merged/'merge_receipt.sha256').read_text().strip()==args.merge_receipt_sha256,'Wrong merge digest sidecar')
    checked_tree(args.merged,merge_record['files'],('merge_receipt.json','merge_receipt.sha256'))
    core_manifest=pinned(args.core_project/'ModuleProductionSourceInventory.json',CORE_SHA)
    final_manifest=pinned(args.final_package/'FinalSourcesManifest.json',FINAL_SHA)
    runner.load_package_verifier(args.final_package).verify_package(args.final_package,args.core_project)
    assembly=pinned(args.assembly_root/'assembly_manifest.json',ASSEMBLY_SHA)
    endpoints=pinned(args.endpoint_root/'endpoint_links_manifest.json',ENDPOINT_SHA)
    census=pinned(args.census,CENSUS_SHA)
    require(sha(args.candidate_source)==CANDIDATE_SHA,'Final application source changed')
    binding=read(args.pipeline_package/'plan/PlanRevisionBinding.json')
    require(assembly['inputs']['plan_sha256']==binding['original_plan_sha256']
            and binding['production_plan_sha256']==PLAN_SHA
            and endpoints['assembly_manifest_sha256']==ASSEMBLY_SHA,'Wrong exact old/new plan rebinding')
    require(not args.output.exists(),'Execution-plan output must be new')
    for protected in (args.pipeline_package,args.core_project,args.final_package,args.merged,args.final_output,
                      args.assembly_root,args.endpoint_root):
        require(not args.output.resolve().is_relative_to(protected.resolve())
                and not protected.resolve().is_relative_to(args.output.resolve()),'Output overlaps protected inputs')
    ctx=runner.base_context(args.base_args,args.base_lock,BASE_SHA)
    for protected in ctx['roots'].values():
        require(not args.output.is_relative_to(protected.resolve())
                and not protected.resolve().is_relative_to(args.output),'Output overlaps a locked base root')
    require(final_report['lean']==ctx['identity'],'Actual48 compiler/runtime differs from current exact base')
    expected_core={r['name'] for r in core_manifest['topological_modules']}
    actual_core={n for n in ctx['primary'] if n.startswith('SolitonClassification.')}
    require(actual_core==expected_core,'Captured core is not exactly frozen88')
    core_labels={ctx['primary'][n][2] for n in expected_core}
    external=[r for label,r in ctx['roots'].items() if label not in core_labels]
    validate_external_roots(external,'SolitonClassification')
    args.output.mkdir(parents=True);scratch=args.output/'_projection_view'
    initial=[];available={};all_layers={};source_records={};final_files={};before_pins={
        'ledger':(args.ledger,args.ledger_sha256),'merge':(args.merged/'merge_receipt.json',args.merge_receipt_sha256),
        'final_report':(args.final_output/'compile_report.json',args.final_report_sha256),
        'self':(Path(__file__),sha(__file__))}
    def add(row,path,origin,layers):
        name=row['name'];require(name not in available,'Duplicate checked module')
        primary=record(path)
        require(layers['']==primary,'Wrong primary proof-layer identity')
        available[name]={'path':str(path.resolve()),**primary,'source_sha256':row['sha256'],'origin':origin}
        all_layers[name]=layers
        initial.append({'name':name,'imports':row['imports']})
    def base_layers(name):
        _,_,label=ctx['primary'][name];rel=module_path(name)
        return {s:ctx['lock']['files'][label+'/'+rel+s] for s in compiler.SIDE if label+'/'+rel+s in ctx['lock']['files']}
    for row in core_manifest['topological_modules']:
        if row['name'].endswith('.ModuleFullGenericAudit'):continue
        source=compiler.confined(args.core_project,row['source'])
        require(sha(source)==row['sha256'] and compiler.header_imports(source)==row['imports'],'Frozen core header/source changed')
        source_records[source]=record(source)
        path,expected,label=ctx['primary'][row['name']];require(record(path)==expected,'Core primary changed')
        add(row,path,{'kind':'captured_core','label':label,'base_lock_sha256':BASE_SHA},base_layers(row['name']))
    final_public={n:{k:r[k] for k in ('sha256','bytes')} for n,r in available.items()}
    for job in ledger['jobs']:
        key=job['key'];ev=args.merged/'evidence'/key
        receipt=pinned(ev/'projection.json',job['receipt_sha256'])
        scratch.mkdir()
        try:
            for relative,wanted in receipt['files'].items():
                source=relative_path(args.merged if relative.startswith('public/') else ev,relative)
                require(record(source)==wanted,'Projection view does not match merged bytes')
                target=compiler.confined(scratch,relative);target.parent.mkdir(parents=True,exist_ok=True)
                shutil.copyfile(source,target)
            for filename in ('projection.json','projection.sha256'):shutil.copyfile(ev/filename,scratch/filename)
            opts=SimpleNamespace(plan=plan_path,plan_sha256=PLAN_SHA,revision=SOURCE_REVISION,key=key,
                archive_sha256=job['full_archive_sha256'],base_lock_sha256=BASE_SHA,
                durable_record_sha256=job['durable_record_sha256'],require_durable=True,max_metadata_mb=8,max_public_mb=4)
            projector.verify_projection(scratch,opts,job['receipt_sha256'])
            manifest=read(scratch/'metadata/manifest.json');report=read(scratch/'metadata/compile_report.json')
            require(report['lean']==ctx['identity'],'Shard compiler/runtime differs from captured core')
            require(len(manifest['modules'])==len(report['modules'])==47,'Wrong actual shard module count')
            for row,actual in zip(manifest['modules'],report['modules']):
                require(row['name']==actual['name'] and row['sha256']==actual['source_sha256']
                        and actual['imports_before']==actual['imports_after']
                        and set(actual['imports_before'])==set(['Init',*row['imports']]),'Source/report import binding differs')
                for dep,info in actual['imports_before'].items():
                    if dep.startswith('SolitonClassification.'):
                        require(dep in available and info=={'artifacts':all_layers[dep]},
                                'Shard imports wrong/unproved project proof layers')
                    else:
                        require(dep in ctx['primary'] and info=={'artifacts':base_layers(dep)},
                                'Shard external import differs from same locked base')
                primary=args.merged/'public'/module_path(row['name'])
                require(record(primary)==actual['artifacts'][''],'Projected primary differs from actual compile')
                add(row,primary,{'kind':'checked_shard','key':key,'receipt_sha256':job['receipt_sha256']},actual['artifacts'])
        finally:
            if scratch.exists():
                resolved=scratch.resolve();require(resolved.parent==args.output.resolve() and resolved.name=='_projection_view',
                                                  'Unsafe owned scratch cleanup')
                shutil.rmtree(resolved)
    require(len(available)==87+11750,'Wrong complete shard/core module count')
    require(merge_record['modules']=={n:{k:r[k] for k in ('sha256','bytes')} for n,r in available.items()
            if r['origin']['kind']=='checked_shard'},'Merged module index differs from actual receipt union')
    rows=final_report['modules']
    require([r['name'] for r in rows]==[r['name'] for r in final_manifest['topological_modules']],
            'Actual48 order differs from frozen source manifest')
    for declared,actual in zip(final_manifest['topological_modules'],rows):
        name=declared['name'];source=args.final_output/'source'/Path(*name.split('.')).with_suffix('.lean')
        frozen=compiler.confined(args.final_package,declared['source'])
        require(sha(source)==sha(frozen)==declared['sha256']==actual['source_sha256']
                and compiler.header_imports(source)==declared['imports'],'Actual48 source/header changed')
        source_records[frozen]=record(frozen)
        final_files.update(check_final_row(args.final_output,actual,declared['imports'],final_public,runner))
        final_public[name]=actual['artifacts']['']
        add(declared,args.final_output/'checked'/module_path(name),{'kind':'actual_Linux48',
            'report_sha256':args.final_report_sha256},actual['artifacts'])
    produced={r['name']:r for r in [*rows,final_report['fresh_audit']]}
    runner.validate_outputs(args.final_output/'checked',produced)
    audit=final_report['fresh_audit'];name=audit['name']
    audit_source=args.final_output/'source'/Path(*name.split('.')).with_suffix('.lean')
    final_files.update(check_final_row(args.final_output,audit,compiler.header_imports(audit_source),final_public,runner))
    validate_fresh_audit(audit_source,(args.final_output/'logs'/(name.replace('.','_')+'.log')).read_text(encoding='utf-8'))
    validate_public_tree(args.final_output/'public_inputs',final_public)
    planned=[]
    for collection,root in ((assembly['modules'],args.assembly_root),(endpoints['modules'],args.endpoint_root)):
        for row in collection:
            source=compiler.confined(root,row['source'])
            require(sha(source)==row['sha256'] and compiler.header_imports(source)==row['imports'],'Planned source/header changed')
            source_records[source]=record(source)
            planned.append({**row,'source_path':str(source.resolve())})
    source_records[args.candidate_source]=record(args.candidate_source)
    planned.append({'name':'SolitonClassification.Rotating.FullCandidate','sha256':CANDIDATE_SHA,
        'source_path':str(args.candidate_source.resolve()),'imports':compiler.header_imports(args.candidate_source)})
    require(len(planned)==502 and [r['name'] for r in planned]==[r['name'] for r in census['actual_assembly_sources_read_and_hashed']],
            'Wrong actual502 source order')
    require(all(r['sha256']==c['source_sha256'] for r,c in zip(planned,census['actual_assembly_sources_read_and_hashed'])),
            'Source differs from reviewed census')
    graph,closures=graph_index([*initial,*planned],'SolitonClassification')
    for row in [*initial,*planned]:
        require(all(d.startswith('SolitonClassification.') or d in ctx['primary'] for d in row['imports']),
                'Source has an unpinned external import')
    validate_order(available,planned,graph)
    require(len(available)==11885,'Wrong actual public index count')
    public_index={'schema':'rotating.assembly-public-index.v1','modules':dict(sorted(available.items())),
        'ledger_sha256':args.ledger_sha256,'merge_receipt_sha256':args.merge_receipt_sha256,
        'actual_Linux48_report_sha256':args.final_report_sha256,'base_lock_sha256':BASE_SHA}
    execution={'schema':'rotating.assembly-execution-plan.v1','status':'inputs_and_source_graph_validated',
        'source_revision':SOURCE_REVISION,'production_plan_sha256':PLAN_SHA,
        'original_source_plan_sha256':binding['original_plan_sha256'],'public_index_digest':data_sha(public_index),
        'planned_modules':[{**r,'project_closure':closures[r['name']],
                           'closure_name_digest':data_sha(closures[r['name']])} for r in planned],
        'graph':graph,'new_Lean_elaborations':0,'full_path_instances_checked':False,'full_certificate_proved':False}
    checked_tree(args.merged,merge_record['files'],('merge_receipt.json','merge_receipt.sha256'))
    for path,digest in before_pins.values():require(sha(path)==digest,'Pinned input changed during validation')
    for path,wanted in source_records.items():require(record(path)==wanted,'Reviewed source changed during validation')
    for relative,wanted in final_files.items():require(record(relative_path(args.final_output,relative))==wanted,
                                                       'Actual48 evidence changed during validation')
    validate_public_tree(args.final_output/'public_inputs',final_public)
    runner.validate_outputs(args.final_output/'checked',produced)
    package.verify(args.pipeline_package,PIPELINE_SHA,args.core_project);runner.base_final_check(ctx);load_helpers()
    save(args.output/'public_input_index.json',public_index);save(args.output/'execution_plan.json',execution)
    return {'status':execution['status'],'actual_checked_input_primaries':len(available),'planned_modules':502,
        'public_input_index_sha256':sha(args.output/'public_input_index.json'),
        'execution_plan_sha256':sha(args.output/'execution_plan.json'),'new_Lean_elaborations':0,'full_certificate_proved':False}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('ledger','merged','pipeline-package','core-project','final-package','final-output',
                 'assembly-root','endpoint-root','candidate-source','census','base-lock','base-args','output'):
        parser.add_argument('--'+name,type=Path,required=True)
    for name in ('ledger-sha256','merge-receipt-sha256','final-report-sha256','base-lock-sha256'):
        parser.add_argument('--'+name,required=True)
    args=parser.parse_args();print(json.dumps(validate(args)),flush=True)


if __name__=='__main__':main()
