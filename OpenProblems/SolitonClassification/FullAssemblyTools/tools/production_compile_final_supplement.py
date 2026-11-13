"""Fresh, portable, public-only compilation of the separately frozen final48.

No numeric blocks are instantiated. No captured base, source package or old
artifact is modified. There is deliberately no resume or imports override.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,time,types
import production_compile_shard as compiler

MANIFEST_SHA='51e1abe4b94640773e1fe66f93cfc1ad58a57fafbd050a260eba53da0f61fd72'
VERIFIER_SHA='03dc3121c4f3b6aa4cd0b33475bcb56671372ec2f7d45adfa8996b1b68d0d1af'
SCHEMA='rotating.final-supplement-build.v1'
ARCTAN='Mathlib.Analysis.SpecialFunctions.Complex.Arctan'
ARCTAN_SOURCE_SHA='f7d25dac9724284dd8820b4841ac21ef9dabd98ad03ab3caf6e92ac80e623613'

def require(ok,message):
    if not ok:raise ValueError(message)
def read_json(path):return json.loads(Path(path).read_text(encoding='utf-8-sig'))
def digest_bytes(raw):return hashlib.sha256(raw).hexdigest()
def record_file(path):return dict(sha256=compiler.digest(path),bytes=path.stat().st_size)
def check_file(path,expected):
    require(path.is_file() and not path.is_symlink() and record_file(path)==expected,
            'Missing or changed pinned file: '+str(path))

def validate_public_inputs(directory,records):
    actual=set()
    for path in directory.rglob('*'):
        require(not path.is_symlink(),'Symlink in public inputs')
        if path.is_file():actual.add(path.relative_to(directory).as_posix())
    expected={compiler.module_file(name) for name in records}
    require(actual==expected,'Unlisted public input or private/server/IR artifact')
    for name,row in records.items():check_file(directory/compiler.module_file(name),row)

def validate_outputs(directory,records):
    expected={compiler.module_file(name)+s for name,row in records.items() for s in row['artifacts']}
    actual=set()
    for path in directory.rglob('*'):
        require(not path.is_symlink(),'Symlink in checked output')
        if path.is_file():actual.add(path.relative_to(directory).as_posix())
    require(actual==expected,'Unlisted or missing checked output artifact')
    for name,row in records.items():
        require(compiler.bundle(directory/compiler.module_file(name))==row['artifacts'],
                'Completed output changed: '+name)

def validate_setup(path,expected):
    raw=path.read_bytes()
    require(json.loads(raw)==expected and 'imports' not in expected,
            'Setup map altered or source imports overridden')
    return digest_bytes(raw)

def expected_header(imports):
    item=lambda name,meta=False:dict(module=name,isMeta=meta,isExported=True,importAll=False)
    return dict(isModule=True,imports=[item('Init'),item('Init',True)]+[item(x) for x in imports])

def parse_header(lean,source,env,expected,log):
    result=subprocess.run([str(lean),'--deps-json',str(source)],env=env,capture_output=True,text=True)
    log.write_text(result.stdout+result.stderr,encoding='utf-8')
    require(result.returncode==0,'Lean header parser failed')
    parsed=json.loads(result.stdout)
    require(len(parsed.get('imports',[]))==1,'Unexpected header result count')
    entry=parsed['imports'][0]
    require(entry.get('errors')==[] and entry.get('result')==expected,
            'Lean header/ordinary-meta Init flags differ from manifest')
    return parsed

def stop_child(child):
    if child.poll() is None:
        child.terminate()
        try:child.wait(timeout=10)
        except subprocess.TimeoutExpired:child.kill();child.wait()
    return child.returncode

def base_context(base_args,base_lock,expected_hash):
    raw_args=Path(base_args).read_bytes();raw_lock=Path(base_lock).read_bytes()
    require(digest_bytes(raw_lock)==expected_hash,'Base lock identity differs')
    parser=argparse.ArgumentParser(add_help=False)
    parser.add_argument('--lean',required=True);parser.add_argument('--base-root',action='append',required=True)
    parsed=parser.parse_args(json.loads(raw_args));roots=compiler.roots_from_args(parsed.base_root)
    lean,identity=compiler.lean_identity(parsed.lean);lock=json.loads(raw_lock)
    require(lock.get('schema')=='rotating.production-base.v1' and lock['lean']==identity
            and lock['root_order']==list(roots),'Wrong base/toolchain identity')
    require(re.search(r'\bversion 4\.33\.1\b',identity['version']) is not None,'Wrong Lean version')
    automatic=Path(subprocess.check_output([str(lean),'--print-libdir'],text=True).strip()).resolve()
    require(any(automatic.is_relative_to(p) for p in roots.values()),'Automatic stdlib is not locked')
    print('Checking whole captured base before supplementary compilation.',flush=True)
    require(compiler.base_snapshot(roots)==lock['files'],'Whole base differs from lock')
    primary={}
    for label in lock['root_order']:
        for key,row in lock['files'].items():
            prefix,relative=key.split('/',1)
            if prefix==label and relative.endswith('.olean'):
                name=relative[:-6].replace('/','.')
                if name not in primary:primary[name]=(roots[label]/relative,row,label)
    return dict(lean=lean,identity=identity,roots=roots,lock=lock,primary=primary,
                base_args=Path(base_args),base_lock=Path(base_lock),raw_args=raw_args,raw_lock=raw_lock)

def base_final_check(ctx):
    require(ctx['base_args'].read_bytes()==ctx['raw_args'] and ctx['base_lock'].read_bytes()==ctx['raw_lock'],
            'Base argument or lock file changed')
    require(compiler.lean_identity(str(ctx['lean']))[1]==ctx['identity'],'Compiler/runtime changed')
    print('Checking whole captured base after supplementary compilation.',flush=True)
    require(compiler.base_snapshot(ctx['roots'])==ctx['lock']['files'],'Whole base changed during run')

def allowed_setup_extras(ctx,all_direct,names,source):
    """Only the previously checked upstream Arctan may use the local cache bridge."""
    if not names:
        require(source is None,'An extra source without the Arctan option is not allowed')
        return {},[]
    require(list(names)==[ARCTAN],'Only the single allowlisted upstream Arctan override is allowed')
    require(source is not None,'Original upstream Arctan source is required')
    source=Path(source).resolve()
    require(source.is_file() and compiler.digest(source)==ARCTAN_SOURCE_SHA,
            'Extra Arctan source differs from the checked upstream bytes')
    require(ARCTAN in all_direct and ARCTAN in ctx['primary'],'Arctan is not an actual pinned dependency')
    path,primary,label=ctx['primary'][ARCTAN];root=ctx['roots'][label]
    rel=compiler.module_file(ARCTAN);artifacts={};artifact_paths={}
    for suffix in [*compiler.SIDE,'.ir.sig','.ir']:
        relative=rel[:-6]+suffix if suffix.startswith('.ir') else rel+suffix
        key=label+'/'+relative;actual=root/relative
        if key in ctx['lock']['files']:
            expected=ctx['lock']['files'][key];check_file(actual,expected);artifacts[suffix]=expected
            artifact_paths[suffix]=str(actual)
        else:require(not actual.exists(),'Unlisted Arctan sidecar at selected origin')
    require(set(compiler.SIDE)<=set(artifacts),'Arctan override requires all three checked olean layers')
    require('.ir' not in artifacts or '.ir.sig' in artifacts,'Arctan IR has no signature')
    mathlib_roots=[(n,r) for n,r in ctx['roots'].items() if (r/'Mathlib').is_dir()]
    require(mathlib_roots,'No default Mathlib root')
    first_label,_=mathlib_roots[0]
    if label!=first_label:
        extra_names={k.split('/',1)[1] for k in ctx['lock']['files']
                     if k.startswith(label+'/Mathlib/') and k.endswith('.olean')}
        require(extra_names=={rel},'Local extra root contains non-allowlisted Mathlib modules')
        require(list(ctx['roots']).index(label)>list(ctx['roots']).index(first_label),
                'Partial extra Mathlib root would shadow the complete default root')
    olean_parts=[str(path),str(path)+'.server',str(path)+'.private']
    ir_parts=[artifact_paths[s] for s in ['.ir.sig','.ir'] if s in artifacts]
    return {ARCTAN:[olean_parts,ir_parts]},[dict(name=ARCTAN,origin_label=label,
        origin_root=str(root),primary=str(path),artifacts=artifacts,artifact_paths=artifact_paths,
        source=str(source),source_record=record_file(source),upstream_source_sha256=ARCTAN_SOURCE_SHA,
        default_mathlib_origin_label=first_label)]

def run_batch(ctx,source_root,modules,core_names,project_prefix,output,audit,
              seconds,memory_mb,extra_imports=(),checkpoint=None,extra_source=None):
    """Shared strict engine; production entry below fixes the complete48 scope."""
    output=Path(output).resolve();source_root=Path(source_root).resolve()
    require(not output.exists(),'Output must be a new directory; resume is disabled')
    for protected in [source_root,*ctx['roots'].values()]:
        require(not (output.is_relative_to(protected) or protected.is_relative_to(output)),
                'Output overlaps source or captured base')
    names=[r['name'] for r in modules]
    require(len(names)==len(set(names)) and len({n.casefold() for n in names})==len(names),
            'Duplicate module names')
    require(not (set(names)&set(core_names)),'Supplement collides with core')
    require(all(n not in ctx['primary'] for n in [*names,audit['name']]),'Module already exists in locked base')
    core_labels=set()
    for name in core_names:
        require(name in ctx['primary'],'Missing core primary: '+name)
        core_labels.add(ctx['primary'][name][2])
    for label,root in ctx['roots'].items():
        if label not in core_labels:
            require(not (root/project_prefix).exists() and not (root/(project_prefix+'.olean')).exists(),
                    'Project namespace exposed in external fallback root')
    seen=set(core_names)
    for item in modules:
        source=compiler.confined(source_root,item['source'])
        require(compiler.digest(source)==item['sha256'],'Source differs before run: '+item['name'])
        require(compiler.header_imports(source)==item['imports'],'Source header differs')
        for dep in item['imports']:
            if dep.startswith(project_prefix+'.'):require(dep in seen,'Non-topological project import')
            else:require(dep in ctx['primary'],'Unpinned external direct import: '+dep)
        seen.add(item['name'])
    all_direct={d for r in modules for d in r['imports']}
    external,extra_records=allowed_setup_extras(ctx,all_direct,extra_imports,extra_source)
    output.mkdir(parents=True)
    inputs=output/'public_inputs';inputs.mkdir()
    checked=output/'checked';checked.mkdir()
    sources=output/'source';sources.mkdir()
    setups=output/'setups';setups.mkdir()
    logs=output/'logs';logs.mkdir()
    temp=output/'temporary';temp.mkdir()
    helpers={str(Path(p).resolve()):compiler.digest(p) for p in [__file__,compiler.__file__]}
    public={};produced={};report=dict(schema=SCHEMA,status='running',full_certificate_proved=False,
        full_path_instances_checked=False,modules=[],fresh_audit=None,
        base_lock_sha256=digest_bytes(ctx['raw_lock']),base_args_sha256=digest_bytes(ctx['raw_args']),
        lean=ctx['identity'],helper_sha256=helpers,extra_external_setup_modules=list(extra_imports),
        extra_external_setup_bindings=extra_records,
        private_project_input_files=0,cpu_seconds=None,peak_memory_bytes=None)
    def save():compiler.atomic_json(output/'compile_report.json',report)
    def validate_all():
        validate_public_inputs(inputs,public);validate_outputs(checked,produced)
        for entry in extra_records:
            check_file(Path(entry['source']),entry['source_record'])
            for suffix,expected in entry['artifacts'].items():check_file(Path(entry['artifact_paths'][suffix]),expected)
        require(all(compiler.digest(p)==h for p,h in helpers.items()),'Runner/helper code changed')
        for name,row in produced.items():
            check_file(sources/Path(*name.split('.')).with_suffix('.lean'),row['source_record'])
            check_file(Path(row['setup']),row['setup_record']);check_file(Path(row['log']),row['log_record'])
            check_file(Path(row['parsed_header_log']),row['parsed_header_record'])
        if checkpoint:checkpoint()
    try:
        for name in core_names:
            path,row,_=ctx['primary'][name];check_file(path,row)
            target=inputs/compiler.module_file(name);target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(path.read_bytes());check_file(target,row);public[name]=row
        env=os.environ.copy()
        env['LEAN_PATH']=os.pathsep.join(str(root) for label,root in ctx['roots'].items() if label not in core_labels)
        require(env['LEAN_PATH'] and all(env['LEAN_PATH'].split(os.pathsep)),'Empty external search path')
        env['LC_ALL']='C'
        for index,item in enumerate([*modules,audit]):
            fresh=index==len(modules);name=item['name'];relative=Path(*name.split('.')).with_suffix('.lean')
            raw=item['text'].encode('utf-8') if fresh else compiler.confined(source_root,item['source']).read_bytes()
            if not fresh:require(digest_bytes(raw)==item['sha256'],'Frozen source changed mid-run')
            source=sources/relative;source.parent.mkdir(parents=True,exist_ok=True);source.write_bytes(raw)
            source_record=record_file(source)
            validate_all()
            parse_log=logs/(name.replace('.','_')+'.imports.json')
            header=parse_header(ctx['lean'],source,env,expected_header(item['imports']),parse_log)
            arts={n:[[str(inputs/compiler.module_file(n))],[]] for n in public}
            arts.update(external)
            setup=dict(name=name,isModule=True,package=None,plugins=[],dynlibs=[],options={},importArts=arts)
            setup_path=setups/(name.replace('.','_')+'.json');compiler.atomic_json(setup_path,setup)
            validate_setup(setup_path,setup);setup_record=record_file(setup_path)
            log=logs/(name.replace('.','_')+'.log')
            temporary=temp/(str(index)+'.olean')
            command=[str(ctx['lean']),'--setup',str(setup_path),'-j','1','-M',str(memory_mb),
                     '-o',str(temporary),str(relative)]
            started=time.monotonic();code=None;termination='completed'
            with log.open('wb') as stream:
                child=subprocess.Popen(command,cwd=sources,env=env,stdout=stream,stderr=subprocess.STDOUT,
                    creationflags=subprocess.CREATE_NO_WINDOW if os.name=='nt' else 0)
                compiler.atomic_json(output/'owned_child.json',dict(pid=child.pid,module=name,command=command))
                try:code=child.wait(timeout=seconds)
                except subprocess.TimeoutExpired:termination='wall_limit';code=stop_child(child)
                except BaseException:stop_child(child);raise
            row=dict(name=name,exit_code=code,termination=termination,wall_seconds=time.monotonic()-started,
                source_sha256=source_record['sha256'],source_record=source_record,
                setup=str(setup_path),setup_record=setup_record,log=str(log),log_record=record_file(log),
                parsed_header=header,parsed_header_sha256=compiler.digest(parse_log),
                parsed_header_log=str(parse_log),parsed_header_record=record_file(parse_log),
                public_input_hashes={k:v for k,v in public.items()},setup_sha256=setup_record['sha256'])
            contents=log.read_text(encoding='utf-8',errors='replace')
            if code!=0 or termination!='completed' or 'error:' in contents or 'warning:' in contents:
                report['failed_module']=row;save();raise RuntimeError('Lean did not pass: '+name)
            if fresh:require(item['marker'] in contents,'Fresh audit marker absent')
            check_file(source,source_record);check_file(setup_path,setup_record);validate_setup(setup_path,setup)
            validate_all()
            row['artifacts']=compiler.bundle(temporary)
            require(set(row['artifacts'])==set(compiler.SIDE),'Expected full public/private/server output bundle')
            target=checked/compiler.module_file(name);target.parent.mkdir(parents=True,exist_ok=True)
            for suffix,expected in row['artifacts'].items():
                dst=Path(str(target)+suffix);Path(str(temporary)+suffix).replace(dst);check_file(dst,expected)
            produced[name]=row
            if fresh:report['fresh_audit']=row
            else:
                public_target=inputs/compiler.module_file(name);public_target.parent.mkdir(parents=True,exist_ok=True)
                public_target.write_bytes(target.read_bytes());public[name]=row['artifacts']['']
                report['modules'].append(row)
            save();print('MODULE',name,'EXIT 0',flush=True)
        validate_all();base_final_check(ctx)
        report.update(status='checked',supplementary_modules_checked=len(modules),
            fresh_public_only_audit_checked=True,full_certificate_proved=False,full_path_instances_checked=False)
        save();return report
    except BaseException as error:
        report.update(status='failed',error_type=type(error).__name__,error=str(error))
        save();raise

def load_package_verifier(package):
    path=package/'final_sources/tools/prepare_final_source_package.py'
    require(compiler.digest(path)==VERIFIER_SHA,'Wrong frozen package verifier')
    module=types.ModuleType('frozen_final_package_verifier');module.__file__=str(path)
    exec(compile(path.read_bytes(),str(path),'exec'),module.__dict__)
    return module

def compile_supplement(args):
    manifest=args.supplement_manifest.resolve();package=manifest.parent
    require(compiler.digest(manifest)==MANIFEST_SHA,'Wrong frozen final48 manifest')
    verifier=load_package_verifier(package)
    report=verifier.verify_package(package,args.core_inventory.parent)
    original_inventory=args.core_inventory.read_bytes()
    require(digest_bytes(original_inventory)==report['core_inventory_sha256'],'Wrong core inventory')
    ctx=base_context(args.base_args,args.base_lock,args.expected_base_lock_sha256)
    core_names=[r['name'] for r in report['reused_core_modules']]
    names_in_base={n for n in ctx['primary'] if n.startswith('SolitonClassification.')}
    allowed=set(core_names)|{'SolitonClassification.Rotating.ModuleFullGenericAudit'}
    require(names_in_base==allowed,'Captured generic base is not exactly the expected core88')
    require('generic' in ctx['roots'],'Captured generic root label is absent')
    generic_names={key.split('/',1)[1][:-6].replace('/','.') for key in ctx['lock']['files']
                   if key.startswith('generic/') and key.endswith('.olean')}
    require(generic_names==allowed and all(ctx['primary'][n][2]=='generic' for n in allowed),
            'Generic root has extra modules or is shadowed')
    original_package_hash=compiler.digest(manifest)
    def checkpoint():
        require(compiler.digest(manifest)==original_package_hash,'Supplement manifest changed')
        require(args.core_inventory.read_bytes()==original_inventory,'Core inventory changed')
        verifier.verify_package(package,args.core_inventory.parent)
    name='SolitonClassification.Rotating.FinalSupplementFreshAudit'
    main='SolitonClassification.Rotating.FullPathFinalGeometry'
    audit=dict(name=name,imports=[main],marker='FINAL_SUPPLEMENT_CONDITIONAL_AUDIT 2205',text=f'''module
public import {main}
#check {main}.exists_geometry_of_two_blocks
#print axioms {main}.exists_geometry_of_two_blocks
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (←getEnv).constants do
    let userName := privateToUserName name
    if (`SolitonClassification.Rotating).isPrefixOf userName || (`ClosedSimilarity).isPrefixOf userName then
      for ax in (←collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom: {{name}} depends on {{ax}}"
      count := count + 1
  unless count == 2205 do throwError "Unexpected imported declaration count: {{count}}"
  logInfo "FINAL_SUPPLEMENT_CONDITIONAL_AUDIT 2205"
''')
    result=run_batch(ctx,package,report['topological_modules'],core_names,'SolitonClassification',
        args.output,audit,args.seconds,args.memory_mb,args.setup_extra,checkpoint,args.setup_extra_source)
    result.update(supplement_manifest_sha256=MANIFEST_SHA,core_inventory_sha256=report['core_inventory_sha256'],
                  conditional_geometry_audit_count=2205)
    compiler.atomic_json(args.output.resolve()/'compile_report.json',result)
    return result

def positive(value):
    x=int(value)
    if x<=0:raise argparse.ArgumentTypeError('Expected a positive integer')
    return x
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--supplement-manifest',type=Path,required=True)
    p.add_argument('--core-inventory',type=Path,required=True)
    p.add_argument('--base-lock',type=Path,required=True);p.add_argument('--base-args',type=Path,required=True)
    p.add_argument('--expected-base-lock-sha256',required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--seconds',type=positive,default=600);p.add_argument('--memory-mb',type=positive,default=8192)
    p.add_argument('--setup-extra',action='append',default=[],help='Allowlisted local Arctan only; all layers come from one locked origin')
    p.add_argument('--setup-extra-source',type=Path,help='Exact upstream Arctan source, SHA256 pinned by this runner')
    a=p.parse_args();result=compile_supplement(a)
    print(json.dumps({k:result[k] for k in ['status','supplementary_modules_checked',
        'conditional_geometry_audit_count','full_certificate_proved']}))
if __name__=='__main__':main()
