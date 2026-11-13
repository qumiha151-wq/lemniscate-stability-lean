"""Pinned production entry and stdlib-only package verifier. No deployment data."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,importlib,json,os,re,shutil,stat,subprocess,sys

FROZEN_RUNTIME = {
  "plan_production_grid.py": "61ea4ae11174cffa51dd5b4fc3c1caba05838b54b05d14c4793f4846ca864cca",
  "production_artifact.py": "ddb448165391a04ab1ffcd9e4b572f9945f29fab5e1fa6ec981adad4b56323b5",
  "production_bulk_origin.py": "de7b32db9c8f2ebea7fc4b1cc7786ea6ba44c807c91a18b989033eb62bce5468",
  "production_compile_shard.py": "f0abd2db3d6b8db32707d33e8ebb8a6aaee7da0c6f2332c9c4da8e931c64310b",
  "production_core_artifact.py": "1ead0d5ced187dbf2d9847f7b08ea7f7a1e8931fe88ce8461c284fa277c73ea6",
  "production_core_release_publisher.py": "c063b963b402cdce9354caac5451b6bf686ea2297a962e049649e97db2826eed",
  "production_core_release_request.py": "3cd4eb7e08f9e5e7d61a373d31aee03ac1bdd5eec3c1b67254ae925fbc2fe210",
  "production_public_projection.py": "b206b8a43a3e1b9a47a31ab33b038ca2ac351a461b810d9265f183019c56708d",
  "production_release_preflight.py": "624df2b5af0c8350bdaeba353b811ae60de9ed17558eeff792da17cd0ff1cf2f",
  "production_release_url_protocol.py": "aaa1f9fbaa1b5b7e3ca12890638abdce4a25d28eb3b992889efa45e8157b1f7d",
  "production_shard_prewrite_budget.py": "b44da9709ae548af4caa419cf54601f76a5f663a986cfa96e55992c72a5c37b5",
  "production_shard_release_controller.py": "50aa90f43c54a3c9404d6611c9970cda3f1ea7a1f50b335fa8c6ce6972fda30e",
  "production_shard_release_publisher_v2.py": "cba63be08c987643a1bbf86aeb5793171667b433dc2a4bbacd962817fdf90b38",
  "production_shard_release_publisher_v3.py": "6aac21ed2412c200d1db0638c45b42ac1588e2b440c4f415867ee9e4742f49e4",
  "production_shard_zip_download.py": "8e9905c801cf08d4f4697b2fabae3b22ee5c4dfed28267d7b1f0dc2eb7e30f65",
  "propose_grid42x22.py": "dcd5024d5d182763cf91ca552080065dbe7dab6cec18bb1f49f7b07a5911c183",
  "reference.py": "e586dcd92c56567232ce7751765eec5a55377d1e7f6398291606d674aa5568b4",
  "stage_public_archives.py": "44f7407c525d4882b2efde128eed23477e06d5e94dbef06673743476e6d4cbb9"
}
SCHEMA='rotating.shard-release-v3-tools.v1'
SHA=re.compile('[0-9a-f]{64}')
REV=re.compile('[0-9a-f]{40}')
MANIFEST_LIMIT=2*1024**2
PACKAGE_LIMIT=64*1024**2
TEXT_LIMIT=32*1024**2


def require(ok,message):
    if not ok:raise ValueError(message)


def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1024**2),b''):h.update(block)
    return h.hexdigest()


def strict(raw):
    def pairs(rows):
        out={}
        for k,v in rows:
            require(k not in out,'Duplicate JSON key');out[k]=v
        return out
    return json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda x:(_ for _ in ()).throw(ValueError('Nonfinite JSON')))


def safe_relative(name):
    require(isinstance(name,str) and re.fullmatch('[A-Za-z0-9_./-]+',name)
        and not name.startswith('/') and all(x not in ('','.','..') for x in name.split('/')),'Unsafe relative path')
    return PurePosixPath(name)


def ordinary(path,kind):
    require(not path.is_symlink() and not getattr(path,'is_junction',lambda:False)(),'Link in package/evidence')
    mode=path.stat().st_mode
    require(stat.S_ISREG(mode) if kind=='file' else stat.S_ISDIR(mode),'Nonordinary path')
    return path


def git(root,*args):
    env=os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):env.pop(key)
    return subprocess.run(['git','-C',str(root),*args],env=env,check=True,
        stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30).stdout


def verify_package(package_root,manifest_sha256,expected_revision=None,require_committed=False):
    root=ordinary(Path(package_root),'dir').resolve();manifest=root/'package_manifest.json'
    require(SHA.fullmatch(manifest_sha256) and ordinary(manifest,'file').stat().st_size<=MANIFEST_LIMIT
        and digest(manifest)==manifest_sha256,'Wrong bounded package manifest')
    data=strict(manifest.read_bytes())
    require(set(data)=={'schema','runtime_helper_sha256','launcher_path','files','status',
        'full_certificate_proved','deployment_YAML_generated','production_catalog_generated'}
        and data['schema']==SCHEMA and data['status']=='local_checked_not_deployed'
        and data['runtime_helper_sha256']==FROZEN_RUNTIME and data['launcher_path']=='launcher/launch.py'
        and all(data[k] is False for k in ('full_certificate_proved','deployment_YAML_generated','production_catalog_generated')),
        'Wrong fixed package schema/scope')
    rows=data['files'];require(isinstance(rows,list) and 20<=len(rows)<=512,'Wrong package member count')
    expected={};folded={};total=0;runtime={}
    for row in rows:
        require(set(row)=={'path','bytes','sha256','role'},'Wrong package member fields')
        name=row['path'];rel=safe_relative(name)
        require(name!='package_manifest.json' and name not in expected,'Manifest self/duplicate entry')
        require(type(row['bytes']) is int and 0<=row['bytes']<=16*1024**2
            and isinstance(row['sha256'],str) and SHA.fullmatch(row['sha256']),'Invalid package member identity')
        role=('runtime' if name.startswith('runtime/') else 'launcher' if name=='launcher/launch.py'
            else 'readme' if name=='README.txt' else 'evidence' if name.startswith('evidence/') else None)
        require(role is not None and row['role']==role,'Unapproved package member role')
        if role=='runtime':
            require(len(rel.parts)==2 and rel.name in FROZEN_RUNTIME and row['sha256']==FROZEN_RUNTIME[rel.name],
                'Unexpected/changed runtime helper');runtime[rel.name]=row['sha256']
        for n in range(1,len(rel.parts)+1):
            part='/'.join(rel.parts[:n]);key=part.casefold()
            require(key not in folded or folded[key]==part,'Casefold package path collision');folded[key]=part
        path=root.joinpath(*rel.parts);ordinary(path,'file')
        require(path.stat().st_size==row['bytes'] and digest(path)==row['sha256'],'Package file bytes differ')
        total+=row['bytes'];expected[name]=row
    require(runtime==FROZEN_RUNTIME and total<=PACKAGE_LIMIT and 'launcher/launch.py' in expected
        and 'README.txt' in expected,'Incomplete/oversized package')
    require([x['path'] for x in rows]==sorted(expected),'Noncanonical package file order')
    allowed_dirs={root}
    for name in expected:
        at=(root/name).parent
        while at!=root:allowed_dirs.add(at);at=at.parent
    actual=set()
    for path in root.rglob('*'):
        if path.is_file():ordinary(path,'file');actual.add(path.relative_to(root).as_posix())
        else:ordinary(path,'dir');require(path in allowed_dirs,'Extra package directory')
    require(actual==set(expected)|{'package_manifest.json'},'Extra/missing package file')
    identity=None
    if require_committed:
        require(isinstance(expected_revision,str) and REV.fullmatch(expected_revision),'Missing expected tool P')
        top=ordinary(Path(git(root,'rev-parse','--show-toplevel').decode().strip()),'dir').resolve()
        require(root.is_relative_to(top) and git(root,'rev-parse','HEAD').decode().strip()==expected_revision,'Wrong actual tool P')
        for name in [*expected,'package_manifest.json']:
            path=root/name
            require(git(top,'show','HEAD:'+path.relative_to(top).as_posix())==path.read_bytes(),'Package is not its committed P blob')
        require(git(root,'rev-parse','HEAD').decode().strip()==expected_revision,'Tool P changed during verification')
        identity=expected_revision
    return {'root':root,'manifest':data,'manifest_sha256':manifest_sha256,
        'files':expected,'bytes':total,'actual_committed_revision':identity}


def isolated_import(package):
    require(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode,'Use Python -I -S -B')
    roots={Path(sys.base_prefix).resolve(),Path(sys.base_exec_prefix).resolve()}
    for value in sys.path:
        require(value and Path(value).is_absolute() and any(Path(value).resolve().is_relative_to(x) for x in roots)
            and 'site-packages' not in Path(value).parts,'Unexpected pre-runtime import path')
    require(not any(Path(name).stem in sys.modules for name in FROZEN_RUNTIME),'Runtime module loaded before verification')
    runtime=ordinary(package['root']/'runtime','dir').resolve();sys.path.insert(0,str(runtime))
    controller=importlib.import_module('production_shard_release_controller')
    check_imports(package,controller)
    require(controller.checked_tools()==package['actual_committed_revision'],'Imported tool revision differs')
    return controller


def check_imports(package,controller):
    runtime=package['root']/'runtime'
    require(controller.helpers()==FROZEN_RUNTIME,'Imported helper identities differ')
    for name,wanted in FROZEN_RUNTIME.items():
        module=sys.modules.get(Path(name).stem)
        require(module is not None and getattr(module,'__file__',None),'Missing imported runtime helper')
        path=Path(module.__file__).resolve()
        require(path==runtime/name and digest(ordinary(path,'file'))==wanted,'Runtime import escaped exact package')


def write_new(path,value):
    raw=(json.dumps(value,sort_keys=True,indent=2)+'\n').encode()
    with path.open('xb') as f:f.write(raw);f.flush();os.fsync(f.fileno())
    if os.name=='posix':
        fd=os.open(path.parent,os.O_RDONLY|getattr(os,'O_DIRECTORY',0))
        try:os.fsync(fd)
        finally:os.close(fd)


def evidence(controller,ctx,package,destination,success):
    """No network or original-body copy. Failure collection is evidence only."""
    require(not destination.exists(),'Evidence destination exists');destination.mkdir(parents=True)
    copies=destination/'files';copies.mkdir();source_root=ctx['output'];snapshot=controller.inventory(source_root)
    expected=None
    if success:
        receipt=strict((source_root/'receipt.json').read_bytes())
        require(receipt['status']=='checked' and receipt['test_fixture'] is False
            and receipt['helper_sha256']==FROZEN_RUNTIME,'Controller did not return a real checked result')
        table_path=source_root/'checked_files.json';require(digest(table_path)==receipt['inventory_sha256'],'Wrong controller inventory')
        expected=strict(table_path.read_bytes())
        for name in ('checked_files.json','receipt.json'):
            path=source_root/name;expected[name]={'sha256':digest(path),'bytes':path.stat().st_size}
        require(snapshot==expected,'Controller evidence differs after completion')
    selected={};excluded={};total=0
    # Paths come from the actual controller inventory; body exclusions are the
    # two exact directories owned by the frozen outer prepare implementation.
    for name,row in snapshot.items():
        safe_relative(name)
        if name.startswith(('download/zips/','download/archives/')):
            excluded[name]=row;continue
        require(name.endswith('.json'),'Unexpected non-JSON compact stage evidence')
        require(name.startswith(('controller/','download/inputs/','download/evidence/','download/journal/',
            'publication/','release_journal/')) or name in ('download/receipt.json','failure_inventory.json','checked_files.json','receipt.json'),
            'Unexpected compact evidence location')
        selected['controller/'+name]=(source_root/name,row)
    input_root=ctx['input_checkout']
    for path,wanted in ctx['pins'].items():
        require(path.resolve().is_relative_to(input_root),'Input evidence outside Q checkout')
        name='inputs/'+path.resolve().relative_to(input_root).as_posix();safe_relative(name)
        require(digest(ordinary(path,'file'))==wanted,'Input changed before evidence copy')
        selected[name]=(path,{'sha256':wanted,'bytes':path.stat().st_size})
    mpath=package['root']/'package_manifest.json'
    selected['package_manifest.json']=(mpath,{'sha256':package['manifest_sha256'],'bytes':mpath.stat().st_size})
    require(shutil.disk_usage(destination).free>=TEXT_LIMIT+16*1024**2,'Insufficient compact evidence disk floor')
    table={}
    for name,(source,row) in selected.items():
        require(row['bytes']<=16*1024**2 and total+row['bytes']<=TEXT_LIMIT,'Compact evidence size cap')
        target=copies.joinpath(*safe_relative(name).parts);target.parent.mkdir(parents=True,exist_ok=True)
        raw=ordinary(source,'file').read_bytes()
        require(len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256'],'Evidence source changed')
        with target.open('xb') as f:f.write(raw)
        total+=len(raw);table[name]=row
    for name,(source,row) in selected.items():
        require(digest(ordinary(source,'file'))==row['sha256'] and digest(copies/name)==row['sha256'],'Evidence changed after copying')
    recovery=[]
    for job in ctx['request']['jobs']:
        path=source_root/'download/archives'/job['archive']
        if path.exists():
            ordinary(path,'file');require(path.resolve().is_relative_to(source_root.resolve()),'Recovery path escape')
            size=path.stat().st_size;sha=digest(path)
            recovery.append({'key':job['key'],'original_path':str(path.resolve()),'observed_bytes':size,'observed_sha256':sha,
                'matches_pinned_raw_archive':size==job['archive_bytes'] and sha==job['archive_sha256'],
                'source_copy_performed':False,'numerical_proof_claimed_here':False})
    write_new(destination/'inventory.json',{'schema':'rotating.launcher-compact-evidence.v1',
        'status':'checked_controller_evidence' if success else 'observed_failure_evidence',
        'files':table,'excluded_original_bodies':excluded,'source_originals_deleted':False,'actual_network_requests':0})
    write_new(destination/'recovery_original_paths.json',{'schema':'rotating.recovery-original-paths.v1','files':recovery,
        'use_on_failure_only':True,'automatic_remote_recovery':False,'full_certificate_proved':False})
    return {'inventory_sha256':digest(destination/'inventory.json'),'recovery_paths_sha256':digest(destination/'recovery_original_paths.json'),
        'compact_bytes':total,'compact_files':len(table),'originals_copied':0}


def main(argv=None):
    ap=argparse.ArgumentParser()
    ap.add_argument('--package-root',type=Path,required=True);ap.add_argument('--manifest-sha256',required=True)
    ap.add_argument('--expected-tools-revision',required=True)
    mode=ap.add_mutually_exclusive_group(required=True);mode.add_argument('--verify-package-only',action='store_true');mode.add_argument('--execute',action='store_true')
    ap.add_argument('--input-checkout',type=Path);ap.add_argument('--request');ap.add_argument('--request-sha256')
    ap.add_argument('--plan');ap.add_argument('--plan-sha256');ap.add_argument('--catalog');ap.add_argument('--catalog-sha256')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args(argv)
    require(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode,'Use Python -I -S -B')
    package=verify_package(args.package_root,args.manifest_sha256,args.expected_tools_revision,True)
    require(Path(__file__).resolve()==package['root']/'launcher/launch.py','Launcher is not its verified package member')
    controller=isolated_import(package)
    if args.verify_package_only:
        verify_package(args.package_root,args.manifest_sha256,args.expected_tools_revision,True);check_imports(package,controller)
        print(json.dumps({'status':'package_and_isolated_import_checked','tool_revision':args.expected_tools_revision,
            'manifest_sha256':args.manifest_sha256,'runtime_helpers':len(FROZEN_RUNTIME),'actual_network_requests':0}));return
    require(args.input_checkout and args.output and all(getattr(args,k) for k in ('request','request_sha256','plan','plan_sha256','catalog','catalog_sha256')),
        'Missing immutable production inputs')
    input_root=ordinary(args.input_checkout,'dir').resolve()
    paths={name:input_root.joinpath(*safe_relative(getattr(args,name)).parts) for name in ('request','plan','catalog')}
    out=args.output.resolve();require(not out.exists() and not out.is_relative_to(package['root'])
        and not out.is_relative_to(input_root) and not input_root.is_relative_to(out),'Unsafe/fresh output required')
    token=os.environ.get('GH_TOKEN');require(isinstance(token,str) and token,'Publisher token must come from GH_TOKEN environment')
    ctx=controller.prepare(request=paths['request'],request_sha256=args.request_sha256,plan=paths['plan'],plan_sha256=args.plan_sha256,
        catalog=paths['catalog'],catalog_sha256=args.catalog_sha256,output=out/'controller_run',
        helper_sha256=FROZEN_RUNTIME,input_checkout=input_root)
    controller.recheck(ctx,dict(os.environ));out.mkdir(parents=True)
    write_new(out/'started.json',{'schema':'rotating.launcher-started.v1','tool_revision':args.expected_tools_revision,
        'observed_workflow_revision':os.environ.get('GITHUB_SHA'),'manifest_sha256':args.manifest_sha256,
        'request_sha256':args.request_sha256,'plan_sha256':args.plan_sha256,'catalog_sha256':args.catalog_sha256,
        'token_recorded':False,'full_certificate_proved':False,'independent_external_Q_pin_performed_here':False})
    result=None
    try:
        result=controller.execute(ctx,token=token)
        verify_package(args.package_root,args.manifest_sha256,args.expected_tools_revision,True);check_imports(package,controller)
        copied=evidence(controller,ctx,package,out/'compact_evidence',True)
        controller.recheck(ctx,dict(os.environ))
        verify_package(args.package_root,args.manifest_sha256,args.expected_tools_revision,True);check_imports(package,controller)
        write_new(out/'receipt.json',{'schema':'rotating.launcher-result.v1','status':'checked','controller_receipt_sha256':digest(ctx['output']/'receipt.json'),
            **copied,'tool_revision':args.expected_tools_revision,'observed_workflow_revision':os.environ.get('GITHUB_SHA'),
            'manifest_sha256':args.manifest_sha256,'full_certificate_proved':False,'actual_Lean_calls':0})
        print(json.dumps({'status':'checked','receipt_sha256':digest(out/'receipt.json')}))
    except Exception as error:
        status={'schema':'rotating.launcher-failure.v1','status':'failed','exception_type':type(error).__name__,
            'controller_returned':result is not None,'remote_writes_not_inferred':True,'automatic_retry':False,
            'remote_cleanup':False,'source_originals_deleted':False,'full_certificate_proved':False}
        try:
            verify_package(args.package_root,args.manifest_sha256,args.expected_tools_revision,True);check_imports(package,controller)
            if not (out/'compact_evidence').exists():status['evidence']=evidence(controller,ctx,package,out/'compact_evidence',False)
            else:status['compact_evidence_already_present']=True
        except Exception as collecting_error:status['evidence_incomplete_exception_type']=type(collecting_error).__name__
        try:write_new(out/'failure.json',status)
        except Exception:pass
        raise


if __name__=='__main__':
    try:main()
    except Exception as error:
        print(json.dumps({'status':'failed','exception_type':type(error).__name__,'details_intentionally_omitted':True}),file=sys.stderr)
        raise SystemExit(1)

