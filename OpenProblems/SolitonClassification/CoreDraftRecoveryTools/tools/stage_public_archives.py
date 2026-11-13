"""Validate complete archives sequentially and retain only public Lean inputs.

Original archives are never deleted. A temporary expansion is removed only
after full validation (and after an explicit resolved-path containment check).
This prepares inputs; it does not assert new Lean checks or permanent storage.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil
import production_compile_shard as compiler
import production_artifact as artifact
import plan_production_grid as trajectory

PREFIX='SolitonClassification.Rotating.'
FIELDS=['candidate_id','candidate_hash','orders','mesh','step','generator_sha256']

def digest_bytes(data):return hashlib.sha256(data).hexdigest()

def expected_modules(key):
    names=[];blocks=[]
    for b in range(4):
        names.append(PREFIX+f'{key}B{b:02d}Nodes')
        names += [PREFIX+f'{key}L{j:04d}' for j in range(8*b,8*b+8)]
        root=PREFIX+f'{key}B{b:02d}Block';names.append(root);blocks.append(root)
    level=0
    while len(blocks)>1:
        next_level=[]
        for i in range(0,len(blocks),2):
            seam=PREFIX+f'{key}Seam{level}_{i//2}';join=PREFIX+f'{key}Join{level}_{i//2}'
            names += [seam,join];next_level.append(join)
        blocks=next_level;level+=1
    names.append(PREFIX+key+'Audit')
    return names,blocks[0]

def validate_plan(plan, trajectory_path=None):
    if plan.get('schema')!='rotating.public-assembly-plan.v1' or plan.get('mode') not in ['pilot','full']:
        raise ValueError('Wrong assembly registry schema/mode')
    if not isinstance(plan['revision'],str) or not plan['revision'] or '\n' in plan['revision']:
        raise ValueError('Invalid pinned revision')
    if plan['candidate_id']!='nonzero_rotation_minus56_over57':raise ValueError('Unexpected candidate')
    if plan['mode']=='full' and not re.fullmatch(r'[0-9a-f]{40}',plan['revision']):
        raise ValueError('Full production requires an exact Git revision, not a worktree label')
    for name in ['base_lock_sha256','candidate_hash','generator_sha256']:
        if not compiler.SHA.fullmatch(plan[name]):raise ValueError('Invalid registry hash: '+name)
    if plan['orders']!={'state':42,'matrix':22} or plan['mesh']!=str(10**60):
        raise ValueError('Wrong fixed orders/mesh')
    if int(plan['step']['num'])<=0 or int(plan['step']['den'])<=0:raise ValueError('Invalid step')
    jobs=plan['jobs'];keys=set();archives=set();modules=set();folded_modules=set()
    for job in jobs:
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',job['key']) or job['key'].casefold() in keys:
            raise ValueError('Invalid/duplicate job namespace')
        if (type(job['sign']) is not int or job['sign'] not in [-1,1]
                or type(job['start']) is not int or job['start']<0 or job['start']+32>4000
                or type(job['count']) is not int or job['count']!=32):
            raise ValueError('Wrong signed shard coverage')
        if not compiler.SHA.fullmatch(job['archive_sha256']):raise ValueError('Invalid archive hash')
        if job['archive'].casefold() in archives:raise ValueError('Archive reused for another job')
        if job['input_node_sha256'] is not None and not compiler.SHA.fullmatch(job['input_node_sha256']):
            raise ValueError('Invalid input checkpoint hash')
        names,_=expected_modules(job['key'])
        folded={n.casefold() for n in names}
        if folded_modules.intersection(folded):raise ValueError('Duplicate public primary module')
        modules.update(names);folded_modules.update(folded);keys.add(job['key'].casefold());archives.add(job['archive'].casefold())
    source_plan=None
    if plan['mode']=='pilot':
        if len(jobs)!=1 or (jobs[0]['sign'],jobs[0]['start'],jobs[0]['count'])!=(1,0,32):
            raise ValueError('Pilot registry covers exactly the initial positive32 shard')
        if trajectory_path is not None:raise ValueError('Pilot must not masquerade as a complete trajectory plan')
        if not compiler.SHA.fullmatch(jobs[0]['output_node_sha256']):raise ValueError('Missing pilot endpoint binding')
    else:
        if trajectory_path is None:raise ValueError('Full registry requires its pinned original trajectory plan')
        if compiler.digest(trajectory_path)!=plan['trajectory_plan_sha256']:
            raise ValueError('Trajectory plan hash mismatch')
        source_plan=json.loads(trajectory_path.read_text(encoding='utf-8-sig'))
        trajectory.validate_plan(source_plan,trajectory_path.resolve().parent)
        if (source_plan['steps_per_sign']!=4000 or source_plan['shard_size']!=32
                or len(jobs)!=250 or len(source_plan['jobs'])!=250
                or plan['revision']!=source_plan['revision']):
            raise ValueError('Incomplete full coverage or different revision')
        for field in ['candidate_id','candidate_hash','orders','mesh','step']:
            if plan[field]!=source_plan[field]:raise ValueError('Trajectory identity differs: '+field)
        if plan['generator_sha256']!=source_plan['source_fingerprints']['shard_generator']['sha256']:
            raise ValueError('Generator identity differs')
        for job,expected in zip(jobs,source_plan['jobs']):
            for field in ['key','sign','start','count','input_node_sha256']:
                if job[field]!=expected[field]:raise ValueError('Full coverage/order/input binding differs')
    return source_plan,modules

def public_tree_check(root, records):
    actual=set()
    for path in root.rglob('*'):
        if path.is_symlink():raise ValueError('Symlink in public input tree')
        if path.is_file():actual.add(path.relative_to(root).as_posix())
    if actual!={compiler.module_file(n) for n in records}:raise ValueError('Unexpected/private public input file')
    for name,data in records.items():
        path=root/compiler.module_file(name)
        if path.stat().st_size!=data['bytes'] or compiler.digest(path)!=data['sha256']:
            raise ValueError('Public copy changed')

def prepare(args):
    plan_bytes=args.plan.read_bytes();plan=json.loads(plan_bytes.decode('utf-8-sig'))
    source_plan,generated_names=validate_plan(plan,args.trajectory_plan)
    lock_bytes=args.base_lock.read_bytes();lock=json.loads(lock_bytes.decode('utf-8-sig'))
    if digest_bytes(lock_bytes)!=plan['base_lock_sha256']:raise ValueError('Different base lock')
    argument_bytes=args.base_args.read_bytes();common=json.loads(argument_bytes.decode('utf-8-sig'))
    if not isinstance(common,list) or any(not isinstance(x,str) for x in common):
        raise ValueError('Base arguments must be a JSON array of strings')
    ap=argparse.ArgumentParser(add_help=False);ap.add_argument('--lean',required=True)
    ap.add_argument('--base-root',action='append',required=True)
    base=ap.parse_args(common);roots=compiler.roots_from_args(base.base_root)
    _,identity=compiler.lean_identity(base.lean)
    if identity!=lock['lean'] or list(roots)!=lock['root_order']:raise ValueError('Different actual compiler/root order')
    if 'generic' not in roots:raise ValueError('Missing isolated generic root')
    for label,root in roots.items():
        if label!='generic' and ((root/'SolitonClassification').exists() or (root/'SolitonClassification.olean').exists()):
            raise ValueError('External root shadows the project namespace')
    output=args.output.resolve();archive_root=args.archive_root.resolve()
    if output.exists() and any(output.iterdir()):raise ValueError('Fresh output directory required')
    for source in [archive_root,*roots.values()]:
        if output.is_relative_to(source) or source.is_relative_to(output):
            raise ValueError('Output must be disjoint from archives and locked libraries')
    helpers={str(Path(p).resolve()):compiler.digest(p) for p in [__file__,compiler.__file__,artifact.__file__,trajectory.__file__]}
    output.mkdir(parents=True,exist_ok=True);args.owned_output=output
    public=output/'public_inputs';metadata=output/'metadata';scratch_root=output/'scratch'
    metadata.mkdir();scratch_root.mkdir();public.mkdir()
    (metadata/'plan.json').write_bytes(plan_bytes);(metadata/'base_lock.json').write_bytes(lock_bytes)
    (metadata/'base_args.json').write_bytes(argument_bytes)
    copies={};folded_copies=set();receipts=[]
    def copy_primary(name,path,expected,origin):
        if name.casefold() in folded_copies:raise ValueError('Duplicate/namespace-shadowing primary olean: '+name)
        data=path.read_bytes()
        if digest_bytes(data)!=expected['sha256'] or len(data)!=expected['bytes']:
            raise ValueError('Primary bytes changed before copy')
        target=public/compiler.module_file(name);target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(data);copies[name]={'path':str(target),'sha256':expected['sha256'],
                                             'bytes':len(data),'origin':origin}
        folded_copies.add(name.casefold())
    for path,expected in lock['files'].items():
        label,relative=path.split('/',1)
        if label=='generic' and relative.endswith('.olean'):
            name=relative[:-6].replace('/','.')
            if not name.startswith(PREFIX) or name.casefold() in {n.casefold() for n in generated_names}:
                raise ValueError('Generic/shard namespace collision')
            copy_primary(name,compiler.confined(roots[label],relative),expected,'generic')
    if not copies:raise ValueError('No locked generic public inputs')
    status={'schema':'rotating.public-archive-stage.v1','status':'running',
      'plan_sha256':digest_bytes(plan_bytes),'base_lock_sha256':digest_bytes(lock_bytes),
      'base_args_sha256':digest_bytes(argument_bytes),'revision':plan['revision'],'mode':plan['mode'],
      'helper_sha256':helpers,'receipts':receipts,'public_inputs':copies,
      'full_plan_coverage_verified':False,'lean_reimport_checked':False,'full_certificate_proved':False,
      'external_library_snapshot_checked':False,'durable_remote_archival_storage_verified':False}
    compiler.atomic_json(output/'public_index.json',status)
    for number,job in enumerate(plan['jobs']):
        archive=compiler.confined(archive_root,job['archive'])
        if archive.is_symlink() or compiler.digest(archive)!=job['archive_sha256']:
            raise ValueError('Archive bytes differ from pinned registry')
        stage=compiler.confined(scratch_root,job['key'])
        if stage.exists():raise ValueError('Scratch stage already exists')
        try:
            artifact.unpack(archive,stage,plan['revision'],args.max_unpacked_mb*1024*1024)
            read=lambda name:compiler.confined(stage,name).read_bytes()
            manifest,report,_,_=artifact.validate_bundle(read)
            if read('base_lock.json')!=lock_bytes:raise ValueError('Archive belongs to another exact base')
            if report['compiler_sha256']!=helpers[str(Path(compiler.__file__).resolve())]:
                raise ValueError('Archive was checked by another compiler-wrapper version')
            for field in FIELDS:
                if manifest[field]!=plan[field]:raise ValueError('Archive candidate/tool identity differs: '+field)
            for field in ['key','sign','start','count','input_node_sha256']:
                if manifest[field]!=job[field]:raise ValueError('Archive job/checkpoint identity differs: '+field)
            names,root=expected_modules(job['key'])
            if ([m['name'] for m in manifest['modules']]!=names or manifest.get('module_system') is not True
                    or manifest['root_module']!=root or manifest['audit_module']!=names[-1]
                    or manifest['checked_constant']!=root+'.certificate'):
                raise ValueError('Unexpected public module set/interface')
            expected_coverage=[{'global_step':job['start']+i,'state_module':PREFIX+f'{job["key"]}L{i:04d}',
              'matrix_module':PREFIX+f'{job["key"]}L{i:04d}',
              'header_module':PREFIX+f'{job["key"]}B{i//8:02d}Nodes'} for i in range(32)]
            if manifest['leaf_coverage']!=expected_coverage:raise ValueError('Wrong numerical leaf coverage')
            endpoint_bytes=read('output_node.json');endpoint=json.loads(endpoint_bytes)
            if plan['mode']=='pilot':
                if digest_bytes(endpoint_bytes)!=job['output_node_sha256']:raise ValueError('Pilot endpoint changed')
                checkpoint_hash=job['output_node_sha256']
            else:
                trajectory_job=source_plan['jobs'][number]
                checkpoint=compiler.confined(args.trajectory_plan.resolve().parent,trajectory_job['output_node'])
                checkpoint_hash=trajectory_job['output_node_sha256']
                if compiler.digest(checkpoint)!=checkpoint_hash or json.loads(checkpoint.read_bytes())!=endpoint:
                    raise ValueError('Archive endpoint disagrees with the pinned trajectory checkpoint')
            if endpoint['index']!=job['start']+32 or endpoint['sign']!=job['sign']:
                raise ValueError('Wrong terminal checkpoint index/sign')
            for field in ['candidate_hash','orders','mesh','step']:
                if endpoint[field]!=plan[field]:raise ValueError('Terminal checkpoint identity differs: '+field)
            evidence=metadata/job['key'];evidence.mkdir()
            (evidence/'manifest.json').write_bytes(read('manifest.json'))
            (evidence/'output_node.json').write_bytes(endpoint_bytes)
            logs={}
            for item in report['modules']:
                copy_primary(item['name'],compiler.confined(stage,item['checked_artifacts']['']),item['artifacts'][''],job['key'])
                data=read(item['log']);target=compiler.confined(evidence,item['log'])
                target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
                logs[item['log']]=digest_bytes(data)
            receipt={'key':job['key'],'sign':job['sign'],'start':job['start'],'count':32,
              'archive_path':str(archive),'archive_sha256':job['archive_sha256'],
              'manifest_sha256':digest_bytes(read('manifest.json')),
              'compile_report_sha256':digest_bytes(read('compile_report.json')),
              'archive_output_node_sha256':digest_bytes(endpoint_bytes),'plan_output_node_sha256':checkpoint_hash,
              'root_module':root,'checked_constant':manifest['checked_constant'],'modules':names,'logs':logs}
            if compiler.digest(archive)!=job['archive_sha256']:raise ValueError('Original archive changed during staging')
            compiler.atomic_json(evidence/'receipt.json',receipt);receipts.append(receipt)
            compiler.atomic_json(output/'public_index.json',status)
            print('STAGED_PUBLIC_ARCHIVE',job['key'],len(receipts),'/',len(plan['jobs']),flush=True)
        finally:
            # Only this newly created stage may be recursively removed. The
            # archive and all caller-owned directories remain untouched.
            if stage.exists():
                resolved=stage.resolve();parent=scratch_root.resolve();target=output.resolve()
                if resolved==parent or not resolved.is_relative_to(parent) or not parent.is_relative_to(target):
                    raise ValueError('Unsafe scratch cleanup target')
                shutil.rmtree(resolved)
    public_tree_check(public,copies)
    if any(scratch_root.iterdir()):raise ValueError('Unexpected retained private expansion')
    if args.plan.read_bytes()!=plan_bytes or args.base_lock.read_bytes()!=lock_bytes or args.base_args.read_bytes()!=argument_bytes:
        raise ValueError('Registry/base binding changed')
    if plan['mode']=='full':
        again,_=validate_plan(plan,args.trajectory_plan)
        if again!=source_plan:raise ValueError('Trajectory plan changed')
    for path,expected in helpers.items():
        if compiler.digest(path)!=expected:raise ValueError('Staging/helper code changed')
    status.update(status='prepared',full_plan_coverage_verified=plan['mode']=='full',
      archives_retained_in_place=True,private_project_input_files=0,
      public_input_bytes=sum(x['bytes'] for x in copies.values()),processed_archives=len(receipts))
    compiler.atomic_json(output/'public_index.json',status)
    print(json.dumps({k:v for k,v in status.items() if k not in ['receipts','public_inputs','helper_sha256']}),flush=True)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['plan','archive-root','base-lock','base-args','output']:
        p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--trajectory-plan',type=Path)
    p.add_argument('--max-unpacked-mb',type=int,default=512)
    args=p.parse_args()
    if args.max_unpacked_mb<=0:p.error('Positive unpacked-size limit required')
    try:prepare(args)
    except BaseException as error:
        if hasattr(args,'owned_output'):
            compiler.atomic_json(args.owned_output/'failure.json',{'status':'failed','error':str(error),
              'full_plan_coverage_verified':False,'lean_reimport_checked':False})
        raise

if __name__=='__main__':main()
