"""Compile three pitch modules from public Q2 artifacts, using fresh absolute paths."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import time

PREFIX = 'SolitonClassification.'
BASE = 'dcf9b162c42c30f387803fc9f395fcb1183f0e8179f5b46004782ba4bbf1f10d'
FINAL48 = '23e73ccbac0d8d374ff23634eb67967ac41ae3f8bc5594e24e3f53fb3b26d9af'
FULL = 'SolitonClassification.Rotating.FullCandidate'
LEAVES = [PREFIX+'PitchContinuation', PREFIX+'CandidatePitchBranch', PREFIX+'Rotating.FullPitchAccumulation']
ALIASES = ['SolitonClassification.Rotating.PitchContinuation.dense_pitch_of_certificate',
           'SolitonClassification.Rotating.CandidatePitchBranch.actual_closed_pitch_dense_of_remaining_enclosures',
           'SolitonClassification.Rotating.FullPitchAccumulation.exists_dense_positive_closed_rotating_pitches']
REVIEWED = dict(zip(LEAVES,[
    '5dc682442386a921635747c38c6724b651e3332bc3693660c6adf68800345b1a',
    'a17dbe31f858315721a8c4cfb2a2772822cc9ad7374aa62cabc44dbad80689b3',
    '212adf5865dcd506c75f276b148e06bc7eab9f2601e22e7251b5884097e0ce49']))
NAME = re.compile(r'[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)+')

def require(test, msg):
    if not test:
        raise ValueError(msg)

def read(path):
    return json.loads(path.read_bytes())

def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream,'sha256').hexdigest()

def save(path, obj):
    path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n',encoding='utf-8')

def rel(name, suffix='.olean'):
    require(NAME.fullmatch(name) and name.startswith(PREFIX),'Invalid project module name')
    return Path(*name.split('.')).with_suffix(suffix)

def check(path, expected):
    require(path.is_file() and path.stat().st_size == expected['bytes'] and
            digest(path)==expected['sha256'], 'Object digest/length mismatch: '+str(path))

def public_source(src):
    text=src.decode('utf-8')
    require(not text.startswith('module\n'),'Expected reviewed legacy source')
    lines=text.splitlines(keepends=True)
    imports=[]
    for line in lines:
        if not line.startswith('import '): break
        imports.append(line.strip().split()[1])
    require(imports and len(set(imports))==len(imports),'Unrecognized source header')
    return ('module\n\n'+''.join('public import '+n+'\n' for n in imports)+
            '\n@[expose] public section\n'+''.join(lines[len(imports):])),imports

def relocate_index(assembly, final48, parts, pool):
    """Use the verified compact shards and actual Q2 outputs, ignoring all archival absolute paths."""
    outer=read(assembly/'assembly_report.json')
    seqfile=assembly/'compiled/compile_report.json'
    require(outer['status']=='concrete_candidate_kernel_checked' and outer['full_certificate_proved']
            and outer['full_path_instances_checked'] and outer['actual_source_modules']==502
            and outer['sequence_report_sha256']==digest(seqfile),'Q2 has not completed its real kernel check')
    manfile=assembly/'run_manifest.json'
    require(digest(manfile)==outer['run_manifest_sha256'],'Wrong Q2 run manifest')
    manifest=read(manfile)
    require(manifest['base_lock_sha256']==BASE and manifest['actual_Linux48_report_sha256']==FINAL48
            and manifest['source_module_count']==502 and manifest['new_Lean_call_count']==503,'Wrong Q2 inputs')
    ipath=assembly/'validation_after/public_input_index.json'
    epath=assembly/'validation_after/execution_plan.json'
    require(digest(ipath)==manifest['public_index_sha256'] and digest(epath)==manifest['execution_plan_sha256'],
            'Archived post-check index or graph changed')
    seq=read(seqfile)
    require(seq['status']=='kernel_sequence_checked' and len(seq['modules'])==502
            and seq['fresh_hypothesis_free_alias_checked'] and seq['complete_input_output_evidence_checked'],
            'Original assembly sequence audit failed')
    initial=read(ipath)['modules']
    graph=read(epath)['graph']
    origins={n:r['origin']['kind'] for n,r in initial.items()}
    expected={n:{k:r[k] for k in ['sha256','bytes']} for n,r in initial.items()}
    paths={}
    shard_names={n for n in initial if origins[n]=='checked_shard'}
    require(len(shard_names)==11750 and len(initial)==11885,'Unexpected Q2 initial graph')
    for n in sorted(set(initial)-shard_names):
        require(origins[n] in ('captured_core','actual_Linux48'),'Unknown input origin')
        p=final48/'public_inputs'/rel(n)
        check(p,expected[n])
        paths[n]=p
    ledger=read(assembly.parent/'fullmerge/ledger.json')
    require(digest(assembly.parent/'fullmerge/ledger.json')==manifest['ledger_sha256']
            and ledger['mode']=='full' and len(ledger['jobs'])==250,'Wrong original shard ledger')
    transports={p.name:p for p in parts.glob('batch??/*.public.tar.xz')}
    require(len(transports)==250 and sum(1 for _ in parts.glob('batch??/*.public.tar.xz'))==250,
            'Missing or duplicate batch transport artifacts')
    for job in ledger['jobs']:
        key=job['key']
        require(re.fullmatch(r'R[PM]\d{4}',key),'Invalid shard key')
        path=transports[key+'.public.tar.xz']
        unpack_transport(path,key,job['transport_sha256'],initial,paths,pool)
    require(shard_names.issubset(paths),'Incomplete shard public objects')
    for row in seq['modules']:
        n=row['name']
        require(n not in paths and row['exit_code']==0,'Invalid new module entry')
        p=assembly/'compiled/checked'/rel(n)
        check(p,row['artifacts'][''])
        paths[n]=p
    require(FULL in paths and set(paths)==set(graph),'Incomplete relocated Q2 graph')
    return paths,graph,outer

def unpack_transport(path,key,expected_digest,index,paths,pool):
    """Extract only independently indexed regular public proof files, streaming one transport at a time."""
    require(digest(path)==expected_digest,'Changed '+key+' transport')
    count=0
    with tarfile.open(path,mode='r|xz') as tar:
        for member in tar:
            if not member.name.startswith('public/'):
                continue
            require(member.isfile() and member.name.endswith('.olean'),'Unexpected public archive entry')
            name=member.name[7:-6].replace('/','.')
            require(name in index and name not in paths and member.name=='public/'+rel(name).as_posix(),
                    'Unexpected, duplicate or unsafe public module')
            info=index[name]
            require(info['origin']['key']==key and info['bytes']==member.size,'Shard module source mismatch')
            dst=pool/rel(name)
            dst.parent.mkdir(parents=True,exist_ok=True)
            with tar.extractfile(member) as inp,dst.open('xb') as out:
                shutil.copyfileobj(inp,out)
            check(dst,info)
            paths[name]=dst
            count+=1
    require(count==47,'Expected 47 certified public modules per shard')

def compile_suffix(sources, paths, graph, lean, external, output, input_hashes, scope, extra_arts=None):
    output.mkdir(parents=True,exist_ok=False)
    require(len(sources)==3,'Require two bridge sources and a final source')
    produced=[]
    for name,source in zip(LEAVES,sources):
        original=source.read_bytes()
        require(hashlib.sha256(original).hexdigest()==input_hashes[name],'Unreviewed suffix input: '+name)
        baseline,imports=public_source(original)
        # All three fresh source declarations are present; enforce each exact theorem's dependencies.
        _,_,last=ALIASES[len(produced)].rpartition('.')
        require('theorem '+last in baseline,'Missing target theorem')
        if name==LEAVES[-1]:
            # The original handoff source has no top-level hypotheses. The real
            # pre-assembly pilot deliberately binds two blocks and eight identities.
            guard=('if info.type.isForall then throwError "Unexpected final hypothesis"'
                   if scope=='post_successful_q2_linux' else
                   'unless info.type.isForall do throwError "Pilot must retain the ten block inputs"')
            marker=('PITCH_ZERO_HYPOTHESES_STANDARD_THREE' if scope=='post_successful_q2_linux'
                    else 'PITCH_PILOT_WITH_BLOCK_INPUTS')
            baseline+=('\nopen Lean Elab Command in\nrun_cmd do\n  let info ← getConstInfo '
                       +chr(96)+ALIASES[-1]+'\n  '+guard+'\n  unless info.levelParams.isEmpty do '
                       +'throwError "Unexpected universe parameters"\n  logInfo "'+marker+'"\n')
        checked_source=output/'source'/rel(name,'.lean')
        checked_source.parent.mkdir(parents=True,exist_ok=True)
        checked_source.write_bytes(baseline.encode('utf-8'))
        graph[name]=[d for d in imports if d.startswith(PREFIX)]
        needed=set()
        def visit(n):
            if n in needed: return
            require(n in paths and n in graph,'Missing transitive proof '+n)
            needed.add(n)
            for d in graph[n]: visit(d)
        for dep in graph[name]: visit(dep)
        configured={n:[[str(paths[n].resolve())],[]] for n in sorted(needed)}
        configured.update(extra_arts or {})
        setup=output/(name+'.setup.json')
        save(setup,dict(name=name,isModule=True,package=None,plugins=[],dynlibs=[],options={},importArts=configured))
        obj=output/'checked'/rel(name)
        obj.parent.mkdir(parents=True,exist_ok=True)
        start=time.monotonic()
        job=subprocess.run([str(lean),'--setup',str(setup),'-j','1','-M','6144','-o',str(obj),str(checked_source)],
                           capture_output=True,timeout=900,env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,external)),LC_ALL='C'))
        log=output/(name+'.log')
        log.write_bytes(job.stdout+job.stderr)
        row=dict(module=name,source_sha256=digest(source),public_header_source_sha256=digest(checked_source),
                 setup_sha256=digest(setup),log_sha256=digest(log),exit=job.returncode,
                 public_project_dependencies=len(needed),wall_seconds=time.monotonic()-start)
        produced.append(row)
        save(output/'report.json',dict(scope=scope,status='running',modules=produced))
        require(job.returncode==0 and b'error:' not in log.read_bytes() and b'warning:' not in log.read_bytes(),
                'Lean failed: '+name+'\n'+log.read_text(encoding='utf-8',errors='replace')[-4000:])
        if name==LEAVES[-1]:
            require(marker in log.read_text(encoding='utf-8') and
                    'Dense actual-pitch theorem passed the standard three-axiom audit.' in log.read_text(encoding='utf-8'),
                    'Missing Lean final type or axiom audit')
        row['object_sha256']=digest(obj)
        paths[name]=obj
    save(output/'report.json',dict(scope=scope,status='checked',modules=produced,
                                   concrete_full_pitch_checked=scope=='post_successful_q2_linux'))
    return produced

def main():
    ap=argparse.ArgumentParser()
    for key in ['assembly','final48','parts','restored','sources','out']:
        ap.add_argument('--'+key,type=Path,required=True)
    a=ap.parse_args()
    require(not a.out.exists(),'Choose an unused output directory')
    require(digest(a.final48/'compile_report.json')==FINAL48 and digest(a.restored/'base_lock.json')==BASE,
            'Original Linux base or final48 differs')
    a.out.mkdir(parents=True)
    paths,graph,evidence=relocate_index(a.assembly,a.final48,a.parts,a.out/'shard_public')
    loc=read(a.restored/'base_args.json')
    require(loc[0]=='--lean' and len(loc)%2==0,'Unexpected restored Lean paths')
    lean=Path(loc[1])
    seq=read(a.assembly/'compiled/compile_report.json')
    require(digest(lean)==seq['lean']['sha256'],'Different Lean executable')
    roots=dict(loc[i+1].split('=',1) for i in range(2,len(loc),2))
    core_labels={r['origin']['label'] for r in read(a.assembly/'validation_after/public_input_index.json')['modules'].values()
                 if r['origin']['kind']=='captured_core'}
    external=[Path(p) for label,p in roots.items() if label not in core_labels]
    hashed=read(a.sources/'source_hashes.json')
    require(hashed==REVIEWED,'The three reviewed sources have changed')
    result=compile_suffix([a.sources/rel(n,'.lean') for n in LEAVES],paths,graph,lean,external,
                          a.out/'suffix',hashed,'post_successful_q2_linux')
    save(a.out/'verified.json',dict(status='checked',q2_report_sha256=digest(a.assembly/'assembly_report.json'),
        q2_kernel_calls_repeated=0,suffix_modules=len(result),theorem=ALIASES[-1],
        standard_axioms_only=True,full_classification_claimed=False))

if __name__=='__main__':
    main()
