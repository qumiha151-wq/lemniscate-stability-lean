from pathlib import Path
import os,subprocess,hashlib,json,shutil,time

ROOT=Path(__file__).resolve().parent.parent
OUT=ROOT/'work/next_research/circle_backtracking_root_audit_v2'
OUT.mkdir(exist_ok=False)
(OUT/'LengthGrowth').mkdir()
PROJ=ROOT/'outputs/open-problems/LengthGrowth'
OLD=ROOT/'work/formal-build/LengthGrowth'
MATH=Path('C:/Users/17815/Desktop/论文/lean_deps/mathlib4-4.33.1')
LEAN=Path('C:/Users/17815/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean.exe')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
actual=ROOT/'work/next_research/circle_backtracking_lean/1794545917190929300'
record=json.loads((actual/'result.json').read_bytes())
assert record['exit_code']==0 and record['source_sha256']==sha(PROJ/'LengthGrowth/CircleConnectionBacktracking.lean')
old_pins={}
for p in (OLD/'LengthGrowth').iterdir():
    if p.is_file() and p.name!='AxiomAudit.olean':
        old_pins[p.name]=sha(p)
        shutil.copyfile(p,OUT/'LengthGrowth'/p.name)
for p in actual.glob('CircleConnectionBacktracking.olean*'):
    shutil.copyfile(p,OUT/'LengthGrowth'/p.name)
paths=[OUT,OLD,MATH/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (MATH/'.lake/packages').iterdir() if p.is_dir()]
env=dict(os.environ,LEAN_PATH=os.pathsep.join(str(p) for p in paths if p.is_dir()))
results=[]
for module in ('LengthGrowth','LengthGrowth/AxiomAudit'):
    source=PROJ/(module+'.lean');before=sha(source)
    argv=[str(LEAN),'-o',str(OUT/(module+'.olean')),str(source)]
    t=time.time();r=subprocess.run(argv,cwd=PROJ,env=env,capture_output=True,timeout=180)
    label=module.replace('/','_')
    (OUT/(label+'.stdout.txt')).write_bytes(r.stdout)
    (OUT/(label+'.stderr.txt')).write_bytes(r.stderr)
    results.append({'module':module,'argv':argv,'exit_code':r.returncode,'seconds':time.time()-t,
                    'source_sha256':before,'source_unchanged':before==sha(source),
                    'stdout_sha256':sha(OUT/(label+'.stdout.txt')),'stderr_sha256':sha(OUT/(label+'.stderr.txt'))})
    print(r.stdout.decode('utf-8',errors='replace'),flush=True)
    print(r.stderr.decode('utf-8',errors='replace'),flush=True)
    if r.returncode:break
out={'actual_commands':results,'reused_prior_dependency_modules':True,
     'new_leaf_compilation_repeated':False,'full_length_growth_proved':False,
     'script_sha256':sha(Path(__file__)),'original_cached_dependency_pins':old_pins}
assert all(sha(OLD/'LengthGrowth'/name)==digest for name,digest in old_pins.items())
(OUT/'result.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps(out))
raise SystemExit(results[-1]['exit_code'])
