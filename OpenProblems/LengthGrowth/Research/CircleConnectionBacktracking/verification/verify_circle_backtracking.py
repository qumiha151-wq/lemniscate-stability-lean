from pathlib import Path
import os, subprocess, hashlib, json, time

ROOT=Path(__file__).resolve().parent.parent
SOURCE=ROOT/'outputs/open-problems/LengthGrowth/LengthGrowth/CircleConnectionBacktracking.lean'
MATHLIB=Path('C:/Users/17815/Desktop/论文/lean_deps/mathlib4-4.33.1')
LEAN=Path('C:/Users/17815/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean.exe')
OUT=ROOT/'work/next_research/circle_backtracking_lean'/str(time.time_ns())
OUT.mkdir(parents=True,exist_ok=False)
paths=[MATHLIB/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (MATHLIB/'.lake/packages').iterdir() if p.is_dir()]
env=dict(os.environ, LEAN_PATH=os.pathsep.join(str(p) for p in paths if p.is_dir()))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before=sha(SOURCE)
argv=[str(LEAN),'-o',str(OUT/'CircleConnectionBacktracking.olean'),str(SOURCE)]
started=time.time()
r=subprocess.run(argv,cwd=SOURCE.parent.parent,env=env,capture_output=True,timeout=180)
(OUT/'stdout.txt').write_bytes(r.stdout)
(OUT/'stderr.txt').write_bytes(r.stderr)
result={'argv':argv,'exit_code':r.returncode,'elapsed_seconds':time.time()-started,
        'source_sha256':before,'source_unchanged':before==sha(SOURCE),
        'stdout_sha256':sha(OUT/'stdout.txt'),'stderr_sha256':sha(OUT/'stderr.txt'),
        'full_length_growth_proved':False,'connection_existence_proved':False}
(OUT/'result.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(r.stdout.decode('utf-8',errors='replace'))
print(r.stderr.decode('utf-8',errors='replace'))
print(json.dumps(result))
raise SystemExit(r.returncode)
