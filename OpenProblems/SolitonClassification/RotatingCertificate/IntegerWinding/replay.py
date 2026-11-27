"""Recompute in a temporary tree, with native assertions on, then check the Lean input boxes."""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

if not __debug__ or sys.flags.optimize:
    raise SystemExit("Use ordinary Python, without -O, -OO or PYTHONOPTIMIZE.")

here=Path(__file__).resolve().parent
sys.path.insert(0,str(here.parents[1]/"pydeps"))
import flint
from flint import arb,ctx

def canonical_json(path):
    # The archived report bytes use CRLF on all platforms.
    data=path.read_bytes().replace(b"\r\n",b"\n")
    path.write_bytes(data.replace(b"\n",b"\r\n"))

def validate_lean_boxes(working,lean):
    ctx.dps=85
    doc=lean.read_text(encoding="utf8")
    match = re.search(r"def ball \(x : ℚ\) : RationalBall := ⟨x,2/10\^12⟩",doc)
    assert match
    reports=json.loads((working/"hyperbolic.json").read_bytes())
    for name,infl in zip(("plus","minus"),reports["inflations"]):
        region=doc.split("def "+name+" : Four ℚ := ")[1].split("\n\n")[0]
        nums=re.findall(r"\((-?\d+):ℚ\)/10\^14",region)
        assert len(nums)==16
        matrix=json.loads((working/(name+".json")).read_bytes())["matrix"]
        for i in range(4):
            for j in range(4):
                assert abs(arb(matrix[i][j])-arb(nums[4*i+j])/10**14)+arb(infl)<arb(2)/10**12

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--saved",action="store_true",help="check saved half grids without regenerating them")
    p.add_argument("--require-byte-match",action="store_true",
                   help="also require exact byte agreement with all four archived reports")
    args=p.parse_args()
    if sys.version_info[:2]!=(3,12) or flint.__version__!="0.9.0":
        raise SystemExit("Use Python 3.12 with python-flint==0.9.0.")
    kernel=here.parent/"classification_odd_branch_interval"/"validated_metric_shoot.py"
    lean=here.parents[1]/"SolitonClassification/Rotating/IntegerWindingPencil.lean"
    if not lean.is_file():
        lean=here/"IntegerWindingPencil.lean"
    with TemporaryDirectory() as tmp:
        wd=Path(tmp)/"IntegerWinding";wd.mkdir()
        shared=wd.parent/"classification_odd_branch_interval";shared.mkdir()
        shutil.copyfile(kernel,shared/kernel.name)
        for f in ("center.json","trajectory.py","verify.py","local.py"):
            shutil.copyfile(here/f,wd/f)
        # Let a local research installation supply flint on child sys.path.
        env=dict(os.environ)
        paths=[p for p in sys.path if Path(p,"flint").is_dir()]
        env["PYTHONPATH"]=os.pathsep.join(paths+[env.get("PYTHONPATH","")])
        def run(file,*argv):
            subprocess.run([sys.executable,str(wd/file),*argv],check=True,cwd=wd,env=env)
        if args.saved:
            for f in ("plus.json","minus.json"):shutil.copyfile(here/f,wd/f)
        else:
            with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
                jobs=[pool.submit(run,"trajectory.py",s) for s in ("1","-1")]
                for job in jobs:job.result()
        for f in ("plus.json","minus.json"):canonical_json(wd/f)
        run("verify.py");canonical_json(wd/"certificate.json")
        run("local.py");canonical_json(wd/"hyperbolic.json")
        validate_lean_boxes(wd,lean)
        for f in ("plus.json","minus.json","certificate.json","hyperbolic.json"):
            computed=(wd/f).read_bytes()
            matches=(here/f).read_bytes()==computed
            print(f,hashlib.sha256(computed).hexdigest(),"archive byte match",matches)
            if args.require_byte_match and not matches:
                raise RuntimeError("Archived report bytes differ: "+f)
        print("All root, radius, winding, primitivity, multiplier and Lean endpoint-box checks passed.")

if __name__=="__main__":
    main()
