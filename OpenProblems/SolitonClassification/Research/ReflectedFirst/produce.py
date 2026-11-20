"""Generate self-contained Lean chunks for the three pure-expander shots."""
from pathlib import Path
import argparse
from make_replay import box
from mesh_replay import replay, STEPS

START = ["import SolitonClassification.Reflected.Trace",
         "namespace SolitonClassification.Reflected",
         "set_option maxHeartbeats 0","set_option maxRecDepth 2000000",
         "set_option Elab.async false","set_option linter.unnecessarySeqFocus false"]

def emit(path,lines):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(("\r\n".join(lines)+"\r\n").encode("utf8"))

def make(dest, size, stop):
    produced=[]
    for label in ["minus","all","plus"]:
        rows=replay(label,stop)
        pieces=[]
        for start in range(0,stop,size):
            end=min(start+size,stop)
            name=f"{label.capitalize()}B{start:03d}"
            out=START+[f"namespace {name}"]
            for j in range(start,end+1):
                out.append(f"def b{j} : Box := {box(rows[j])}")
            for j in range(start,end):
                out.extend([f"theorem step{j} : Segment traceStep b{j} b{j+1} (traceStep:ℝ) := by",
                    "  exact Segment.single traceStep_spec (by decide +kernel) (by decide +kernel)"])
            times="(traceStep:ℝ)"
            proof=f"step{start}"
            for j in range(start+1,end):
                times=f"({times}+(traceStep:ℝ))"
                proof=f"({proof}).join step{j}"
            out.extend([f"theorem block : Segment traceStep b{start} b{end} ({end-start}*(traceStep:ℝ)) := by",
                f"  convert ({proof}) using 1 <;> ring",
                f"end {name}","end SolitonClassification.Reflected",
                f"#print axioms SolitonClassification.Reflected.{name}.block"])
            emit(dest/(name+".lean"),out)
            pieces.append((name,start,end))
            produced.append(name)
        out=[f"import SolitonClassification.Reflected.{name}" for name,_,_ in pieces]
        n=label.capitalize()+"Trajectory"
        out+=["namespace SolitonClassification.Reflected",f"namespace {n}","set_option maxHeartbeats 0","set_option maxRecDepth 2000000",
              "set_option linter.unnecessarySeqFocus false"]
        proof=pieces[0][0]+".block"
        for piece,_,_ in pieces[1:]:
            proof=f"({proof}).join {piece}.block"
        out+=[f"theorem trajectory : Segment traceStep {pieces[0][0]}.b0 {pieces[-1][0]}.b{stop} ({stop}*(traceStep:ℝ)) := by",
              f"  convert ({proof}) using 1 <;> ring",f"end {n}","end SolitonClassification.Reflected",
              f"#print axioms SolitonClassification.Reflected.{n}.trajectory"]
        emit(dest/(n+".lean"),out)
        produced.append(n)
    return produced

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--dest",type=Path,required=True)
    p.add_argument("--size",type=int,default=12)
    p.add_argument("--steps",type=int,default=STEPS)
    args=p.parse_args()
    make(args.dest,args.size,args.steps)
