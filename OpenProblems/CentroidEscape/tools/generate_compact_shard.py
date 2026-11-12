"""Generate a deterministic, independently kernel-checkable Taylor shard.

Only Python's standard library is used. Native JSON and this generator are
untrusted; arithmetic, gluing and the strict axiom audit are Lean proofs.
Existing frozen modules are never named or overwritten by this generator.
"""
from pathlib import Path
from fractions import Fraction
import argparse
import hashlib
import json

CASES = ("center", "a_plus", "a_minus", "b_plus", "b_minus")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def integer(value):
    text = str(value)
    number = int(text)
    if str(number) != text:
        raise ValueError(f"Noncanonical integer: {text!r}")
    return text


def ball(pair):
    if len(pair) != 2 or int(pair[1]) < 0:
        raise ValueError("Expected a center and nonnegative radius")
    return "⟨" + integer(pair[0]) + ", " + integer(pair[1]) + "⟩"


def vector(values):
    if len(values) != 7:
        raise ValueError("Expected seven coordinates")
    return "⟨#[" + ",".join(map(ball, values)) + "], rfl⟩"


def rational(value):
    value = Fraction(value)
    return f"({value.numerator} : ℚ) / {value.denominator}"


def assembly(mode):
    body = """  let P : ℕ → Prop := fun n =>
    stepData.square n=fixedTaylorNextSquare mesh n stepData ∧
    stepData.coeffs[n+1]?.getD (Vector.ofFn zeroFixedVector)=
      fixedTaylorNextCoeff mesh n stepData (stepData.square n)
"""
    if mode == "bounded":
        term = "(fun i hi => (Nat.not_lt_zero i hi).elim)"
        for n in range(60):
            term = f"(checkedStagesExtend P {n} {term} stage{n})"
        body += f"  have h : ∀ n<60, P n := {term}\n"
        result = "fun n => h n.val n.isLt"
    else:
        term = "(fun i : Fin 0 => Fin.elim0 i)"
        for n in reversed(range(60)):
            term = f"(Fin.cases stage{n} {term})"
        body += f"  have h : ∀ n : Fin 60, P n.val := {term}\n"
        result = "h"
    return body + "  apply decide_eq_true\n  exact ⟨by decide +kernel, by decide +kernel, " + result + "⟩\n\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--data-root", type=Path, required=True)
    parser.add_argument("--case", choices=CASES, required=True)
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--count", type=int, required=True)
    parser.add_argument("--outdir", "--output-root", dest="outdir", type=Path, required=True)
    parser.add_argument("--assembly", choices=("bounded", "fin_cases"), default="bounded")
    parser.add_argument("--force", action="store_true", help="Replace only this generator's namespaced output files")
    args = parser.parse_args()
    if not (0 <= args.start < 750 and 1 <= args.count <= 750 - args.start):
        raise ValueError("Requested interval must be a nonempty subset of 0..749")
    data_dir = args.data_root.resolve() / args.case
    status_bytes = (data_dir / "status.json").read_bytes()
    status = json.loads(status_bytes)
    status_start = int(status.get("start", 0))
    status_steps = int(status["steps"])
    mesh_steps = int(status.get("mesh_steps", 750))
    if status["case"] != args.case or int(status["order"]) != 60 or mesh_steps != 750:
        raise ValueError("Wrong case, order, or mesh-step count in status")
    if status_start > args.start or status_start + status_steps < args.start + args.count:
        raise ValueError("Status interval does not cover the requested shard")
    mesh = int(status["mesh"])
    h = Fraction(status["h"])
    length = Fraction(status["L"])
    if mesh <= 0 or h != length / 750 or not 0 < h <= Fraction(1, 100):
        raise ValueError("Inconsistent positive mesh or h=L/750<=.01")
    records, inputs = [], []
    for step in range(args.start, args.start + args.count):
        path = data_dir / f"step{step}.json"
        raw = path.read_bytes()  # Missing data always raises; no fallback.
        record = json.loads(raw)
        if record["step"] != step or len(record["coefficients"]) != 61 or len(record["squares"]) != 60:
            raise ValueError(f"Wrong step index or dimensions in {path.name}")
        records.append(record)
        inputs.append({"file": f"{args.case}/{path.name}", "sha256": sha(raw)})
    key = f"Shard_{args.case}_s{args.start:04}_n{args.count:04}_{args.assembly}"
    base = f"CentroidEscape.CertificateShards.{key}"
    outdir = args.outdir.resolve()
    outdir.mkdir(parents=True, exist_ok=True)
    manifest_path = outdir / "manifest.json"
    if manifest_path.exists() and json.loads(manifest_path.read_text())["key"] != key:
        raise ValueError("Output directory belongs to a different shard")
    modules = []

    def emit(part, source):
        module = f"CentroidEscape.{key}_{part}"
        relative = Path("sources") / Path(*module.split(".")).with_suffix(".lean")
        target = outdir / relative
        encoded = source.encode("utf-8")
        if target.exists() and target.read_bytes() != encoded and not args.force:
            raise FileExistsError(f"Changed generated source requires --force: {target}")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(encoded)
        modules.append({"name": module, "source": relative.as_posix(), "sha256": sha(encoded)})
        return module

    params = emit("Parameters", f"""import CentroidEscape.CompactStageAssembly

namespace {base}
noncomputable def mesh : ℕ := {mesh}
noncomputable def candidateL : ℚ := {rational(length)}
noncomputable def stepTime : ℚ := {rational(h)}
theorem mesh_pos : 0<mesh := by decide +kernel
theorem stepTime_eq : stepTime=candidateL/750 := by decide +kernel
theorem stepTime_bounds : 0<stepTime ∧ stepTime≤1/100 := by decide +kernel
end {base}
""")
    steps = []
    for d in records:
        index = d["step"]
        short = f"Step{index:04}"
        ns = f"{base}.{short}"
        source = f"""import {params}
import CentroidEscape.BallStep

namespace {ns}
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

noncomputable def stepData : FixedTaylorState := ⟨#[
"""
        source += ",\n".join(map(vector, d["coefficients"])) + "\n],#[\n"
        source += ",\n".join(map(ball, d["squares"])) + "\n]⟩\n\n"
        source += f"noncomputable def inputData : Vector FixedBall 7 := {vector(d['coefficients'][0])}\n\n"
        source += f"noncomputable def endpointData : Vector FixedBall 7 := {vector(d['endpoint'])}\n\n"
        for n in range(60):
            source += f"""theorem stage{n} :
    stepData.square {n}=fixedTaylorNextSquare mesh {n} stepData ∧
    stepData.coeffs[{n+1}]?.getD (Vector.ofFn zeroFixedVector)=
      fixedTaylorNextCoeff mesh {n} stepData (stepData.square {n}) := by
  decide +kernel

"""
            if n % 10 == 9:
                source += f'run_cmd Lean.logInfo "{short}: stages 0 through {n} checked."\n\n'
        source += "theorem allStagesChecked : checkOrderTaylorData mesh 60 stepData=true := by\n" + assembly(args.assembly)
        source += """run_cmd Lean.logInfo "Compact assembly checked."

theorem inputCoefficient (i : Fin 7) : stepData.coefficient 0 i=inputData[i.val] := by rfl

theorem endpointCorrect : endpointData=evaluateFixedTaylorOrder mesh 60 stepTime stepData := by
  decide +kernel

run_cmd Lean.logInfo "Actual endpoint checked."

theorem initialMarginCheck : checkBallCanonicalMargin
    (fun i=>(stepData.coefficient 0 i).toRational mesh)=true := by
  decide +kernel

theorem endpointMarginCheck : checkBallCanonicalMargin
    (fun i=>endpointData[i.val].toRational mesh)=true := by
  decide +kernel

run_cmd Lean.logInfo "Input and endpoint margins checked."
attribute [irreducible] stepData
"""
        source += f"\nend {ns}\n"
        module = emit(short, source)
        steps.append({"short": short, "namespace": ns, "module": module, "index": index})

    blocks = []
    for offset in range(0, len(steps), 5):
        group = steps[offset:offset + 5]
        size = len(group)
        short = f"Block{offset // 5:04}"
        ns = f"{base}.{short}"
        source = "import CentroidEscape.FiniteTaylorBlock\n" + "".join(f"import {s['module']}\n" for s in group)
        source += f"\nnamespace {ns}\nopen MetricStability\nset_option maxRecDepth 100000\nset_option maxHeartbeats 5000000\n\n"
        for j in range(size - 1):
            source += f"theorem glue{j} : {group[j+1]['short']}.inputData={group[j]['short']}.endpointData := by decide +kernel\n\n"
        first, last = group[0]["short"], group[-1]["short"]
        source += f"noncomputable def inputData : Vector FixedBall 7 := {first}.inputData\n"
        source += f"noncomputable def endpointData : Vector FixedBall 7 := {last}.endpointData\n"
        source += "noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩\n\n"
        source += "noncomputable def stages : ℕ → FixedTaylorState\n"
        source += "".join(f"  | {j}=>{s['short']}.stepData\n" for j, s in enumerate(group))
        source += "  | _=>terminalData\n\n"
        source += f"theorem checked : Order60SegmentValid mesh stepTime {size} stages := by\n  intro j hj\n  interval_cases j\n"
        for j, s in enumerate(group):
            here = s["short"]
            nxt = group[j+1]["short"] + ".stepData" if j+1 < size else "terminalData"
            source += f"""  · change checkOrderTaylorData mesh 60 {here}.stepData=true ∧
      (∀ i : Fin 7, {nxt}.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime {here}.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>({here}.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨{here}.allStagesChecked,?_,{here}.initialMarginCheck⟩
    intro i
"""
            if j+1 < size:
                source += f"    rw [{group[j+1]['short']}.inputCoefficient,← {here}.endpointCorrect,glue{j}]\n"
            else:
                source += f"    change {here}.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime {here}.stepData)[i.val]\n    rw [← {here}.endpointCorrect]\n"
        source += f"""
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change {first}.stepData.coefficient 0 i={first}.inputData[i.val]
  exact {first}.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages {size}).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end {ns}
"""
        module = emit(short, source)
        blocks.append({"short": short, "namespace": ns, "module": module, "count": size})

    level = 0
    while len(blocks) > 1:
        merged = []
        for pair in range(0, len(blocks), 2):
            if pair + 1 == len(blocks):
                merged.append(blocks[pair])
                continue
            a, b = blocks[pair:pair+2]
            left, right = a["short"], b["short"]
            n, m = a["count"], b["count"]
            short = f"Merge{level:03}_{pair//2:04}"
            ns = f"{base}.{short}"
            source = f"""import {a['module']}
import {b['module']}

namespace {ns}
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue : {left}.endpointData={right}.inputData := by decide +kernel

theorem boundary : ∀ i : Fin 7,
    ({left}.stages {n}).coefficient 0 i=({right}.stages 0).coefficient 0 i := by
  intro i
  rw [{left}.terminalCoefficient,{right}.initialCoefficient,glue]

noncomputable def inputData : Vector FixedBall 7 := {left}.inputData
noncomputable def endpointData : Vector FixedBall 7 := {right}.endpointData
noncomputable def stages : ℕ → FixedTaylorState :=
  appendTaylorStages {n} {left}.stages {right}.stages

theorem checked : Order60SegmentValid mesh stepTime {n+m} stages :=
  Order60SegmentValid.append {left}.checked {right}.checked boundary

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages {n} {left}.stages {right}.stages 0).coefficient 0 i={left}.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact {left}.initialCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages {n+m}).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages {n} {left}.stages {right}.stages ({n}+{m})).coefficient 0 i={right}.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact {right}.terminalCoefficient i

attribute [irreducible] stages
end {ns}
"""
            module = emit(short, source)
            merged.append({"short": short, "namespace": ns, "module": module, "count": n+m})
        blocks = merged
        level += 1
    root = blocks[0]
    audit = emit("Audit", f"""import {root['module']}

#print axioms {root['namespace']}.checked

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`{base}).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Shard audit failed: {{name}} depends on {{axiomName}}"
      count := count+1
  logInfo m!"Strict shard audit passed for {{count}} declarations."
""")
    manifest = {
        "schema": "centroid.compact-shard.v1", "key": key, "case": args.case,
        "start": args.start, "count": args.count, "order": 60, "mesh_steps": 750,
        "mesh": str(mesh), "h": str(h), "assembly": args.assembly, "namespace": base,
        "generator_sha256": sha(Path(__file__).read_bytes()),
        "native_status": {"file": f"{args.case}/status.json", "sha256": sha(status_bytes)},
        "inputs": inputs, "modules": modules, "root_module": root["module"],
        "checked_theorem": root["namespace"] + ".checked", "audit_module": audit,
        "first_input": records[0]["coefficients"][0], "last_endpoint": records[-1]["endpoint"],
        "required_generic_modules": ["CentroidEscape.CompactStageAssembly", "CentroidEscape.FiniteTaylorBlock", "CentroidEscape.BallStep"],
    }
    manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Generated {len(steps)} actual steps, five-step blocks and balanced assembly: {manifest_path}")


if __name__ == "__main__":
    main()
