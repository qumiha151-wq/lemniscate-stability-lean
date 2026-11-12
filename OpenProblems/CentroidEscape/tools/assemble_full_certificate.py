"""Generate the final typed five-path assembly from a complete shard set.

Generation is NOT kernel verification. All emitted equalities are proved
in Lean; the final unconditional theorem is available only after every
import and generated module compiles. No native/JSON pass bit is a proof.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import hashlib
import json
import re

CASES = ("center", "a_plus", "a_minus", "b_plus", "b_minus")
IDENTIFIER = re.compile(r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def checked_int(value):
    if isinstance(value, bool):
        raise ValueError("Boolean is not an integer datum")
    result = int(str(value))
    if str(result) != str(value):
        raise ValueError(f"Noncanonical integer {value!r}")
    return result


def fixed_vector(raw):
    if not isinstance(raw, list) or len(raw) != 7:
        raise ValueError("Expected seven fixed-mesh balls")
    result = []
    for pair in raw:
        if not isinstance(pair, list) or len(pair) != 2:
            raise ValueError("Expected center/radius pair")
        c, r = map(checked_int, pair)
        if r < 0:
            raise ValueError("Negative ball radius")
        result.append((c, r))
    return result


def vector_text(values):
    return "⟨#[" + ",".join(f"⟨{c},{r}⟩" for c, r in values) + "],rfl⟩"


def read_candidate(path):
    raw = path.read_bytes()
    text = re.sub(r"\s+", "", raw.decode("utf-8"))
    mesh_match = re.search(r"defmesh:ℕ:=(\d+)(?:\^(\d+))?(?=def)", text)
    parameter_match = re.search(r"defparameters:RationalVector3:=!\[(.*?)\]defendpointVectors", text)
    endpoint_match = re.search(r"defendpointVectors:Fin5→VectorFixedBall7:=!\[(.*?)\]defendpointBall", text)
    if not all((mesh_match, parameter_match, endpoint_match)):
        raise ValueError("Candidate source has an unexpected literal-data format")
    exponent = int(mesh_match.group(2) or 1)
    if exponent > 1000:
        raise ValueError("Unreasonable candidate mesh exponent")
    mesh = int(mesh_match.group(1)) ** exponent
    fractions = re.findall(r"\((-?\d+)/(\d+):ℚ\)", parameter_match.group(1))
    if len(fractions) != 3:
        raise ValueError("Expected exactly three literal rational candidate parameters")
    parameter = tuple(Q(int(a), int(b)) for a, b in fractions)
    pairs = re.findall(r"⟨(-?\d+),(\d+)⟩", endpoint_match.group(1))
    if len(pairs) != 35:
        raise ValueError("Expected exactly five candidate endpoint vectors")
    endpoints = [fixed_vector([[a, b] for a, b in pairs[7*k:7*k+7]]) for k in range(5)]
    if mesh <= 0 or not (1 <= parameter[2] and parameter[2] + Q(1,16000) <= Q(15,2)):
        raise ValueError("Candidate mesh or time is outside the proved range")
    return {"source":str(path),"sha256":sha(raw),"mesh":mesh,
            "parameter":parameter,"h":parameter[2]/750,"endpoints":endpoints}


def expected_parameter(candidate, case):
    a, b, length = candidate["parameter"]
    delta = Q(1,10**25)
    if case == "a_plus": a += delta
    if case == "a_minus": a -= delta
    if case == "b_plus": b += delta
    if case == "b_minus": b -= delta
    return a, b, length


def collect_paths(args):
    paths = list(args.manifest or [])
    if args.manifest_list:
        index = args.manifest_list.resolve()
        data = json.loads(index.read_text(encoding="utf-8"))
        items = data if isinstance(data,list) else data["manifests"]
        for item in items:
            entry = item if isinstance(item,dict) else None
            name = entry.get("manifest") if entry is not None else item
            if not isinstance(name,str):
                raise ValueError("Manifest index entries must be paths or {manifest,sha256,...} records")
            path = Path(name)
            path = path if path.is_absolute() else index.parent/path
            if entry is not None:
                raw = path.read_bytes()
                if sha(raw) != entry.get("sha256"):
                    raise ValueError(f"Manifest index hash mismatch: {path}")
                actual = json.loads(raw)
                for field in ("case","start","count","checked_theorem"):
                    if field in entry and actual.get(field) != entry[field]:
                        raise ValueError(f"Manifest index {field} mismatch: {path}")
            paths.append(path)
    if args.shards_root:
        paths.extend(args.shards_root.resolve().rglob("manifest.json"))
    resolved = [p.resolve() for p in paths]
    if len(set(resolved)) != len(resolved):
        raise ValueError("A shard manifest was supplied more than once")
    if not resolved:
        raise ValueError("Supply --manifest, --manifest-list, or --shards-root")
    return resolved


def validate_manifests(paths, candidate):
    groups = {case:[] for case in CASES}
    module_names = set()
    for path in paths:
        raw = path.read_bytes()
        data = json.loads(raw)
        if data.get("schema") != "centroid.compact-shard.v1":
            raise ValueError(f"Not a compact-shard manifest: {path}")
        case = data["case"]
        if case not in groups:
            raise ValueError(f"Unknown case {case!r}")
        start, count = checked_int(data["start"]), checked_int(data["count"])
        if not (0 <= start < 750 and 1 <= count <= 750-start):
            raise ValueError(f"Invalid interval in {path}")
        if data["order"] != 60 or data["mesh_steps"] != 750:
            raise ValueError("All shards must use order60 and750 mesh steps")
        if checked_int(data["mesh"]) != candidate["mesh"] or Q(data["h"]) != candidate["h"]:
            raise ValueError(f"Mesh/time mismatch in {path}")
        parameters = data.get("parameters")
        if not isinstance(parameters,dict) or set(parameters) != {"a","b","L"}:
            raise ValueError("Full assembly requires embedded parameters:{a,b,L}; legacy smoke manifests are not complete-path inputs")
        actual = tuple(Q(parameters[k]) for k in ("a","b","L"))
        if actual != expected_parameter(candidate,case) or Q(data["h"]) != actual[2]/750:
            raise ValueError(f"Wrong candidate/probe parameter in {path}")
        assembly = data["assembly"]
        if assembly not in ("bounded","fin_cases"):
            raise ValueError("Unknown compact stage-assembly mode")
        key = f"Shard_{case}_s{start:04}_n{count:04}_{assembly}"
        base = "CentroidEscape.CertificateShards." + key
        if data["key"] != key or data["namespace"] != base:
            raise ValueError("Shard identifier does not match its interval/case")
        names = []
        for item in data["modules"]:
            name = item["name"]
            if not IDENTIFIER.fullmatch(name) or not name.startswith("CentroidEscape."+key+"_"):
                raise ValueError("Invalid or foreign module name")
            if name in module_names:
                raise ValueError(f"Duplicate module name {name}")
            module_names.add(name)
            names.append(name)
        if not names or names[-1] != data["audit_module"] or data["root_module"] not in names:
            raise ValueError("Missing root or final audit module")
        theorem = data["checked_theorem"]
        if not IDENTIFIER.fullmatch(theorem) or not theorem.startswith(base+".") or not theorem.endswith(".checked"):
            raise ValueError("Invalid checked theorem identifier")
        first, last = fixed_vector(data["first_input"]), fixed_vector(data["last_endpoint"])
        groups[case].append({"manifest":str(path),"manifest_sha256":sha(raw),
                             "data":data,"start":start,"count":count,"first":first,"last":last,
                             "root_namespace":theorem[:-len(".checked")]})
    for k,case in enumerate(CASES):
        group = sorted(groups[case],key=lambda x:x["start"])
        next_index = 0
        previous = None
        for item in group:
            if item["start"] != next_index:
                kind = "overlap" if item["start"] < next_index else "gap"
                raise ValueError(f"{case}: {kind} at expected index{next_index}")
            if previous is not None and previous != item["first"]:
                raise ValueError(f"{case}: endpoint/input mismatch at index{next_index}")
            next_index += item["count"]
            previous = item["last"]
        if next_index != 750:
            raise ValueError(f"{case}: coverage ends at{next_index}, expected750")
        a,b,_ = expected_parameter(candidate,case)
        initial = (a,Q(0),Q(0),Q(1,4),b/16,Q(0),Q(0))
        if not all(abs(x-Q(c,candidate["mesh"])) <= Q(r,candidate["mesh"])
                   for x,(c,r) in zip(initial,group[0]["first"])):
            raise ValueError(f"{case}: first input does not contain the actual candidate initial point")
        if group[-1]["last"] != candidate["endpoints"][k]:
            raise ValueError(f"{case}: final endpoint differs from CandidateEndpointChecks")
        groups[case] = group
    # Reject cheap metadata/coverage errors before reading all 243 MB of sources.
    # Every source still gets verified before any proof source is generated.
    for group in groups.values():
        for record in group:
            directory = Path(record["manifest"]).parent
            for item in record["data"]["modules"]:
                source = (directory/item["source"]).resolve()
                if not source.is_relative_to(directory) or not source.is_file() or sha(source.read_bytes()) != item["sha256"]:
                    raise ValueError(f"Missing/mismatched source for {item['name']}")
    return groups


def generate(groups,candidate,outdir,force):
    ordered = [item for case in CASES for item in groups[case]]
    fingerprint = sha((candidate["sha256"]+"".join(x["manifest_sha256"] for x in ordered)).encode())[:16]
    key = "FullCandidate_v1_"+fingerprint
    base = "CentroidEscape.FullCertificates."+key
    outdir.mkdir(parents=True,exist_ok=True)
    manifest_path = outdir/"manifest.json"
    if manifest_path.exists() and json.loads(manifest_path.read_text())["key"] != key:
        raise ValueError("Output directory belongs to a different full-assembly input set")
    modules=[]

    def emit(part,source):
        name="CentroidEscape."+key+"_"+part
        relative=Path("sources")/Path(*name.split(".")).with_suffix(".lean")
        target=outdir/relative
        raw=source.encode("utf-8")
        if target.exists() and target.read_bytes()!=raw and not force:
            raise FileExistsError(f"Changed source requires --force: {target}")
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(raw)
        modules.append({"name":name,"source":relative.as_posix(),"sha256":sha(raw)})
        return name

    paths=[]
    for case_index,case in enumerate(CASES):
        blocks=[]
        for index,item in enumerate(groups[case]):
            data=item["data"]
            ns=f"{base}.{case}.Input{index:04}"
            original=item["root_namespace"]
            count=item["count"]
            source=f"""import CentroidEscape.CandidatePathAssembly
import {data['audit_module']}

namespace {ns}
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : {data['namespace']}.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : {data['namespace']}.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := {original}.inputData
noncomputable def endpointData : Vector FixedBall 7 := {original}.endpointData
noncomputable def stages : ℕ → FixedTaylorState := {original}.stages
theorem input_literal : inputData={vector_text(item['first'])} := by decide +kernel
theorem endpoint_literal : endpointData={vector_text(item['last'])} := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) {count} stages := by
  have h := {data['checked_theorem']}
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  {original}.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages {count}).coefficient 0 i=endpointData[i.val] :=
  {original}.terminalCoefficient i
attribute [irreducible] stages
end {ns}
"""
            module=emit(f"{case}_Input{index:04}",source)
            blocks.append({"namespace":ns,"module":module,"count":count})
        level=0
        while len(blocks)>1:
            merged=[]
            for pair in range(0,len(blocks),2):
                if pair+1==len(blocks):
                    merged.append(blocks[pair]); continue
                left,right=blocks[pair:pair+2]
                a,b=left["namespace"],right["namespace"]
                n,m=left["count"],right["count"]
                ns=f"{base}.{case}.Merge{level:03}_{pair//2:04}"
                source=f"""import {left['module']}
import {right['module']}

namespace {ns}
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem glue : {a}.endpointData={b}.inputData := by decide +kernel
theorem boundary : ∀ i : Fin 7,
    ({a}.stages {n}).coefficient 0 i=({b}.stages 0).coefficient 0 i := by
  intro i
  rw [{a}.terminalCoefficient,{b}.initialCoefficient,glue]
noncomputable def inputData : Vector FixedBall 7 := {a}.inputData
noncomputable def endpointData : Vector FixedBall 7 := {b}.endpointData
noncomputable def stages : ℕ → FixedTaylorState := appendTaylorStages {n} {a}.stages {b}.stages
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) {n+m} stages :=
  Order60SegmentValid.append {a}.checked {b}.checked boundary
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages {n} {a}.stages {b}.stages 0).coefficient 0 i={a}.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact {a}.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages {n+m}).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages {n} {a}.stages {b}.stages ({n}+{m})).coefficient 0 i={b}.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact {b}.terminalCoefficient i
attribute [irreducible] stages
end {ns}
"""
                module=emit(f"{case}_Merge{level:03}_{pair//2:04}",source)
                merged.append({"namespace":ns,"module":module,"count":n+m})
            blocks=merged;level+=1
        root=blocks[0]
        assert root["count"]==750
        ns=f"{base}.{case}.Path"
        original=root["namespace"]
        source=f"""import {root['module']}

namespace {ns}
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem first_input_contains : ∀ i : Fin 7,
    |rationalShootingInitial (candidateParameter {case_index}) i-
      ({original}.inputData[i.val].toRational CandidateEndpointChecks.mesh).center|≤
      ({original}.inputData[i.val].toRational CandidateEndpointChecks.mesh).radius := by decide +kernel
theorem initial_contains : ∀ i : Fin 7,
    |rationalShootingInitial (candidateParameter {case_index}) i-
      ((({original}.stages 0).coefficient 0 i).toRational CandidateEndpointChecks.mesh).center|≤
      ((({original}.stages 0).coefficient 0 i).toRational CandidateEndpointChecks.mesh).radius := by
  intro i
  rw [{original}.initialCoefficient]
  exact first_input_contains i
theorem terminal_matches : {original}.endpointData=CandidateEndpointChecks.endpointVectors {case_index} := by decide +kernel
theorem terminal_coefficients : ∀ i : Fin 7,
    ({original}.stages 750).coefficient 0 i=(CandidateEndpointChecks.endpointVectors {case_index})[i.val] := by
  intro i
  rw [{original}.terminalCoefficient,terminal_matches]
noncomputable def path : FiniteShootingPath := finiteShootingPathOfStages {original}.stages
theorem checked : path.check CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) (candidateParameter {case_index})=true :=
  (candidate_path_of_segment_checked {case_index} {original}.stages {original}.checked initial_contains terminal_coefficients).1
theorem endpoint_matches : path.endpoint CandidateEndpointChecks.mesh=CandidateEndpointChecks.endpointBall {case_index} :=
  (candidate_path_of_segment_checked {case_index} {original}.stages {original}.checked initial_contains terminal_coefficients).2
end {ns}
"""
        module=emit(f"{case}_Path",source)
        paths.append({"namespace":ns,"module":module})
    ns=base+".Certificate"
    source="".join(f"import {p['module']}\n" for p in paths)
    source+=f"""
namespace {ns}
open CentroidEscape CentroidEscape.MetricStability Set Real Filter
open scoped Topology ContDiff NNReal
noncomputable def paths : Fin 5 → FiniteShootingPath := ![{','.join(p['namespace']+'.path' for p in paths)}]
theorem paths_checked : ∀ k, (paths k).check CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) (candidateParameter k)=true := by
  intro k
  fin_cases k
"""+"".join(f"  · exact {p['namespace']}.checked\n" for p in paths)
    source+="theorem endpoints_match : ∀ k, (paths k).endpoint CandidateEndpointChecks.mesh=CandidateEndpointChecks.endpointBall k := by\n  intro k\n  fin_cases k\n"
    source+="".join(f"  · exact {p['namespace']}.endpoint_matches\n" for p in paths)
    source+=f"""
noncomputable def data : FivePathCertificateData := candidateCertificate paths
theorem checked : data.check=true := candidate_certificate_checked paths paths_checked endpoints_match
theorem smooth_FEF_centroid_escape :
    ∃ L : ℝ, 0<L ∧ ∃ γ : ℝ → ℝ → Plane,
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ=>γ q.1 q.2) {{q | -1/4<q.1}} ∧
      (∀t, Function.Periodic (γ t) (2*L) ∧ ContDiff ℝ ∞ (γ t)) ∧
      (∀t, 0≤t → ∀s, 0<‖deriv (γ t) s‖) ∧
      (∀t, 0≤t → ∀s, HasDerivAt (fun r=>γ r s)
        ((-curveElasticForce (γ t) s) • curveUnitNormal (γ t) s) t) ∧
      Tendsto (fun t=>curveCentroidX (2*L) (γ t)) atTop atTop :=
  checked_fivePathCertificate_yields_smooth_classical_FEF_escape data checked
end {ns}
"""
    final_module=emit("Certificate",source)
    audit=emit("Audit",f"""import {final_module}

#print axioms {ns}.smooth_FEF_centroid_escape
open Lean Elab Command in
run_cmd do
  let target := `{ns}.smooth_FEF_centroid_escape
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in (← collectAxioms target) do
    unless allowed.contains axiomName do
      throwError "Full certificate audit failed: {{target}} depends on {{axiomName}}"
  logInfo "Strict full certificate audit passed: unconditional smooth FEF centroid escape."
""")
    manifest={"schema":"centroid.full-certificate-assembly.v1","key":key,
              "status":"sources_generated_unverified","kernel_verified":False,
              "expected_steps":3750,"steps_per_case":750,"case_order":list(CASES),
              "generator_sha256":sha(Path(__file__).read_bytes()),
              "candidate_source":{"path":candidate["source"],"sha256":candidate["sha256"]},
              "input_shards":[{"path":x["manifest"],"sha256":x["manifest_sha256"],
                               "case":x["data"]["case"],"start":x["start"],"count":x["count"],
                               "audit_module":x["data"]["audit_module"]} for x in ordered],
              "modules":modules,"root_module":final_module,"audit_module":audit,
              "checked_theorem":ns+".checked","escape_theorem":ns+".smooth_FEF_centroid_escape",
              "required_generic_modules":["CentroidEscape.CandidatePathAssembly"],
              "scope":"Generated proof sources only. All shard and assembly modules must compile before the final theorem is claimed."}
    temporary=manifest_path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+"\n",encoding="utf-8")
    temporary.replace(manifest_path)
    return manifest_path


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest",type=Path,action="append")
    parser.add_argument("--manifest-list",type=Path)
    parser.add_argument("--shards-root",type=Path)
    parser.add_argument("--candidate-source",type=Path,required=True)
    parser.add_argument("--outdir","--output-root",dest="outdir",type=Path,required=True)
    parser.add_argument("--force",action="store_true")
    args=parser.parse_args()
    candidate=read_candidate(args.candidate_source.resolve())
    groups=validate_manifests(collect_paths(args),candidate)
    target=generate(groups,candidate,args.outdir.resolve(),args.force)
    print(f"Generated complete five-path proof sources, NOT yet kernel verified: {target}")


if __name__=="__main__":
    main()
