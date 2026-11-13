"""Stage the sixteen frozen actual-flow modules; recheck only root and original audit.

This is a local integration check, not a from-scratch rebuild of already checked
leaves or a whole Mathlib-cache provenance audit. No remote operation is used.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

sys.stdout.reconfigure(encoding="utf-8")
ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OUT = HERE / "stage_v1"
PROJECT = OUT / "project"
BUILD = OUT / "build"
OLD = ROOT / "outputs/open-problems/LengthGrowth"
FLOW = ROOT / "work/length_flow_formal"
MATH = Path("C:/Users/17815/Desktop/论文/lean_deps/mathlib4-4.33.1")
LEAN = Path("C:/Users/17815/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean.exe")
OLD_BUILD = ROOT / "work/next_research/circle_backtracking_root_audit_v2"
CURVE_RESULT = FLOW / "curve_first_variation_build/1794550544485520800/result.json"
EXPECTED_CURVE = "3775cb0032910105af10a623b35402530c102e5568e379a769183f516fab72e8"

def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def info(path):
    p = Path(path)
    return {"sha256": digest(p), "bytes": p.stat().st_size}

def write_json(path, obj):
    Path(path).write_text(json.dumps(obj, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")

def imports(path):
    return re.findall(r"^(?:public )?import\s+([A-Za-z0-9_.]+)\s*$", Path(path).read_text(encoding="utf-8-sig"), re.M)

def snapshot(folder):
    return {p.relative_to(folder).as_posix(): info(p) for p in sorted(folder.rglob("*")) if p.is_file()}

# Exact checked sources whose successful evidence is a plain log.
KNOWN = {
    "IntrinsicCurve": ("C87069BEEFCE3A69CBE728FF3F36C85C3233B329D84582FD4915365311272766", "build/LengthGrowth/ActualFlow/IntrinsicCurve.olean", "check_intrinsic_06.log"),
    "SpatialPeriodicity": ("028EA07209B8675C7515B297C29D4ED5C100CF53BC3E72FDE415B23DDCF76009", "build/LengthGrowth/ActualFlow/SpatialPeriodicity.olean", "SpatialPeriodicity_check01.log"),
    "FamilyRegularity": ("336A39E7ECFEC57EF68163FC35FFE47A83B663393612D4F776611F73F37111F0", "build/LengthGrowth/ActualFlow/FamilyRegularity.olean", "FamilyRegularity_check05.log"),
    "FamilyPeriodicity": ("1BD69952C9A2105423B3E33914A01A58A5C9C8B2F23A40B191F012857C418DB7", "build/LengthGrowth/ActualFlow/FamilyPeriodicity.olean", "FamilyPeriodicity_check02.log"),
    "CompactParameterIntegral": ("A4FA2790570FF1600DC88DC167053A0D7643EEE7EDCFF2F82482092B1051C079", "compact_integral_build/LengthGrowth/ActualFlow/CompactParameterIntegral.olean", "CompactParameterIntegral_check02.log"),
    "JetGeometry": ("A37C4934EF97C44373FCC776173219FB35D26955F4FEE075F762D7C05A24F445", "build/LengthGrowth/ActualFlow/JetGeometry.olean", "JetGeometry_check03.log"),
    "FourJetForce": ("00D6F86BCE7E4FDD20F3E1F5D47E89B8F8DF1A3540128A6894EF58DF9F404F98", "build/LengthGrowth/ActualFlow/FourJetForce.olean", "FourJetForce_check03.log"),
}
REPORTS = {
    "MixedPartials": "mixed_partials_build/1794548685872452600/result.json",
    "PeriodicIntegration": "periodic_integration_build/1794549248415212300/result.json",
    "MaterialIntegrals": "material_integrals_build/1794549481996751500/result.json",
    "SpatialFirstVariation": "spatial_first_variation_build/1794549634563391800/result.json",
    "FamilyDerivatives": "family_derivatives_build/1794549982314638000/result.json",
    "FamilyIntegrals": "family_integrals_build/1794549904508879500/result.json",
    "CurveFirstVariation": str(CURVE_RESULT.relative_to(FLOW)),
    "ForwardGeometry": "forward_owned_build/ForwardGeometry/1794550599741113500/result.json",
    "ForwardDissipation": "forward_owned_build/ForwardDissipation/1794550768746585100/result.json",
}
ROLES = {
    "IntrinsicCurve": "Actual arbitrary-speed intrinsic geometry and stress derivative",
    "SpatialPeriodicity": "Periodicity of actual spatial fields",
    "MixedPartials": "Actual mixed-partial commutation on an open domain",
    "FamilyRegularity": "Position-only moving immersion and derived joint regularity",
    "FamilyDerivatives": "Derived metric, frame and curvature time variations",
    "FamilyPeriodicity": "Derived actual velocity periodicity and variation boundary terms",
    "PeriodicIntegration": "Periodic integration by parts for actual derivatives",
    "SpatialFirstVariation": "Spatial first-variation stress identities",
    "CompactParameterIntegral": "Differentiation of a compact spatial parameter integral",
    "MaterialIntegrals": "Actual weighted integrals and Cauchy-Schwarz bound",
    "FamilyIntegrals": "Time continuity and actual integral derivatives",
    "CurveFirstVariation": "Open-time first variations, normal FEF laws and actual secant estimate",
    "JetGeometry": "Actual first-through-fourth jets and two-jet curvature formula",
    "FourJetForce": "Actual four-jet force formula and arbitrary-filter continuity",
    "ForwardGeometry": "Actual forward spatial jets and initial-time integral continuity",
    "ForwardDissipation": "Initial-time dissipation/restart and actual conditional subsqrt growth",
}

def main():
    if OUT.exists():
        raise ValueError("Refusing to reuse an integration output directory")
    baseline = snapshot(OLD)
    before = {str(Path(__file__).resolve()): info(__file__), str(LEAN): info(LEAN)}
    curve = json.loads(CURVE_RESULT.read_text())
    assert curve["exit_code"] == 0 and curve["source_sha256"] == EXPECTED_CURVE
    assert curve["source_unchanged"] and curve["dependency_outputs_unchanged"]
    assert len(KNOWN) + len(REPORTS) == 16 and set(ROLES) == set(KNOWN) | set(REPORTS)
    checked_artifacts = {}
    def pin_artifact(path, sha):
        key = str(Path(path).resolve())
        assert checked_artifacts.get(key,sha.lower()) == sha.lower(), key
        checked_artifacts[key] = sha.lower()
    for manifest_name in ("IntrinsicCurveFrozenManifest.json", "SpatialPeriodicityFrozenManifest.json",
            "FamilyPeriodicityFrozenManifest.json", "FourJetForceFrozenManifest.json"):
        manifest = FLOW / manifest_name
        before[str(manifest)] = info(manifest)
        for row in json.loads(manifest.read_text(encoding="utf-8-sig"))["artifacts"]:
            pin_artifact(ROOT / row["path"], row["sha256"])
    pin_artifact(FLOW / KNOWN["FamilyRegularity"][1],
        "2A9AE1F6CE5A316867600B55389B4A1FDF0BB4F340EF041430793074E824245D")
    pin_artifact(FLOW / KNOWN["CompactParameterIntegral"][1],
        "6C1769C5967C159C1D0F3EA2EB7069528EF46D4C297013949A3DB65AF4167B79")
    pin_artifact(FLOW / "family_derivatives_build/1794549982314638000/stdout.txt",
        "9052AC296CCE38549DED3B97C6A980A7394F5729393F082BDDD3E7636C31F056")
    forward_manifest = FLOW / "ForwardEndpointFrozenManifest.json"
    assert digest(forward_manifest) == "ef2dfee0ff6f9560796356eafb336f91402e695e741cdaadcbe3d0685ebe5422"
    before[str(forward_manifest)] = info(forward_manifest)
    for module_row in json.loads(forward_manifest.read_text())["modules"]:
        for path,sha in module_row["artifacts"].items():
            pin_artifact(path,sha)
    for relative in REPORTS.values():
        report = FLOW / relative
        r = json.loads(report.read_text())
        assert r["exit_code"] == 0
        for path,sha in r.get("dependency_pins",{}).items():
            pin_artifact(path,sha)
        for path,sha in r.get("artifacts",{}).items():
            pin_artifact(report.parent / path,sha)
    sources = {name: FLOW / f"LengthGrowth/ActualFlow/{name}.lean" for name in ROLES}
    rows = {}
    for name, src in sources.items():
        if name in KNOWN:
            sha, obj, log = KNOWN[name]
            artifact, logpath, report = FLOW/obj, FLOW/log, None
            assert digest(src) == sha.lower(), name
        else:
            report = FLOW / REPORTS[name]
            r = json.loads(report.read_text())
            assert r["exit_code"] == 0 and r["source_unchanged"], name
            assert digest(src) == r["source_sha256"], name
            artifact = Path(r["argv"][r["argv"].index("-o")+1])
            logpath = report.parent / "stdout.txt"
            expected_log = r.get("stdout_sha256")
            if expected_log is None:
                expected_log = checked_artifacts[str(logpath.resolve())]
            assert digest(logpath) == expected_log, name
            assert not (report.parent / "stderr.txt").read_bytes(), name
            before[str(report)] = info(report)
        text = logpath.read_text(encoding="utf-8-sig")
        assert text.strip() and not re.search(r"\b(?:error|warning|sorryAx)\b", text), name
        assert digest(artifact) == checked_artifacts[str(artifact.resolve())], name
        for p in (src, artifact, logpath):
            before[str(p)] = info(p)
        rows[name] = {"module": f"LengthGrowth.ActualFlow.{name}", "role": ROLES[name],
            "source": str(src), **info(src), "artifact_origin": str(artifact),
            "artifact": info(artifact), "success_log": str(logpath),
            "success_log_sha256": digest(logpath), "imports": imports(src),
            "actual_leaf_recompiled_in_integration": False}
    # Topological order comes from the frozen actual source headers.
    ordered = []
    while len(ordered) < 16:
        choices = [n for n in sorted(rows) if n not in ordered and all(
            dep.rsplit(".",1)[1] in ordered for dep in rows[n]["imports"]
            if dep.startswith("LengthGrowth.ActualFlow."))]
        assert choices, "Cycle or missing actual-flow source"
        ordered.extend(choices)
    closure = set()
    def visit(name):
        if name in closure: return
        closure.add(name)
        for dep in rows[name]["imports"]:
            if dep.startswith("LengthGrowth.ActualFlow."):
                visit(dep.rsplit(".",1)[1])
    visit("ForwardDissipation")
    assert closure == set(rows)
    shutil.copytree(OLD, PROJECT)
    evidence = PROJECT / "ActualFlowEvidence"
    evidence.mkdir()
    target_sources = PROJECT / "LengthGrowth/ActualFlow"
    target_sources.mkdir()
    arts = {}
    for name in ordered:
        row = rows[name]
        shutil.copyfile(row["source"], target_sources/f"{name}.lean")
        shutil.copyfile(row["success_log"], evidence/f"{name}.success.log")
        obj = BUILD / "LengthGrowth/ActualFlow" / f"{name}.olean"
        obj.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(row["artifact_origin"], obj)
        arts[row["module"]] = [[str(obj)], []]
    # Preserve all eighteen prior mathematical leaves, including CircleConnection.
    old_report = json.loads((OLD_BUILD / "result.json").read_text())
    old_log = OLD_BUILD / "LengthGrowth_AxiomAudit.stdout.txt"
    assert "236 declarations" in old_log.read_text()
    shutil.copyfile(old_log, evidence / "Prior236.audit.log")
    old_sources = sorted((OLD / "LengthGrowth").glob("*.lean"))
    old_leaves = [p for p in old_sources if p.stem != "AxiomAudit"]
    assert len(old_leaves) == 18
    for src in old_leaves:
        original_obj = OLD_BUILD / "LengthGrowth" / (src.stem+".olean")
        if src.stem != "CircleConnectionBacktracking":
            assert digest(original_obj) == old_report["original_cached_dependency_pins"][original_obj.name]
        else:
            assert digest(src) == "672908a1d09c1e8695b846a734a69dc78d7ba9e179eb75d082d413762524ce25"
            assert digest(original_obj) == digest(ROOT / "work/next_research/circle_backtracking_lean/1794545917190929300/CircleConnectionBacktracking.olean")
        before[str(original_obj)] = info(original_obj)
        obj = BUILD / "LengthGrowth" / original_obj.name
        obj.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(original_obj, obj)
        arts[f"LengthGrowth.{src.stem}"] = [[str(obj)], []]
    # Official missing Mathlib cache artifacts were already built from unchanged official sources.
    symmetric_report = FLOW / "symmetric_dependency/build_v1/report.json"
    assert digest(symmetric_report) == "7ec7dae9256c3ca68d0519a323938eaeb5d1c5783565be5972f1fdb9ea39e7f4"
    sr = json.loads(symmetric_report.read_text())
    for module, layers in sr["importArts"].items():
        arts[module] = layers
        for group in layers:
            for path in group:
                before[path] = info(path)
    before[str(symmetric_report)] = info(symmetric_report)
    root = PROJECT / "LengthGrowth.lean"
    text = root.read_text()
    text = "import LengthGrowth.ActualFlow.ForwardDissipation\n" + text
    old = "secant bound from explicitly assumed scalar derivative and dissipation\nhypotheses. The free-elastic-flow PDE, its variation formulae, and the\nunrestricted quarter-power upper bound are not formalized here."
    new = "secant bound from scalar derivative and dissipation hypotheses. The new\nActualFlow chain derives those laws from a genuine smooth periodic position\nfamily satisfying the actual normal FEF equation on an open time domain:\nL' = integral k F ds and E' = -integral F^2 ds. Actual spatial-jet continuity\nextends the integral and secant laws to initial time. For a global forward\nclassical normal FEF with the stated initial regularity it proves\nL(t)/sqrt(t) tends to zero. It proves neither global existence for arbitrary\ninitial curves nor the unrestricted quarter-power upper bound."
    assert old in text
    root.write_text(text.replace(old,new), encoding="utf-8")
    status = PROJECT / "STATUS.txt"
    text = status.read_text()
    old = "ScalarDissipation.lean derives a secant estimate from genuine derivative\nhypotheses and proves a conditional fourth-power length bound. The geometric\nPDE identities and the assumed normalized-energy bound are not formalized\nor proved here. This does not solve unrestricted quarter-power growth."
    new = "ScalarDissipation.lean derives a secant estimate from derivative hypotheses\nand proves a conditional fourth-power length bound. The new sixteen-module\nActualFlow chain derives length and energy laws and the actual secant bound\nfrom the position PDE, including the initial endpoint using actual spatial-jet\ncontinuity. For a global forward classical normal FEF with the stated initial\nregularity it proves L(t)/sqrt(t) tends to zero. Global existence for arbitrary\ninitial curves, a uniform normalized-energy bound, and unrestricted\nquarter-power growth remain unproved. See ActualFlowScope.txt and\nActualFlowEvidence."
    assert old in text
    status.write_text(text.replace(old,new), encoding="utf-8")
    shutil.copyfile(HERE / "README.txt", PROJECT / "README.txt")
    shutil.copyfile(HERE / "ActualFlowScope.txt", PROJECT / "ActualFlowScope.txt")
    write_json(evidence / "Modules.json", {"schema":"actual-flow-forward16-v1",
        "topological_order":[rows[n]["module"] for n in ordered],
        "new_modules":[rows[n] for n in ordered], "prior_mathematical_leaves":18,
        "prior_audited_declarations":236, "forward_extension_included":True})
    # Freeze the staged sources before the two actual integration commands.
    staged_before = snapshot(PROJECT)
    build_before = snapshot(BUILD)
    write_json(OUT / "selected_inputs_before.json", before)
    write_json(OUT / "staged_project_before.json", staged_before)
    env = dict(os.environ)
    dependencies = [MATH / ".lake/build/lib/lean"] + sorted(
        p / ".lake/build/lib/lean" for p in (MATH/".lake/packages").iterdir()
        if (p/".lake/build/lib/lean").is_dir())
    env["LEAN_PATH"] = os.pathsep.join(map(str, dependencies))
    checks = []
    for module, src in [("LengthGrowth", root), ("LengthGrowth.AxiomAudit", PROJECT/"LengthGrowth/AxiomAudit.lean")]:
        setup = {"name":module,"isModule":False,"package":None,"plugins":[],"dynlibs":[],"options":{},"importArts":dict(arts)}
        setup_path = OUT / (module+".setup.json")
        write_json(setup_path, setup)
        output = BUILD / Path(*module.split(".")).with_suffix(".olean")
        argv = [str(LEAN),"--setup",str(setup_path),"-M","4096","-j","1","-o",str(output),str(src)]
        print("Compiling "+module, flush=True)
        start = time.monotonic()
        p = subprocess.run(argv, cwd=PROJECT, env=env, capture_output=True, timeout=300)
        stdout, stderr = evidence/(module+".stdout.txt"), evidence/(module+".stderr.txt")
        stdout.write_bytes(p.stdout); stderr.write_bytes(p.stderr)
        row = {"module":module,"argv":argv,"exit_code":p.returncode,"seconds":time.monotonic()-start,
            "source":info(src),"setup":info(setup_path),"stdout":info(stdout),"stderr":info(stderr)}
        checks.append(row)
        write_json(OUT / "progress.json",checks)
        print(p.stdout.decode("utf-8",errors="replace"), end="", flush=True)
        print(p.stderr.decode("utf-8",errors="replace"), end="", flush=True)
        assert p.returncode == 0 and not re.search(rb"\b(?:error|warning|sorryAx)\b",p.stdout+p.stderr)
        row["output"] = info(output)
        arts[module] = [[str(output)], []]
    audit_text = (evidence/"LengthGrowth.AxiomAudit.stdout.txt").read_text()
    audit_count = int(re.search(r"Length-growth audit passed: (\d+) declarations; standard axioms only", audit_text).group(1))
    assert audit_count > 236
    assert snapshot(OLD) == baseline, "Published workspace changed during staging"
    assert all(info(p)==record for p,record in before.items()), "Selected source/artifact changed"
    assert all(info(PROJECT/p)==record for p,record in staged_before.items()), "Staged input changed"
    assert all(info(BUILD/p)==record for p,record in build_before.items()), "Reused project object changed"
    verification = {"schema":"actual-flow16-project-integration-v1","status":"PASS",
        "actual_integration_calls":checks,"reused_leaves":34,"new_leaf_recompilations":0,
        "original_audit_source_unchanged":True,"prior236_preserved_by_exact_leaf_reuse":True,
        "actual_recursive_audit_count":audit_count,"allowed_axioms":["propext","Classical.choice","Quot.sound"],
        "selected_inputs_before_after_equal":True,"published_workspace_before_after_equal":True,
        "staged_sources_before_after_equal":True,"reused_artifacts_before_after_equal":True,
        "whole_mathlib_cache_snapshot_performed":False,"explicit_importArts_count_for_root":36,
        "ordinary_mathlib_roots":list(map(str,dependencies)),"no_project_LEAN_PATH":True,
        "forward_initial_extension_included":True,"actual_conditional_subsqrt_proved":True,
        "arbitrary_initial_global_existence_proved":False,"general_quarter_power_growth_proved":False,
        "runner_sha256":digest(__file__),"source_project_sha256":digest(OUT/"staged_project_before.json"),
        "selected_input_manifest_sha256":digest(OUT/"selected_inputs_before.json")}
    write_json(evidence/"Integration.json",verification)
    shutil.copyfile(OUT/"selected_inputs_before.json",evidence/"SelectedInputs.json")
    shutil.copyfile(__file__,evidence/"prepare_and_check.py")
    final = snapshot(PROJECT)
    entries = []
    for path, data in final.items():
        if baseline.get(path) == data: continue
        entries.append({"path":path,"repository_path":"OpenProblems/LengthGrowth/"+path,
            "local_path":str(PROJECT/path), **data,
            "action":"update" if path in baseline else "add",
            "previous_sha256":baseline.get(path,{}).get("sha256")})
    assert not any(path.startswith("LengthGrowth/") and path in baseline and final[path]!=baseline[path] for path in final)
    write_json(OUT/"entries_manifest.json",{"schema":"actual-flow16-publication-entries-v1",
        "publication_performed":False,"entries":entries,"entry_count":len(entries),
        "total_entry_bytes":sum(e["bytes"] for e in entries),"project_inventory":final})
    print(json.dumps({"status":"PASS","audit_count":audit_count,"entries":len(entries),
        "entries_manifest_sha256":digest(OUT/"entries_manifest.json")}),flush=True)

if __name__ == "__main__":
    main()
