"""Restore all 75 same-revision checked shards before a fresh full Lean audit.

Hash and provenance checks are not mathematical proof. The result explicitly
keeps full_certificate_proved false; compile_full_assembly.py must finish.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--artifacts-root", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--build-root", type=Path, required=True)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--lean", default="lean")
    args = parser.parse_args()
    root = args.output_root.resolve()
    root.mkdir(parents=True, exist_ok=True)
    report_path = root / "restore_report.json"
    index_path = root / "manifest-index.json"
    report = {"status": "running", "provenance_restored": False,
              "full_certificate_proved": False, "revision": args.revision, "shards": []}
    report_path.write_text(json.dumps(report) + "\n")
    # Invalidate an older successful index before any preflight or subprocess.
    index_path.write_text(json.dumps({"status": "incomplete", "manifests": [],
                                     "kernel_checked": False, "full_certificate_proved": False}) + "\n")
    try:
        plan = json.loads(args.plan.read_text())
        cases = ("center", "a_plus", "a_minus", "b_plus", "b_minus")
        expected = [(case, start, 50) for case in cases for start in range(0, 750, 50)]
        entries = plan["entries"]
        if (plan.get("schema") != "centroid.full-shard-plan.v1"
                or plan.get("revision") != args.revision
                or [(e["case"], e["start"], e["count"]) for e in entries] != expected):
            raise ValueError("Plan is not this revision's complete ordered 75-shard coverage")
        tools = Path(__file__).resolve().parent
        records = []
        for entry in entries:
            tag = f"{entry['case']}-s{entry['start']:04}-n0050"
            artifact_name = f"centroid-{args.revision}-{tag}"
            if (entry["tag"] != tag or entry["artifact_name"] != artifact_name
                    or entry["directory"] != f"shards/{tag}"):
                raise ValueError("Inconsistent or unsafe artifact location in plan")
            archive = args.artifacts_root.resolve() / artifact_name / "certificate.tar.xz"
            if not archive.is_file():
                raise FileNotFoundError(f"Missing checked shard artifact: {artifact_name}")
            directory = root / "shards" / tag
            subprocess.run([sys.executable, str(tools / "shard_artifact.py"), "unpack",
                            "--archive", str(archive), "--output-root", str(directory),
                            "--revision", args.revision], check=True)
            manifest_path = directory / "manifest.json"
            m = json.loads(manifest_path.read_text())
            if (m["case"], m["start"], m["count"]) != (entry["case"], entry["start"], 50):
                raise ValueError(f"Archive contains a different shard: {tag}")
            subprocess.run([sys.executable, str(tools / "reimport_shard.py"),
                            "--manifest", str(manifest_path), "--build-root", str(args.build_root.resolve()),
                            "--lean", args.lean, "--restore-only"], check=True)
            restored = json.loads((directory / "reimport_report.json").read_text())
            if restored.get("status") != "restored" or restored.get("provenance_verified") is not True:
                raise ValueError(f"Shard provenance was not restored: {tag}")
            records.append({"manifest": manifest_path.relative_to(root).as_posix(),
                            "sha256": digest(manifest_path), "case": m["case"],
                            "start": m["start"], "count": m["count"],
                            "checked_theorem": m["checked_theorem"]})
            report["shards"].append({"tag": tag, "manifest_sha256": digest(manifest_path),
                                     "archive_sha256": digest(archive)})
            report_path.write_text(json.dumps(report, indent=2) + "\n")
        index = {"schema": "centroid.generated-manifest-index.v1", "revision": args.revision,
                 "manifests": records, "provenance_restored": True,
                 "kernel_checked": False, "full_certificate_proved": False}
        index_path.write_text(json.dumps(index, indent=2) + "\n")
        report.update(status="restored", provenance_restored=True,
                      meaning="All checked shard artifacts restored. Full assembly and its Lean audit remain required.")
        print(json.dumps({"restored_shards": len(records), "full_certificate_proved": False}))
    except Exception as error:
        report.update(status="failed", provenance_restored=False, error=repr(error))
        raise
    finally:
        report_path.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
