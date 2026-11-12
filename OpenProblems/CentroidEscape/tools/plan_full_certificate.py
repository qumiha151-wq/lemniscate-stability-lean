"""Prepare the complete 75-shard matrix; never invokes Lean compilation.

Optional source generation uses existing native JSON, then checks metadata,
coverage and every adjacent ball boundary across all five paths. None of
these static checks is represented as a Lean proof or kernel verification.
"""
from pathlib import Path
from fractions import Fraction
import argparse
import hashlib
import json
import subprocess
import sys

CASES = ("center", "a_plus", "a_minus", "b_plus", "b_minus")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--data-root", type=Path)
    parser.add_argument("--generate-sources", action="store_true")
    args = parser.parse_args()
    if not args.revision or (args.generate_sources and args.data_root is None):
        raise ValueError("Revision and, for source generation, native data root are required")
    root = args.output_root.resolve()
    root.mkdir(parents=True, exist_ok=True)
    generator = Path(__file__).with_name("generate_compact_shard.py")
    entries = []
    for case in CASES:
        for start in range(0, 750, 50):
            tag = f"{case}-s{start:04}-n0050"
            entries.append({"index": len(entries), "case": case, "start": start, "count": 50,
                            "tag": tag, "directory": f"shards/{tag}",
                            "manifest": f"shards/{tag}/manifest.json",
                            "artifact_name": f"centroid-{args.revision}-{tag}"})
    plan = {"schema": "centroid.full-shard-plan.v1", "revision": args.revision,
            "paths": list(CASES), "steps_per_path": 750, "shard_steps": 50,
            "shards": 75, "lean_processes_per_shard": 2, "lean_threads_per_process": 1,
            "memory_mb_per_process": 6144, "max_parallel_shards": 8,
            "initial_final_assembly_memory_mb": 12288,
            "generator_sha256": digest(generator), "entries": entries,
            "kernel_checked": False, "full_certificate_proved": False}
    (root / "plan.json").write_text(json.dumps(plan, indent=2) + "\n")
    matrix = {"include": [{k: e[k] for k in ("index", "case", "start", "count", "tag", "artifact_name")} for e in entries]}
    (root / "matrix.json").write_text(json.dumps(matrix, separators=(",", ":")) + "\n")
    if args.generate_sources:
        index = []
        parameters = {}
        previous_endpoint = {}
        common = None
        source_bytes, modules = 0, 0
        for entry in entries:
            directory = root / entry["directory"]
            subprocess.run([sys.executable, str(generator), "--data-root", str(args.data_root.resolve()),
                            "--case", entry["case"], "--start", str(entry["start"]), "--count", "50",
                            "--output-root", str(directory)], check=True)
            manifest_path = directory / "manifest.json"
            m = json.loads(manifest_path.read_text())
            if (m["case"], m["start"], m["count"]) != (entry["case"], entry["start"], 50):
                raise ValueError("Generated manifest interval mismatch")
            geometry = (m["mesh"], m["h"], m["order"], m["mesh_steps"])
            if common is None:
                common = geometry
            elif common != geometry:
                raise ValueError("Case/shard integration geometry differs")
            case = entry["case"]
            if case in parameters and parameters[case] != m["parameters"]:
                raise ValueError("Parameters changed within a path")
            parameters[case] = m["parameters"]
            if case in previous_endpoint and previous_endpoint[case] != m["first_input"]:
                raise ValueError(f"Native boundary differs at {case}/{entry['start']}")
            previous_endpoint[case] = m["last_endpoint"]
            source_bytes += sum((directory / item["source"]).stat().st_size for item in m["modules"])
            modules += len(m["modules"])
            index.append({"manifest": entry["manifest"], "sha256": digest(manifest_path),
                          "case": case, "start": entry["start"], "count": 50,
                          "checked_theorem": m["checked_theorem"]})
        center = {key: Fraction(value) for key, value in parameters["center"].items()}
        delta = Fraction(1, 10**25)
        for case in CASES:
            expected = dict(center)
            if case != "center":
                coordinate, sign = case.split("_")
                expected[coordinate] += delta if sign == "plus" else -delta
            if {key: Fraction(value) for key, value in parameters[case].items()} != expected:
                raise ValueError(f"Wrong prescribed probe parameters: {case}")
        record = {"schema": "centroid.generated-manifest-index.v1", "revision": args.revision,
                  "manifests": index, "source_bytes": source_bytes, "modules": modules,
                  "native_boundary_equalities_checked": 5 * 749,
                  "metadata_probe_delta": str(delta), "static_consistency_checked": True,
                  "kernel_checked": False, "full_certificate_proved": False}
        (root / "manifest-index.json").write_text(json.dumps(record, indent=2) + "\n")
        print(json.dumps({"generated_shards": 75, "source_bytes": source_bytes,
                          "modules": modules, "kernel_compilations_started": 0}))
    print(f"Prepared {root / 'plan.json'} and {root / 'matrix.json'}; no Lean compilation was started.")


if __name__ == "__main__":
    main()
