"""Verify a transferred shard's provenance and re-run its transitive Lean audit.

This consumes the output of a successful kernel-checking job in the same
workflow. It is not a replacement for compiling the arithmetic proofs.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inside(root, relative):
    target = (root / relative).resolve()
    if not target.is_relative_to(root) or not target.is_file():
        raise ValueError(f"Missing artifact member or path outside artifact: {relative}")
    return target


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--build-root", type=Path, required=True)
    parser.add_argument("--lean", default="lean")
    args = parser.parse_args()
    manifest_path = args.manifest.resolve()
    directory = manifest_path.parent
    result_path = directory / "reimport_report.json"
    result = {"status": "running", "reimport_audit_passed": False,
              "complete_five_path_certificate": False}
    result_path.write_text(json.dumps(result) + "\n")
    try:
        manifest = json.loads(manifest_path.read_text())
        report = json.loads((directory / "compile_report.json").read_text())
        if (manifest.get("schema") != "centroid.compact-shard.v1"
                or report.get("schema") != "centroid.compact-shard-build.v1"
                or report.get("key") != manifest["key"]
                or report.get("manifest_sha256") != digest(manifest_path)
                or report.get("status") != "checked"
                or report.get("shard_kernel_checked") is not True):
            raise ValueError("Artifact lacks a matching successful kernel-build report")
        modules = manifest["modules"]
        names = {m["name"] for m in modules}
        checked = {m["name"]: m for m in report["modules"]}
        if (len(names) != len(modules) or len(checked) != len(report["modules"])
                or names != set(checked) or not modules
                or modules[-1]["name"] != manifest["audit_module"]):
            raise ValueError("Missing or duplicate compiled modules")
        build = args.build_root.resolve()
        paths = [Path(p).resolve() for p in os.environ.get("LEAN_PATH", "").split(os.pathsep) if p]
        if build not in paths:
            paths.append(build)
        environment = os.environ.copy()
        environment["LEAN_PATH"] = os.pathsep.join(map(str, paths))
        lean = shutil.which(args.lean) or str(Path(args.lean).resolve())
        version = subprocess.check_output([lean, "--version"], env=environment, text=True).strip()
        if version != report["lean_version"]:
            raise ValueError("Transferred proofs use a different Lean toolchain")
        sources, binaries, imports = {}, {}, {}
        for item in modules:
            name = item["name"]
            if (not name.startswith("CentroidEscape." + manifest["key"] + "_")
                    or not re.fullmatch(r"[A-Za-z0-9_.]+", name)):
                raise ValueError(f"Invalid generated module name: {name}")
            evidence = checked[name]
            source = inside(directory, item["source"])
            binary = inside(directory, evidence["checked_olean"])
            if (evidence.get("exit_code") != 0 or digest(source) != item["sha256"]
                    or evidence["source_sha256"] != item["sha256"]
                    or digest(binary) != evidence["olean_sha256"]
                    or binary.stat().st_size != evidence["olean_bytes"]):
                raise ValueError(f"Changed source or compiled proof: {name}")
            log = inside(directory, evidence["log"])
            if digest(log) != evidence["log_sha256"]:
                raise ValueError(f"Changed compilation log: {name}")
            imported = re.findall(r"^import\s+([A-Za-z0-9_.]+)\s*$",
                                  source.read_text(encoding="utf-8"), re.MULTILINE)
            if set(imported) != set(evidence["import_hashes"]):
                raise ValueError(f"Incomplete dependency provenance: {name}")
            sources[name], binaries[name], imports[name] = source, binary, imported
        if checked[manifest["audit_module"]].get("audit_message_seen") is not True:
            raise ValueError("Original kernel job did not finish its strict audit")

        def resolved_import(name):
            relative = Path(*name.split(".")).with_suffix(".olean")
            return next((p / relative for p in paths if (p / relative).is_file()), None)

        # Check coherence of the entire dependency graph before restoring anything.
        for name, imported in imports.items():
            for dependency in imported:
                actual = binaries.get(dependency) or resolved_import(dependency)
                if actual is None or digest(actual) != checked[name]["import_hashes"][dependency]:
                    raise ValueError(f"Dependency differs from the checked build: {name} -> {dependency}")
        for name, binary in binaries.items():
            relative = Path(*name.split(".")).with_suffix(".olean")
            destination = build / relative
            first = resolved_import(name)
            if first is not None and first.resolve() != destination.resolve() and digest(first) != digest(binary):
                raise ValueError(f"Another LEAN_PATH entry shadows generated proof {name}")
        for name, binary in binaries.items():
            destination = build / Path(*name.split(".")).with_suffix(".olean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(binary, destination)
        for name, imported in imports.items():
            for dependency in imported:
                actual = resolved_import(dependency)
                if actual is None or digest(actual) != checked[name]["import_hashes"][dependency]:
                    raise ValueError(f"Restored dependency resolution changed: {dependency}")

        log_path = directory / "reimport_audit.log"
        command = [lean, "-M4096", "-j1", str(sources[manifest["audit_module"]])]
        resource_path = directory / "reimport_resources.txt"
        if os.name != "nt" and Path("/usr/bin/time").is_file():
            command = ["/usr/bin/time", "-v", "-o", str(resource_path)] + command
        started = time.monotonic()
        process = subprocess.run(command, env=environment, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
        log_path.write_text(process.stdout, encoding="utf-8")
        print(process.stdout, end="")
        passed = process.returncode == 0 and "Strict shard audit passed" in process.stdout
        result.update(status="checked" if passed else "failed", reimport_audit_passed=passed,
                      wall_ms=round(1000 * (time.monotonic() - started)), exit_code=process.returncode,
                      manifest_sha256=digest(manifest_path), modules=len(modules),
                      lean_version=version, log_sha256=digest(log_path))
        if not passed:
            raise RuntimeError("Transferred-shard audit did not pass")
        return 0
    except Exception as error:
        result.update(status="failed", reimport_audit_passed=False, error=repr(error))
        raise
    finally:
        result_path.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    raise SystemExit(main())
