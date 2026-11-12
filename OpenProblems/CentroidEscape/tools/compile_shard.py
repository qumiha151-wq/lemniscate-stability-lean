"""Compile and audit a generated shard, with explicit per-module evidence.

Run under `lake env python3` in CI so LEAN_PATH contains the audited core.
This script does not trust native data, generated source, or a JSON pass bit.
Only successful Lean kernel checking AND the generated audit count as success.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import traceback

COMPILER_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
REPORT_PATH = None
LIVE_REPORT = None


def atomic_report(path, report):
    temporary = path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def windows_memory(process):
    if os.name != "nt":
        return None, None
    import ctypes
    from ctypes import wintypes

    class Counters(ctypes.Structure):
        _fields_ = [("cb", wintypes.DWORD), ("faults", wintypes.DWORD)] + [
            (name, ctypes.c_size_t) for name in (
                "peak_working", "working", "peak_paged", "paged",
                "peak_nonpaged", "nonpaged", "pagefile", "peak_pagefile", "private"
            )
        ]

    counters = Counters()
    counters.cb = ctypes.sizeof(counters)
    read = ctypes.WinDLL("psapi").GetProcessMemoryInfo
    read.argtypes = [wintypes.HANDLE, ctypes.c_void_p, wintypes.DWORD]
    read.restype = wintypes.BOOL
    if read(int(process._handle), ctypes.byref(counters), counters.cb):
        return counters.peak_working, counters.private
    return None, None


def main():
    global REPORT_PATH, LIVE_REPORT
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--lean", default="lean", help="Single Lean executable; invoke this script via lake env")
    parser.add_argument("--build-root", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=1, help="Independent Lean processes; each uses -j 1")
    parser.add_argument("--memory-mb", type=int, default=4096)
    parser.add_argument("--resume-verified", action="store_true", help="Reuse only hash-matching prior successful module results")
    args = parser.parse_args()
    manifest_path = args.manifest.resolve()
    directory = manifest_path.parent
    directory.mkdir(parents=True, exist_ok=True)
    report_path = directory / "compile_report.json"
    old_report = {}
    if args.resume_verified and report_path.exists():
        try:
            old_report = json.loads(report_path.read_text())
        except (ValueError, OSError):
            pass  # Invalid cache evidence forces fresh checking.
    REPORT_PATH = report_path
    LIVE_REPORT = {"schema": "centroid.compact-shard-build.v1", "status": "running",
                   "shard_kernel_checked": False, "compiler_sha256": COMPILER_SHA256,
                   "modules": []}
    atomic_report(REPORT_PATH, LIVE_REPORT)  # Clear stale success before ANY preflight.
    if args.jobs < 1 or args.memory_mb < 1:
        raise ValueError("Positive job count and memory cap required")
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != "centroid.compact-shard.v1":
        raise ValueError("Unknown shard-manifest schema")
    key = manifest["key"]
    if not re.fullmatch(r"Shard_[A-Za-z0-9_]+", key):
        raise ValueError("Invalid shard key")
    prefix = "CentroidEscape." + key + "_"
    modules = manifest["modules"]
    names = {item["name"] for item in modules}
    if len(names) != len(modules) or not modules or modules[-1]["name"] != manifest["audit_module"]:
        raise ValueError("Duplicate modules or missing final audit")
    if manifest["root_module"] not in names:
        raise ValueError("Missing shard root module")
    by_name, dependencies, sources = {}, {}, {}
    imports = {}
    for item in modules:
        name = item["name"]
        if not name.startswith(prefix) or not re.fullmatch(r"[A-Za-z0-9_.]+", name):
            raise ValueError("Module outside this shard's namespace")
        source = (directory / item["source"]).resolve()
        if not source.is_relative_to(directory) or not source.is_file():
            raise ValueError("Missing source or path outside shard output")
        if digest(source) != item["sha256"]:
            raise ValueError(f"Source hash mismatch: {source}")
        text = source.read_text(encoding="utf-8")
        imported = re.findall(r"^import\s+([A-Za-z0-9_.]+)\s*$", text, re.MULTILINE)
        by_name[name], sources[name], imports[name] = item, source, imported
        dependencies[name] = set(imported) & names

    build = args.build_root.resolve()
    build.mkdir(parents=True, exist_ok=True)
    logs = directory / "logs"
    logs.mkdir(exist_ok=True)
    checked = directory / "checked_oleans"
    checked.mkdir(exist_ok=True)
    environment = os.environ.copy()
    search_paths = [Path(p).resolve() for p in environment.get("LEAN_PATH", "").split(os.pathsep) if p]
    if build not in search_paths:
        search_paths.append(build)  # Preserve mathlib-first order in the local environment.
    environment["LEAN_PATH"] = os.pathsep.join(map(str, search_paths))
    environment["LC_ALL"] = "C"
    lean = shutil.which(args.lean) or str(Path(args.lean).resolve())
    if not Path(lean).is_file():
        raise FileNotFoundError(f"Lean executable not found: {args.lean}")
    version = subprocess.check_output([lean, "--version"], env=environment, text=True).strip()

    def olean_path(name):
        return build / Path(*name.split(".")).with_suffix(".olean")

    def import_hashes(name):
        hashes = {}
        for imported in imports[name]:
            relative = Path(*imported.split(".")).with_suffix(".olean")
            path = next((root / relative for root in search_paths if (root / relative).is_file()), None)
            if path is None:
                raise FileNotFoundError(f"Missing audited dependency {imported} for {name}")
            if imported in names and path.resolve() != olean_path(imported).resolve():
                raise ValueError(f"Generated dependency shadowed by another LEAN_PATH entry: {imported}")
            hashes[imported] = digest(path)
            if imported in names:
                produced = results.get(imported)
                if not produced or produced.get("exit_code") != 0 or hashes[imported] != produced.get("olean_sha256"):
                    raise ValueError(f"Generated import does not match this run's produced hash: {imported}")
        return hashes

    previous = {}
    if args.resume_verified and old_report.get("key") == key and old_report.get("lean_version") == version:
        previous = {item["name"]: item for item in old_report.get("modules", []) if item.get("exit_code") == 0}
    report = {
        "schema": "centroid.compact-shard-build.v1", "key": key,
        "manifest_sha256": digest(manifest_path), "lean_version": version,
        "compiler_sha256": COMPILER_SHA256,
        "jobs": args.jobs, "memory_mb_per_process": args.memory_mb,
        "lean_threads_per_process": 1, "shard_kernel_checked": False,
        "status": "running", "modules": [],
        "axioms_allowed": ["propext", "Classical.choice", "Quot.sound"],
        "meaning": "Finite Taylor segment checked; no complete ODE or shooting-root claim.",
    }
    LIVE_REPORT = report
    abort = threading.Event()
    print_lock = threading.Lock()
    results = {}
    started = time.monotonic()

    def save():
        report["modules"] = [results[item["name"]] for item in modules if item["name"] in results]
        report["wall_ms"] = round((time.monotonic() - started) * 1000)
        atomic_report(report_path, report)

    def run_module(name):
        item, source = by_name[name], sources[name]
        if digest(source) != item["sha256"]:
            raise ValueError(f"Source changed during compilation: {name}")
        deps = import_hashes(name)
        output = olean_path(name)
        output.parent.mkdir(parents=True, exist_ok=True)
        prior = previous.get(name)
        if name != manifest["audit_module"] and prior and prior.get("source_sha256") == item["sha256"] and prior.get("import_hashes") == deps and output.is_file() and digest(output) == prior.get("olean_sha256"):
            result = dict(prior)
            result["reused_verified"] = True
        else:
            log_path = logs / (name.split(".")[-1] + ".log")
            resource_path = logs / (name.split(".")[-1] + ".resource.txt")
            descriptor, temporary_name = tempfile.mkstemp(prefix=".shard-", suffix=".olean", dir=output.parent)
            os.close(descriptor)
            temporary_output = Path(temporary_name)
            temporary_output.unlink()  # This script's unique empty placeholder, never an old proof.
            command = [lean, "-M", str(args.memory_mb), "-j", "1", "-o", str(temporary_output), str(source)]
            timed = sys.platform.startswith("linux") and Path("/usr/bin/time").is_file()
            if timed:
                command = ["/usr/bin/time", "-v", "-o", str(resource_path)] + command
            flags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
            begin = time.monotonic()
            peak_resident, sampled_private = 0, 0
            audit_seen = False
            with log_path.open("w", encoding="utf-8") as log:
                process = subprocess.Popen(command, env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                           text=True, encoding="utf-8", errors="replace", creationflags=flags,
                                           start_new_session=(os.name == "posix"))

                def read_output():
                    nonlocal audit_seen
                    for line in process.stdout:
                        log.write(line)
                        log.flush()
                        if "Strict shard audit passed" in line:
                            audit_seen = True
                        with print_lock:
                            print(f"[{name.split('_')[-1]}] {line.rstrip()}", flush=True)

                reader = threading.Thread(target=read_output, daemon=True)
                reader.start()
                while process.poll() is None:
                    resident, private = windows_memory(process)
                    peak_resident = max(peak_resident, resident or 0)
                    sampled_private = max(sampled_private, private or 0)
                    if abort.is_set():
                        try:
                            if os.name == "posix":
                                os.killpg(process.pid, signal.SIGTERM)
                            else:
                                process.terminate()
                        except ProcessLookupError:
                            pass
                    time.sleep(0.1)
                reader.join()
                code = process.wait()
            elapsed = round((time.monotonic() - begin) * 1000)
            if timed and resource_path.exists():
                match = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", resource_path.read_text())
                if match:
                    peak_resident = 1024 * int(match.group(1))
            if code == 0 and (not temporary_output.is_file() or temporary_output.stat().st_size == 0 or
                              (name == manifest["audit_module"] and not audit_seen)):
                code = 97
            if code == 0:
                temporary_output.replace(output)
            elif temporary_output.exists():
                temporary_output.unlink()
            result = {
                "name": name, "source_sha256": item["sha256"], "import_hashes": deps,
                "exit_code": code, "wall_ms": elapsed, "peak_resident_bytes": peak_resident or None,
                "sampled_peak_private_bytes": sampled_private or None,
                "log": log_path.relative_to(directory).as_posix(), "log_sha256": digest(log_path),
                "reused_verified": False, "audit_message_seen": audit_seen,
            }
            if code == 0:
                result.update(olean_sha256=digest(output), olean_bytes=output.stat().st_size)
        if result["exit_code"] == 0:
            destination = checked / Path(*name.split(".")).with_suffix(".olean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(output, destination)
            result["checked_olean"] = destination.relative_to(directory).as_posix()
        with print_lock:
            print(f"MODULE {name} EXIT={result['exit_code']} WALL_MS={result['wall_ms']} RESIDENT={result.get('peak_resident_bytes')}", flush=True)
        return result

    save()
    pending = [item["name"] for item in modules]
    done, active = set(), {}
    failure = None
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        while pending or active:
            if not abort.is_set():
                ready = [name for name in pending if dependencies[name] <= done]
                for name in ready[:max(0, args.jobs - len(active))]:
                    pending.remove(name)
                    active[executor.submit(run_module, name)] = name
            if not active:
                if pending and failure is None:
                    failure = "Unresolved or cyclic module dependencies"
                break
            finished, _ = wait(active, return_when=FIRST_COMPLETED)
            for future in finished:
                name = active.pop(future)
                try:
                    result = future.result()
                except Exception as error:
                    result = {"name": name, "exit_code": 98, "error": repr(error)}
                results[name] = result
                if result["exit_code"] == 0:
                    done.add(name)
                else:
                    failure = f"Module failed: {name}"
                    abort.set()
                save()
    success = failure is None and done == names and results[manifest["audit_module"]].get("audit_message_seen", False)
    report["status"] = "checked" if success else "failed"
    report["shard_kernel_checked"] = success
    if failure:
        report["failure"] = failure
    save()
    print(f"SHARD_KERNEL_CHECKED={str(success).lower()} REPORT={report_path}", flush=True)
    return 0 if success else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        if REPORT_PATH is not None:
            failed = LIVE_REPORT or {}
            failed.update(status="failed", shard_kernel_checked=False, failure=repr(error),
                          compiler_sha256=COMPILER_SHA256)
            atomic_report(REPORT_PATH, failed)
        traceback.print_exc()
        raise SystemExit(1)
