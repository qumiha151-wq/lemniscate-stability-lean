"""Hash-checked tar.xz transport for one successful kernel-checking job.

This is a transport/build-provenance check, not a substitute for Lean.
After unpacking, reimport_shard.py must check the exact core dependency
hashes; a fresh shard audit or the final complete transitive audit is still
required. Full flow certification remains
the responsibility of the final assembled, kernel-checked theorem.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import io
import json
import re
import tarfile

HEADER = "shard-archive.json"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def allowed(name):
    p = PurePosixPath(name)
    return (bool(re.fullmatch(r"[A-Za-z0-9_./-]+", name)) and not p.is_absolute()
            and ".." not in p.parts and p.as_posix() == name
            and (name in ("manifest.json", "compile_report.json")
                 or p.parts[0] in ("sources", "checked_oleans", "logs")))


def inside(root, name):
    if not allowed(name):
        raise ValueError(f"Unexpected artifact path: {name}")
    path = (root / name).resolve()
    if not path.is_relative_to(root):
        raise ValueError(f"Artifact path leaves output directory: {name}")
    return path


def validate_bundle(read):
    manifest_bytes, report_bytes = read("manifest.json"), read("compile_report.json")
    m, r = json.loads(manifest_bytes), json.loads(report_bytes)
    if (m.get("schema") != "centroid.compact-shard.v1"
            or r.get("schema") != "centroid.compact-shard-build.v1"
            or r.get("key") != m["key"] or r.get("status") != "checked"
            or r.get("shard_kernel_checked") is not True
            or r.get("manifest_sha256") != sha(manifest_bytes)):
        raise ValueError("No matching successful kernel-build report")
    modules = m["modules"]
    names = {item["name"] for item in modules}
    evidence = {item["name"]: item for item in r["modules"]}
    if (not modules or len(names) != len(modules) or len(evidence) != len(r["modules"])
            or names != set(evidence) or modules[-1]["name"] != m["audit_module"]
            or m["root_module"] not in names
            or evidence[m["audit_module"]].get("audit_message_seen") is not True):
        raise ValueError("Incomplete module set or unfinished audit")
    required = {"manifest.json", "compile_report.json"}
    external = {}
    for item in modules:
        name, record = item["name"], evidence[item["name"]]
        if not name.startswith("CentroidEscape." + m["key"] + "_") or not re.fullmatch(r"[A-Za-z0-9_.]+", name):
            raise ValueError(f"Module outside shard: {name}")
        if record.get("exit_code") != 0 or record.get("source_sha256") != item["sha256"]:
            raise ValueError(f"Failed/stale module evidence: {name}")
        source = read(item["source"])
        binary = read(record["checked_olean"])
        log = read(record["log"])
        if (sha(source) != item["sha256"] or sha(binary) != record["olean_sha256"]
                or len(binary) != record["olean_bytes"] or sha(log) != record["log_sha256"]):
            raise ValueError(f"Changed source, proof or log: {name}")
        imported = re.findall(r"^import\s+([A-Za-z0-9_.]+)\s*$", source.decode("utf-8"), re.MULTILINE)
        if set(imported) != set(record["import_hashes"]):
            raise ValueError(f"Incomplete dependency hashes: {name}")
        for dependency in imported:
            expected = record["import_hashes"][dependency]
            if dependency in names:
                if expected != evidence[dependency]["olean_sha256"]:
                    raise ValueError(f"Mixed generated dependencies: {name} -> {dependency}")
            elif dependency in external and external[dependency] != expected:
                raise ValueError(f"Mixed core versions: {dependency}")
            else:
                external[dependency] = expected
        required.update((item["source"], record["checked_olean"], record["log"]))
    return m, r, required, external


def pack(manifest_path, archive, revision):
    manifest_path = manifest_path.resolve()
    if manifest_path.name != "manifest.json":
        raise ValueError("The shard manifest must be named manifest.json")
    root = manifest_path.parent
    read = lambda name: inside(root, name).read_bytes()
    m, r, required, external = validate_bundle(read)
    for record in r["modules"]:
        resource = str(PurePosixPath(record["log"]).with_suffix(".resource.txt"))
        if inside(root, resource).is_file():
            required.add(resource)
    files = sorted(required)
    if len({name.casefold() for name in files}) != len(files):
        raise ValueError("Case-insensitive duplicate artifact paths")
    records = []
    archive = archive.resolve()
    archive.parent.mkdir(parents=True, exist_ok=True)
    temporary = archive.with_name(archive.name + ".tmp")
    with tarfile.open(temporary, "w:xz", preset=6) as tar:
        for name in files:
            data = read(name)
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.mtime = len(data), 0o644, 0
            tar.addfile(info, io.BytesIO(data))
            records.append({"path": name, "bytes": len(data), "sha256": sha(data)})
        metadata = {"schema": "centroid.shard-artifact.v1", "revision": revision,
                    "key": m["key"], "case": m["case"], "start": m["start"], "count": m["count"],
                    "manifest_sha256": sha(read("manifest.json")),
                    "compile_report_sha256": sha(read("compile_report.json")),
                    "lean_version": r["lean_version"], "compiler_sha256": r.get("compiler_sha256"),
                    "external_import_hashes": external, "files": records,
                    "full_certificate_proved": False,
                    "meaning": "Transport of one successful partial-segment build; reimport/audit still required."}
        encoded = json.dumps(metadata, sort_keys=True).encode()
        info = tarfile.TarInfo(HEADER)
        info.size, info.mode, info.mtime = len(encoded), 0o644, 0
        tar.addfile(info, io.BytesIO(encoded))
    temporary.replace(archive)
    result = {"archive": str(archive), "archive_bytes": archive.stat().st_size,
              "archive_sha256": sha(archive.read_bytes()), "unpacked_bytes": sum(x["bytes"] for x in records),
              "files": len(records), "key": m["key"], "revision": revision}
    archive.with_name(archive.name + ".index.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


def unpack(archive, root, revision, max_unpacked_mb):
    root = root.resolve()
    root.mkdir(parents=True, exist_ok=True)
    result = {"status": "running", "transport_verified": False,
              "reimport_audit_passed": False, "full_certificate_proved": False}
    result_path = root / "unpack_report.json"
    result_path.write_text(json.dumps(result) + "\n")
    try:
        with tarfile.open(archive, "r:xz") as tar:
            members = tar.getmembers()
            names = [member.name for member in members]
            if len(names) != len(set(names)) or len(names) != len({n.casefold() for n in names}):
                raise ValueError("Duplicate archive member paths")
            if any(member.type not in (tarfile.REGTYPE, tarfile.AREGTYPE) for member in members):
                raise ValueError("Nonregular archive members are forbidden")
            if HEADER not in names:
                raise ValueError("Missing shard archive metadata")
            metadata = json.load(tar.extractfile(HEADER))
            if metadata.get("schema") != "centroid.shard-artifact.v1" or metadata.get("revision") != revision:
                raise ValueError("Wrong artifact schema or checkout revision")
            records = metadata["files"]
            expected = {record["path"] for record in records}
            if len(expected) != len(records) or set(names) != expected | {HEADER}:
                raise ValueError("Archive members differ from the hash manifest")
            if sum(record["bytes"] for record in records) > max_unpacked_mb * 1024 * 1024:
                raise ValueError("Artifact exceeds the configured unpacked-size budget")
            verified = {}
            for record in records:
                name = record["path"]
                inside(root, name)  # Validate canonical confined paths before writes.
                member = tar.getmember(name)
                if member.size != record["bytes"]:
                    raise ValueError(f"Changed member size: {name}")
                data = tar.extractfile(member).read()
                if sha(data) != record["sha256"]:
                    raise ValueError(f"Changed member bytes: {name}")
                verified[name] = data
            m, r, required, external = validate_bundle(lambda name: verified[name])
            if (m["key"] != metadata["key"]
                    or (m["case"], m["start"], m["count"]) != (metadata["case"], metadata["start"], metadata["count"])
                    or sha(verified["manifest.json"]) != metadata["manifest_sha256"]
                    or sha(verified["compile_report.json"]) != metadata["compile_report_sha256"]
                    or external != metadata["external_import_hashes"] or r["lean_version"] != metadata["lean_version"]
                    or r.get("compiler_sha256") != metadata.get("compiler_sha256")):
                raise ValueError("Archive provenance does not match its checked contents")
            old_manifest = root / "manifest.json"
            if old_manifest.exists() and json.loads(old_manifest.read_text()).get("key") != m["key"]:
                raise ValueError("Output directory already contains another shard")
            # Every member and the proof dependency graph have been validated.
            for name, data in verified.items():
                target = inside(root, name)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
        result.update(status="verified", transport_verified=True, revision=revision,
                      key=m["key"], files=len(verified), archive_sha256=sha(archive.read_bytes()))
        print(json.dumps(result))
    except Exception as error:
        result.update(status="failed", transport_verified=False, error=repr(error))
        raise
    finally:
        result_path.write_text(json.dumps(result, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="mode", required=True)
    make = sub.add_parser("pack")
    make.add_argument("--manifest", type=Path, required=True)
    make.add_argument("--archive", type=Path, required=True)
    make.add_argument("--revision", required=True)
    restore = sub.add_parser("unpack")
    restore.add_argument("--archive", type=Path, required=True)
    restore.add_argument("--output-root", type=Path, required=True)
    restore.add_argument("--revision", required=True)
    restore.add_argument("--max-unpacked-mb", type=int, default=512)
    args = parser.parse_args()
    if not args.revision:
        raise ValueError("A nonempty pinned revision is required")
    if args.mode == "pack":
        pack(args.manifest, args.archive, args.revision)
    else:
        if args.max_unpacked_mb <= 0:
            raise ValueError("Positive unpacked-size budget required")
        unpack(args.archive, args.output_root, args.revision, args.max_unpacked_mb)


if __name__ == "__main__":
    main()
