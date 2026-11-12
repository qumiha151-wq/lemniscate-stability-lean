"""Transfer only the freshly built centroid modules between jobs of one run.

The artifact is a build cache, not a mathematical certificate. The producing
job must compile and audit the checked-in sources before invoking this tool.
Mathlib and the Lean toolchain remain separate, pinned dependencies.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import io
import json
import tarfile


def digest(data):
    return hashlib.sha256(data).hexdigest()


def allowed_name(name):
    p = PurePosixPath(name)
    return (not p.is_absolute() and ".." not in p.parts and "\\" not in name
            and (p.parts[0] == "CentroidEscape"
                 or (len(p.parts) == 1 and p.name.startswith("CentroidEscape.olean"))))


def pack(build_root, archive, revision):
    root = Path(build_root).resolve()
    files = sorted(p for p in root.rglob("*")
                   if p.is_file() and allowed_name(p.relative_to(root).as_posix()))
    if not (root / "CentroidEscape.olean").is_file() or not files:
        raise ValueError("Missing compiled centroid root")
    records = []
    archive = Path(archive)
    archive.parent.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive, "w:xz", preset=6) as tar:
        for path in files:
            name = path.relative_to(root).as_posix()
            data = path.read_bytes()
            records.append({"path": name, "bytes": len(data), "sha256": digest(data)})
            info = tarfile.TarInfo(name)
            info.size = len(data)
            info.mode = 0o644
            tar.addfile(info, io.BytesIO(data))
        manifest = json.dumps({"revision": revision, "files": records}, sort_keys=True).encode()
        info = tarfile.TarInfo("core-manifest.json")
        info.size = len(manifest)
        tar.addfile(info, io.BytesIO(manifest))
    print(json.dumps({"archive": str(archive), "bytes": archive.stat().st_size,
                      "files": len(records), "revision": revision}))


def unpack(build_root, archive, revision):
    root = Path(build_root).resolve()
    root.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive, "r:xz") as tar:
        members = tar.getmembers()
        names = [m.name for m in members]
        if len(names) != len(set(names)):
            raise ValueError("Duplicate core archive paths")
        manifest_member = tar.getmember("core-manifest.json")
        if not manifest_member.isfile():
            raise ValueError("Invalid core manifest member")
        manifest = json.load(tar.extractfile(manifest_member))
        if manifest["revision"] != revision:
            raise ValueError("Core archive revision differs from this checkout")
        records = manifest["files"]
        expected = {r["path"] for r in records}
        if len(expected) != len(records) or set(names) != expected | {"core-manifest.json"}:
            raise ValueError("Core archive and manifest disagree")
        verified = []
        for record in records:
            name = record["path"]
            if not allowed_name(name):
                raise ValueError(f"Unexpected core path: {name}")
            member = tar.getmember(name)
            if not member.isfile() or member.size != record["bytes"]:
                raise ValueError(f"Invalid core member: {name}")
            data = tar.extractfile(member).read()
            if digest(data) != record["sha256"]:
                raise ValueError(f"Changed core member: {name}")
            target = (root / name).resolve()
            if not target.is_relative_to(root):
                raise ValueError(f"Path leaves build directory: {name}")
            verified.append((target, data))
        # Validate every member before writing any restored module.
        for target, data in verified:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    print(json.dumps({"restored_files": len(verified), "revision": revision}))


def main():
    p = argparse.ArgumentParser()
    p.add_argument("mode", choices=("pack", "unpack"))
    p.add_argument("build_root", type=Path)
    p.add_argument("archive", type=Path)
    p.add_argument("--revision", required=True)
    args = p.parse_args()
    if not args.revision:
        raise ValueError("A nonempty checkout revision is required")
    (pack if args.mode == "pack" else unpack)(args.build_root, args.archive, args.revision)


if __name__ == "__main__":
    main()
