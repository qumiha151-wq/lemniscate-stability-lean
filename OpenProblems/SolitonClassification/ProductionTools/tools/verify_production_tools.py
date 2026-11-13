"""Verify the separate transport-only source package and unchanged core project."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, re

CORE_SHA = '2c252cf849e22e027ca2630b836e5227b8ff8390cf45f36a6b467db64580c924'
FROZEN = {
    'production_core_artifact.py': '1ead0d5ced187dbf2d9847f7b08ea7f7a1e8931fe88ce8461c284fa277c73ea6',
    'production_compile_shard.py': 'f0abd2db3d6b8db32707d33e8ebb8a6aaee7da0c6f2332c9c4da8e931c64310b',
    'production_artifact.py': 'ddb448165391a04ab1ffcd9e4b572f9945f29fab5e1fa6ec981adad4b56323b5',
    'production_environment.py': 'e51d7452662a39353a774242c60873ca5099deaad75db04c7ae083b68a7b74ac',
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def relative(name):
    p = PurePosixPath(name)
    if (not re.fullmatch('[A-Za-z0-9_./-]+', name) or p.is_absolute()
            or any(x in ('.', '..') for x in p.parts) or p.as_posix() != name):
        raise ValueError('Unsafe package member')
    return p


def verify(package, project=None):
    package = package.resolve()
    raw = (package/'ProductionToolsInventory.json').read_bytes()
    record = json.loads(raw)
    if (record.get('schema') != 'rotating.production-tools-source.v1'
            or record.get('source_only') is not True or record.get('full_certificate_proved') is not False
            or record['core_inventory_sha256'] != CORE_SHA or record['frozen_tools'] != FROZEN):
        raise ValueError('Wrong source-only transport package identity')
    actual = set()
    for p in package.rglob('*'):
        if p.is_symlink() or not p.resolve().is_relative_to(package):
            raise ValueError('Package link or escape')
        if p.is_file():
            actual.add(p.relative_to(package).as_posix())
    if actual != set(record['files']) | {'ProductionToolsInventory.json'}:
        raise ValueError('Unlisted/missing transport package file')
    for name, expected in record['files'].items():
        data = (package/relative(name)).read_bytes()
        if len(data) != expected['bytes'] or digest(data) != expected['sha256']:
            raise ValueError('Transport source bytes changed: '+name)
        if '.olean' in name or name.endswith(('.dll', '.so', '.exe')):
            raise ValueError('Source package contains compiled artifacts')
    for name, expected in FROZEN.items():
        if digest((package/'tools'/name).read_bytes()) != expected:
            raise ValueError('A frozen production helper changed')
    if digest((package/'workflow/rotating-core-transfer.yml').read_bytes()) != record['workflow_sha256']:
        raise ValueError('Workflow copy changed')
    if project is not None:
        project = project.resolve()
        inventory_raw = (project/'ModuleProductionSourceInventory.json').read_bytes()
        if digest(inventory_raw) != CORE_SHA:
            raise ValueError('The original 108-file core inventory changed')
        inventory = json.loads(inventory_raw)
        if len(inventory['files']) != 108 or len(inventory['topological_modules']) != 88:
            raise ValueError('Wrong core inventory/module count')
        for name, expected in inventory['files'].items():
            path = project/relative(name)
            if path.is_symlink() or not path.resolve().is_relative_to(project):
                raise ValueError('Core source link/escape')
            data = path.read_bytes()
            if len(data) != expected['bytes'] or digest(data) != expected['sha256']:
                raise ValueError('Core source byte changed: '+name)
        found = {p.relative_to(project).as_posix() for p in (project/'SolitonClassification').rglob('*.lean')}
        if found != {m['source'] for m in inventory['topological_modules']}:
            raise ValueError('Core source glob changed')
    return digest(raw)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--package', type=Path, required=True)
    p.add_argument('--project', type=Path)
    args = p.parse_args()
    print('PRODUCTION_TOOLS_SOURCE_VERIFIED='+verify(args.package, args.project))


if __name__ == '__main__':
    main()
