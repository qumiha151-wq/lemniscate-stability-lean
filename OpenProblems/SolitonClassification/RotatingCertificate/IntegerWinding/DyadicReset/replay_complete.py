"""Regenerate the two exact winding-one grids and check the selected Lean target."""
import argparse
import gzip
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[2]
DEST = PROJECT / 'SolitonClassification' / 'Rotating'

def sha_lf(path):
    data = path.read_bytes()
    return sha256(data.replace(b'\r\n',b'\n')).hexdigest()

def script(name, *args):
    subprocess.run([sys.executable, str(HERE / name), *args], cwd=HERE, check=True)

def stage(src):
    dest = DEST / src.name
    if dest.exists():
        if sha_lf(src) != sha_lf(dest):
            raise ValueError(f'Existing source differs from generated source: {dest}')
        return
    with dest.open('xb') as target, src.open('rb') as original:
        shutil.copyfileobj(original,target)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('target', choices=['nodes','full'])
    parser.add_argument('--stage-only', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE/'GridReplay.json').read_bytes())
    for label, sign in [('plus','1'),('minus','-1')]:
        path = HERE / f'{label}4000.jsonl.gz'
        if not path.exists():
            script('reset_tape.py',sign,'4000')
        with gzip.open(path, 'rb') as tape:
            digest = sha256()
            for line in tape:
                digest.update(line.replace(b'\r\n',b'\n'))
        if digest.hexdigest() != manifest['tapes_lf'][label]:
            raise ValueError(f'Incorrect {label} dyadic trajectory: {path}')
    script('node_blocks.py')
    script('whole_tape.py')
    script('grid_inverses.py')
    for name in ['ResetGridClosure','ResetOnlyCells','ResetFinalImmersion']:
        base = HERE/'ReplayModules' if name=='ResetFinalImmersion' else DEST
        shutil.copyfile(base/(name+'.lean'),HERE/'fullassembly'/(name+'.lean'))
    groups = [(HERE/'nodeblocks','ResetNode[PM]*.lean'),
              (HERE/'fullassembly','ResetGrid*.lean'),
              (HERE/'fullassembly','ResetAllInverses*.lean'),
              (HERE/'fullassembly','ResetOnlyCells.lean')]
    target = 'ResetOnlyCells'
    if args.target == 'full':
        script('compact_blocks.py','full')
        groups += [(HERE/'cellblocks','ResetPacked*.lean'),
                   (HERE/'fullassembly','ResetTile*.lean'),
                   (HERE/'fullassembly','ResetComplete*.lean'),
                   (HERE/'fullassembly','ResetFinalImmersion.lean')]
        target = 'ResetFinalImmersion'
    for folder, pattern in groups:
        for src in sorted(folder.glob(pattern)):
            expected = manifest['generated_sources_lf'].get(src.name)
            if expected is None or sha_lf(src) != expected:
                raise ValueError(f'Unrecognized or mismatched generated input: {src.name}')
            stage(src)
    if not args.stage_only:
        subprocess.run(['lake','build','+SolitonClassification.Rotating.'+target],cwd=PROJECT,check=True)

if __name__ == '__main__':
    main()
