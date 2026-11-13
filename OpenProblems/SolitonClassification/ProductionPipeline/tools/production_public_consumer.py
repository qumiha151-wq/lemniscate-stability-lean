"""Fresh portable public-only consumption of one strictly checked module shard.

The complete original source/log/three-layer artifact bundle is validated and
retained. Only primary project oleans are copied into this consumer's input
tree. This is a separate Lean check, not a replacement for numerical checking.
No CPU or peak-memory measurements are inferred from wall time or Lean -M.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import time

import production_compile_shard as compiler
import production_artifact as artifact_tools


def positive_integer(text):
    value = int(text)
    if value <= 0:
        raise argparse.ArgumentTypeError('Require a positive integer')
    return value


def stop_owned_child(child):
    """Terminate only the child returned by this invocation's Popen call."""
    if child.poll() is None:
        child.terminate()
        try:
            child.wait(timeout=10)
        except subprocess.TimeoutExpired:
            child.kill()
            child.wait()
    return child.returncode


def validate_public_inputs(inputs, copies):
    expected = {Path(item['path']).relative_to(inputs).as_posix() for item in copies.values()}
    actual = set()
    for path in inputs.rglob('*'):
        if path.is_symlink():
            raise ValueError('Unexpected symlink in public inputs')
        if path.is_file():
            actual.add(path.relative_to(inputs).as_posix())
    if actual != expected:
        raise ValueError('Unexpected public input files or private/server sidecars')
    for item in copies.values():
        path = Path(item['path'])
        if path.stat().st_size != item['bytes'] or compiler.digest(path) != item['sha256']:
            raise ValueError('Public input bytes changed')


def consume(args):
    manifest_path = args.manifest.resolve()
    if manifest_path.name != 'manifest.json':
        raise ValueError('Require the canonical manifest.json from the checked bundle')
    directory = manifest_path.parent
    read = lambda name: compiler.confined(directory, name).read_bytes()
    originals = {name: read(name) for name in ['manifest.json', 'compile_report.json', 'base_lock.json']}
    initial_read = lambda name: originals[name] if name in originals else read(name)
    helpers = {str(Path(path).resolve()): compiler.digest(path)
               for path in [__file__, compiler.__file__, artifact_tools.__file__]}
    manifest, report, _, _ = artifact_tools.validate_bundle(initial_read)
    if (manifest.get('module_system') is not True
            or any(row['state_module'] != row['matrix_module'] for row in manifest['leaf_coverage'])):
        raise ValueError('Require a checked module shard with combined numerical leaves')
    lock = json.loads(originals['base_lock.json'])
    argument_bytes = args.base_args.read_bytes()
    common = json.loads(argument_bytes.decode('utf-8-sig'))
    if not isinstance(common, list) or any(not isinstance(x, str) for x in common):
        raise ValueError('Base arguments must be a JSON array of strings')
    base_parser = argparse.ArgumentParser(add_help=False)
    base_parser.add_argument('--lean', required=True)
    base_parser.add_argument('--base-root', action='append', required=True)
    base = base_parser.parse_args(common)
    roots = compiler.roots_from_args(base.base_root)
    lean, identity = compiler.lean_identity(base.lean)
    if identity != lock['lean'] or list(roots) != lock['root_order']:
        raise ValueError('External base/toolchain identity differs')
    output_root = args.output.resolve()
    if output_root == directory or output_root.is_relative_to(directory) or directory.is_relative_to(output_root):
        raise ValueError('Consumer output must be separate from the original checked bundle')
    for root in roots.values():
        if output_root.is_relative_to(root) or root.is_relative_to(output_root):
            raise ValueError('Consumer output must be separate from the locked base')
    if output_root.exists() and any(output_root.iterdir()):
        raise ValueError('Require a new or empty consumer output directory')
    print('Checking complete locked base before public consumption.', flush=True)
    if compiler.base_snapshot(roots) != lock['files']:
        raise ValueError('External base bytes differ')
    output_root.mkdir(parents=True, exist_ok=True)
    args.owned_output = output_root
    inputs = output_root / 'public_inputs'
    source_root = output_root / 'source'
    full_outputs = output_root / 'full_consumer_outputs'
    selected = {}
    generic_labels = set()
    for label in lock['root_order']:
        for path, expected in lock['files'].items():
            file_label, relative = path.split('/', 1)
            if file_label != label:
                continue
            if relative.startswith('SolitonClassification/') and relative.endswith('.olean'):
                name = relative[:-6].replace('/', '.')
                if name not in selected:
                    selected[name] = (compiler.confined(roots[label], relative), expected)
                    generic_labels.add(label)
    for item in report['modules']:
        if item['name'] in selected:
            raise ValueError('Generated module shadows a locked base module')
        selected[item['name']] = (compiler.confined(directory, item['checked_artifacts']['']), item['artifacts'][''])
    copies = {}
    for name, (path, expected) in selected.items():
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != expected['sha256'] or len(data) != expected['bytes']:
            raise ValueError('Selected primary olean changed')
        target = inputs / compiler.module_file(name)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        copies[name] = {'path': str(target), 'sha256': expected['sha256'], 'bytes': len(data)}
    validate_public_inputs(inputs, copies)
    external_roots = []
    for label, root in roots.items():
        if label in generic_labels:
            continue
        if (root / 'SolitonClassification').exists():
            raise ValueError('Project namespace available in an external fallback root')
        external_roots.append(root)
    key = manifest['key']
    name = 'SolitonClassification.Rotating.PublicConsumer_' + key
    if name in selected:
        raise ValueError('Consumer module collides with an imported module')
    relative = Path(*name.split('.')).with_suffix('.lean')
    source = source_root / relative
    source.parent.mkdir(parents=True, exist_ok=True)
    leaves = sorted({item['state_module'] for item in manifest['leaf_coverage']})
    numeric = [f'`{leaf}{suffix}' for leaf in leaves for suffix in ['State', 'Matrix']]
    source.write_text(f'''module
public import {manifest['root_module']}

namespace SolitonClassification.Rotating
set_option Elab.async false
public theorem public_shard_{key}_available :
    Nonempty (PolynomialPointGridBlock ({manifest['sign']}:ℝ) (Candidate.step:ℝ)
      (1/10^55) (1/10^55) {manifest['count']}) := ⟨{manifest['checked_constant']}⟩
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let numeric : Array Name := #[{','.join(numeric)}]
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    let userName := privateToUserName name
    if name != userName && numeric.any (·.isPrefixOf userName) then
      throwError "Imported private numerical declaration: {{name}}"
    if (`SolitonClassification.Rotating).isPrefixOf userName then
      for ax in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Public consumer audit failed: {{name}} depends on {{ax}}"
      count := count + 1
  logInfo m!"PUBLIC_SHARD_CONSUMER_CHECKED {key}: {{count}} declarations; standard axioms only; no private numerical declarations."
''', encoding='utf-8')
    setup = output_root / 'consumer.setup.json'
    compiler.atomic_json(setup, {'name': name, 'isModule': True, 'package': None,
        'plugins': [], 'dynlibs': [], 'options': {},
        'importArts': {n: [[item['path']], []] for n, item in copies.items()}})
    setup_value = json.loads(setup.read_text(encoding='utf-8'))
    if set(setup_value) != {'name', 'isModule', 'package', 'plugins', 'dynlibs', 'options', 'importArts'}:
        raise ValueError('Unexpected setup field')
    output = full_outputs / relative.with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    environment['LEAN_PATH'] = os.pathsep.join(map(str, [inputs, *external_roots]))
    log = output_root / 'consumer.log'
    source_hash, setup_hash = compiler.digest(source), compiler.digest(setup)
    metadata = {'schema': 'rotating.public-consumer.v1', 'status': 'prepared',
        'public_only_consumer_checked': False, 'key': key,
        'manifest_sha256': hashlib.sha256(originals['manifest.json']).hexdigest(),
        'compile_report_sha256': hashlib.sha256(originals['compile_report.json']).hexdigest(),
        'base_lock_sha256': hashlib.sha256(originals['base_lock.json']).hexdigest(),
        'base_args_sha256': hashlib.sha256(argument_bytes).hexdigest(), 'helper_sha256': helpers,
        'source_sha256': source_hash, 'setup_sha256': setup_hash, 'public_inputs': copies,
        'public_input_bytes': sum(item['bytes'] for item in copies.values()), 'private_project_input_files': 0,
        'lean': identity, 'wall_limit_seconds': args.seconds, 'lean_memory_limit_mb': args.memory_mb,
        'cpu_seconds': None, 'peak_memory_bytes': None,
        'resource_scope': 'Actual child wall/exit only; Lean -M is a limit, not a peak measurement.',
        'full_certificate_proved': False}
    report_path = output_root / 'public_consumer_report.json'
    compiler.atomic_json(report_path, metadata)
    command = [str(lean), '--setup', str(setup), '-M', str(args.memory_mb), '-j', '1', '-o', str(output), str(relative)]
    print('Starting fresh public-only Lean consumer.', flush=True)
    started = time.perf_counter()
    reason = 'completed'
    with log.open('wb') as stream:
        child = subprocess.Popen(command, cwd=source_root, env=environment, stdout=stream, stderr=subprocess.STDOUT)
        try:
            compiler.atomic_json(output_root / 'consumer_started.json', {'pid': child.pid,
                'command': command, 'source_sha256': source_hash, 'setup_sha256': setup_hash,
                'wall_limit_seconds': args.seconds, 'lean_memory_limit_mb': args.memory_mb})
            try:
                code = child.wait(timeout=args.seconds)
            except subprocess.TimeoutExpired:
                reason = 'terminated_at_wall_limit'
                code = stop_owned_child(child)
        except BaseException:
            code = stop_owned_child(child)
            compiler.atomic_json(output_root / 'child_cleanup.json', {'pid': child.pid, 'exit_code': code,
                'reason': 'exception cleanup limited to the current owned child'})
            raise
    result = {**metadata, 'status': 'lean_finished_provenance_pending', 'exit_code': code,
        'termination': reason, 'wall_seconds': time.perf_counter() - started,
        'log_sha256': compiler.digest(log), 'consumer_artifacts': compiler.bundle(output) if code == 0 else {}}
    compiler.atomic_json(report_path, result)
    if (code != 0 or reason != 'completed'
            or f'PUBLIC_SHARD_CONSUMER_CHECKED {key}' not in log.read_text(encoding='utf-8')):
        raise RuntimeError('Lean consumer did not pass; preserved child log/report are authoritative')
    if compiler.digest(source) != source_hash or compiler.digest(setup) != setup_hash:
        raise ValueError('Consumer source/setup changed')
    validate_public_inputs(inputs, copies)
    print('Checking locked base and original complete bundle after consumption.', flush=True)
    if compiler.base_snapshot(roots) != lock['files'] or compiler.lean_identity(base.lean)[1] != identity:
        raise ValueError('Locked external base/toolchain changed')
    artifact_tools.validate_bundle(read)
    for name, data in originals.items():
        if read(name) != data:
            raise ValueError('Original bundle header changed: ' + name)
    if args.base_args.read_bytes() != argument_bytes:
        raise ValueError('Base-argument binding changed')
    for path, expected in helpers.items():
        if compiler.digest(path) != expected:
            raise ValueError('Consumer/helper code changed')
    result.update(status='checked', public_only_consumer_checked=True)
    compiler.atomic_json(report_path, result)
    print(json.dumps({k: v for k, v in result.items() if k not in ['public_inputs', 'lean']}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--base-args', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seconds', type=positive_integer, default=120)
    parser.add_argument('--memory-mb', type=positive_integer, default=4096)
    args = parser.parse_args()
    try:
        consume(args)
    except BaseException as error:
        if hasattr(args, 'owned_output'):
            compiler.atomic_json(args.owned_output / 'consumer_failure.json', {
                'status': 'failed', 'error_type': type(error).__name__, 'error': str(error),
                'public_only_consumer_checked': False})
        raise


if __name__ == '__main__':
    main()
