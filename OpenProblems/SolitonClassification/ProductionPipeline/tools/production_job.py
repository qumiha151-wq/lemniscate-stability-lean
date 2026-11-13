"""Bind one cloud shard to a complete pinned proposal plan.

Preparation and verification do not check a theorem. The compile-pack command
uses the unchanged strict compiler and complete archive validator; it claims
only one checked shard, never the full two-path certificate.
"""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, sys
import production_compile_shard as compiler
import production_artifact as artifact
import plan_production_grid as planner

HERE = Path(__file__).resolve().parent
PREFIX = 'SolitonClassification.Rotating.'


def read_json(path):
    return json.loads(Path(path).read_bytes())


def expected_modules(key):
    names = []
    blocks = []
    for b in range(4):
        names.append(PREFIX + f'{key}B{b:02d}Nodes')
        names.extend(PREFIX + f'{key}L{j:04d}' for j in range(8*b, 8*b+8))
        root = PREFIX + f'{key}B{b:02d}Block'
        names.append(root)
        blocks.append(root)
    level = 0
    while len(blocks) > 1:
        next_blocks = []
        for pair in range(len(blocks)//2):
            seam, root = PREFIX + f'{key}Seam{level}_{pair}', PREFIX + f'{key}Join{level}_{pair}'
            names.extend([seam, root])
            next_blocks.append(root)
        blocks = next_blocks
        level += 1
    names.append(PREFIX + key + 'Audit')
    return names, blocks[0]


def bound_inputs(args):
    if not compiler.SHA.fullmatch(args.plan_sha256) or compiler.digest(args.plan) != args.plan_sha256:
        raise ValueError('Pinned trajectory plan hash differs')
    plan = read_json(args.plan)
    planner.validate_plan(plan, args.plan.resolve().parent)
    git_revision = bool(re.fullmatch(r'[0-9a-f]{40}', args.revision))
    if (not git_revision and not (args.allow_worktree and args.mode != 'compile-pack'
            and re.fullmatch(r'worktree-[A-Za-z0-9_-]+', args.revision))):
        raise ValueError('Production requires an exact Git revision')
    if plan['revision'] != args.revision:
        raise ValueError('Plan revision differs')
    if (plan['candidate_id'] != 'nonzero_rotation_minus56_over57'
            or plan['steps_per_sign'] != 4000 or plan['shard_size'] != 32
            or len(plan['jobs']) != 250):
        raise ValueError('Require the complete fixed 250-shard proposal plan')
    canonical = [(sign, start) for sign in (1, -1) for start in range(0, 4000, 32)]
    if [(j['sign'], j['start']) for j in plan['jobs']] != canonical:
        raise ValueError('Require canonical positive-then-negative job order')
    selected = [j for j in plan['jobs'] if j['key'] == args.key]
    if len(selected) != 1:
        raise ValueError('Shard key is absent or ambiguous')
    sources = {'seed': args.seed, 'candidate_initial': args.candidate_source,
               'planner': Path(planner.__file__),
               'proposal_arithmetic': Path(planner.arithmetic.__file__),
               'interval_arithmetic': Path(planner.reference.__file__),
               'shard_generator': HERE / 'generate_production_shard.py',
               'state_template': args.template_root / 'Block16Leaf08State.lean',
               'matrix_template': args.template_root / 'Block16Leaf08Matrix.lean'}
    if set(sources) != set(plan['source_fingerprints']):
        raise ValueError('Unexpected planner source set')
    for name, path in sources.items():
        expected = plan['source_fingerprints'][name]
        if path.is_symlink() or compiler.digest(path) != expected['sha256'] or path.stat().st_size != expected['bytes']:
            raise ValueError('Pinned source differs: ' + name)
    helpers = {p.name: compiler.digest(p) for p in [Path(__file__), Path(compiler.__file__), Path(artifact.__file__)]}
    return plan, selected[0], helpers


def verify_generated(args, plan, job):
    directory = args.output.resolve() / 'generated'
    manifest = read_json(directory / 'manifest.json')
    compiler.validate_manifest(manifest)
    for field in ('key', 'sign', 'start', 'count', 'input_node_sha256'):
        if manifest[field] != job[field]:
            raise ValueError('Generated shard job binding differs: ' + field)
    for field in ('candidate_id', 'candidate_hash', 'orders', 'mesh', 'step'):
        if manifest[field] != plan[field]:
            raise ValueError('Generated candidate binding differs: ' + field)
    expected_sources = {('generator' if k == 'shard_generator' else k): v
                        for k, v in plan['source_fingerprints'].items() if k != 'planner'}
    if (manifest['source_fingerprints'] != expected_sources
            or manifest['generator_sha256'] != expected_sources['generator']['sha256']):
        raise ValueError('Generated source provenance differs')
    names, root = expected_modules(job['key'])
    if ([m['name'] for m in manifest['modules']] != names or manifest['module_system'] is not True
            or manifest['root_module'] != root or manifest['checked_constant'] != root + '.certificate'
            or manifest['audit_module'] != names[-1]
            or manifest['audit_marker'] != f'Production_{job["key"]}_audit'
            or manifest['reset_bounds'] != {k: {'num': '1', 'den': str(10**55)} for k in ('state', 'matrix')}):
        raise ValueError('Unexpected fixed shard interface')
    coverage = [{'global_step': job['start']+i, 'state_module': PREFIX+f'{job["key"]}L{i:04d}',
                 'matrix_module': PREFIX+f'{job["key"]}L{i:04d}',
                 'header_module': PREFIX+f'{job["key"]}B{i//8:02d}Nodes'} for i in range(32)]
    if manifest['leaf_coverage'] != coverage:
        raise ValueError('Numerical leaf coverage differs')
    for item in manifest['modules']:
        path = compiler.confined(directory, item['source'])
        if path.is_symlink() or compiler.digest(path) != item['sha256']:
            raise ValueError('Generated Lean source changed')
        if compiler.header_imports(path) != item['imports']:
            raise ValueError('Generated header import list differs')
    expected_endpoint = compiler.confined(args.plan.resolve().parent, job['output_node'])
    endpoint = directory / 'output_node.json'
    if (manifest['output_node'] != 'output_node.json'
            or manifest['attachments'] != [{'source': 'output_node.json', 'sha256': compiler.digest(endpoint)}]
            or compiler.digest(expected_endpoint) != job['output_node_sha256']
            or read_json(endpoint) != read_json(expected_endpoint)):
        raise ValueError('Generated endpoint disagrees with pinned proposal')
    return manifest


def run(args):
    before = bound_inputs(args)
    plan, job, helpers = before
    output = args.output.resolve()
    if args.mode == 'prepare':
        if any(p.is_symlink() or (hasattr(p, 'is_junction') and p.is_junction())
               for p in [args.output, *args.output.parents]):
            raise ValueError('Output path contains a link or reparse junction')
        if output.exists() or args.output.is_symlink():
            raise ValueError('Prepare requires a nonexistent output directory')
        input_paths = [args.plan.parent, args.seed, args.candidate_source, args.template_root, HERE]
        if any(output.is_relative_to(p.resolve()) or p.resolve().is_relative_to(output) for p in input_paths):
            raise ValueError('Output overlaps pinned inputs or tools')
        output.mkdir(parents=True, exist_ok=False)
        command = [sys.executable, str(HERE / 'generate_production_shard.py'), '--key', job['key'],
                   '--count', '32', '--sign', str(job['sign']), '--module', '--output', str(output / 'generated'),
                   '--seed', str(args.seed.resolve()), '--candidate-source', str(args.candidate_source.resolve()),
                   '--template-root', str(args.template_root.resolve())]
        if job['input_node'] is not None:
            command += ['--input-node', str(compiler.confined(args.plan.resolve().parent, job['input_node']))]
        subprocess.run(command, check=True)
    manifest = verify_generated(args, plan, job)
    binding = {'schema': 'rotating.planned-job.v1', 'revision': args.revision, 'key': job['key'],
               'plan_sha256': args.plan_sha256,
               'manifest_sha256': compiler.digest(output / 'generated/manifest.json'),
               'proposed_endpoint_sha256': job['output_node_sha256'],
               'generated_endpoint_sha256': compiler.digest(output / 'generated/output_node.json'),
               'helper_sha256': helpers, 'kernel_checked': False, 'full_certificate_proved': False}
    if args.mode == 'prepare':
        if bound_inputs(args) != before:
            raise ValueError('Pinned preparation inputs changed')
        compiler.atomic_json(output / 'job_binding.json', binding)
    else:
        if read_json(output / 'job_binding.json') != binding:
            raise ValueError('Preparation receipt differs from actual pinned inputs')
    if args.mode == 'compile-pack':
        if (args.allow_worktree or args.seconds <= 0 or args.memory_mb <= 0
                or not compiler.SHA.fullmatch(args.base_lock_sha256)
                or compiler.digest(args.base_lock) != args.base_lock_sha256):
            raise ValueError('Wrong production base lock or resource limits')
        common_bytes = args.base_args.read_bytes()
        common = json.loads(common_bytes)
        if not isinstance(common, list) or any(not isinstance(x, str) for x in common):
            raise ValueError('Base arguments must be a string array')
        parser = argparse.ArgumentParser(add_help=False)
        parser.add_argument('--lean', required=True)
        parser.add_argument('--base-root', action='append', required=True)
        parsed = parser.parse_args(common)
        compiler.roots_from_args(parsed.base_root)
        archive = output / (job['artifact_name'] + '.tar.xz')
        if any(p.exists() for p in [output/'build', output/'generated/compile_report.json', archive, output/'checked_job.json']):
            raise ValueError('Check-and-pack requires fresh build and archive destinations')
        subprocess.run([sys.executable, str(Path(compiler.__file__)), 'compile',
                        '--manifest', str(output/'generated/manifest.json'), '--build-root', str(output/'build'),
                        '--base-lock', str(args.base_lock.resolve()), '--seconds', str(args.seconds),
                        '--memory-mb', str(args.memory_mb), *common], check=True)
        verify_generated(args, plan, job)
        artifact.pack(output/'generated/manifest.json', archive, args.revision)
        if (bound_inputs(args) != before or args.base_args.read_bytes() != common_bytes
                or compiler.digest(args.base_lock) != args.base_lock_sha256):
            raise ValueError('Pinned check-and-pack inputs changed')
        report = read_json(output/'generated/compile_report.json')
        if report['status'] != 'checked' or report['shard_kernel_checked'] is not True:
            raise ValueError('No successful strict shard check')
        compiler.atomic_json(output/'checked_job.json', dict(binding, kernel_checked=True,
            base_lock_sha256=args.base_lock_sha256, base_args_sha256=hashlib.sha256(common_bytes).hexdigest(),
            archive=archive.name, archive_sha256=compiler.digest(archive),
            compile_report_sha256=compiler.digest(output/'generated/compile_report.json')))
    elif bound_inputs(args) != before:
        raise ValueError('Pinned verification inputs changed')
    print(json.dumps({'mode': args.mode, 'key': job['key'], 'source_modules': len(manifest['modules']),
                      'kernel_checked': args.mode == 'compile-pack', 'full_certificate_proved': False}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['prepare', 'verify', 'compile-pack'])
    for name in ['plan', 'seed', 'candidate-source', 'template-root', 'output']:
        parser.add_argument('--'+name, type=Path, required=True)
    for name in ['plan-sha256', 'revision', 'key']:
        parser.add_argument('--'+name, required=True)
    parser.add_argument('--allow-worktree', action='store_true')
    parser.add_argument('--base-lock', type=Path)
    parser.add_argument('--base-lock-sha256')
    parser.add_argument('--base-args', type=Path)
    parser.add_argument('--seconds', type=int, default=600)
    parser.add_argument('--memory-mb', type=int, default=4096)
    args = parser.parse_args()
    if args.mode == 'compile-pack' and any(x is None for x in [args.base_lock, args.base_lock_sha256, args.base_args]):
        parser.error('compile-pack needs --base-lock, --base-lock-sha256, --base-args')
    run(args)


if __name__ == '__main__':
    main()
