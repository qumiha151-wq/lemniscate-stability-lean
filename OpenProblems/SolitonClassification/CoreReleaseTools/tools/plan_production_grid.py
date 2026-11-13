"""Propose exact finite-shard checkpoints for both signed 42/22 paths.

This is an untrusted data planner, not a proof checker. Its checkpoints allow
independent cloud jobs to propose their own sources; all finite checks and
every inter-shard seam must subsequently be proved by Lean. Original sources
and the candidate seed are read-only. No compilation or upload occurs here.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import time

import propose_grid42x22 as arithmetic
import reference


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')


def ranges(steps, size):
    if isinstance(steps, bool) or not isinstance(steps, int) or not 1 <= steps <= 4000:
        raise ValueError('Require 1..4000 steps per sign')
    if isinstance(size, bool) or not isinstance(size, int) or not 1 <= size <= 32:
        raise ValueError('Require 1..32 steps per independent shard')
    return [(start, min(size, steps - start)) for start in range(0, steps, size)]


def checkpoint(index, sign, state, matrix, candidate_hash, step):
    return {'index': index, 'sign': sign, 'mesh': str(arithmetic.S),
            'candidate_hash': candidate_hash, 'orders': {'state': 42, 'matrix': 22},
            'step': {'num': str(step.numerator), 'den': str(step.denominator)},
            'state_exact_rational': [[v.numerator, v.denominator] for v in state],
            'matrix_integer_columns': matrix}


def validate_plan(plan, directory):
    """Check partition/metadata identity; this does not prove a numerical seam."""
    jobs = plan['jobs']
    if (plan['schema'] != 'rotating.production-plan.v1' or plan['kernel_checked'] is not False
            or plan['inter_shard_seams_proved'] is not False or len(jobs) > 256):
        raise ValueError('Wrong plan schema/status')
    if (plan['orders'] != {'state': 42, 'matrix': 22} or plan['mesh'] != str(arithmetic.S)
            or plan['full_path_steps_per_sign'] != 4000
            or plan['candidate_hash'] != plan['source_fingerprints']['candidate_initial']['sha256']):
        raise ValueError('Wrong fixed protocol or candidate binding')
    if not re.fullmatch(r'(?:[0-9a-f]{40}|worktree-[A-Za-z0-9_-]+)', plan['revision']):
        raise ValueError('Noncanonical revision label')
    if any(type(j[k]) is not int for j in jobs for k in ('start', 'count', 'sign')):
        raise ValueError('Noninteger shard range/sign')
    expected = ranges(plan['steps_per_sign'], plan['shard_size'])
    names = [j['key'] for j in jobs]
    if len(names) != len(set(names)):
        raise ValueError('Duplicate job key')
    for sign in (1, -1):
        signed = [j for j in jobs if j['sign'] == sign]
        if [(j['start'], j['count']) for j in signed] != expected:
            raise ValueError('Missing, overlapping or reordered signed coverage')
        previous = None
        for j in signed:
            tag = 'p' if sign == 1 else 'm'
            if (j['key'] != f'R{tag.upper()}{j["start"]:04d}'
                    or j['output_node'] != f'checkpoints/{tag}_{j["start"] + j["count"]:04d}.json'
                    or j['artifact_name'] != f'rotating-{plan["revision"]}-{tag}-{j["start"]:04d}-{j["count"]:04d}'):
                raise ValueError('Noncanonical job/checkpoint name')
            if j['input_node'] != previous:
                raise ValueError('Checkpoint chain does not match partition')
            node_path = directory / j['output_node']
            if node_path.is_symlink() or not node_path.resolve().is_relative_to(directory.resolve()):
                raise ValueError('Checkpoint escapes plan directory')
            if sha(node_path) != j['output_node_sha256']:
                raise ValueError('Changed output proposal')
            node = json.loads(node_path.read_text(encoding='utf-8-sig'))
            if (node['index'] != j['start'] + j['count'] or node['sign'] != sign
                    or node['candidate_hash'] != plan['candidate_hash']
                    or node['orders'] != plan['orders'] or node['step'] != plan['step']
                    or node['mesh'] != plan['mesh']):
                raise ValueError('Checkpoint metadata mismatch')
            if previous is not None and sha(directory / previous) != j['input_node_sha256']:
                raise ValueError('Changed input proposal')
            if previous is None and j['input_node_sha256'] is not None:
                raise ValueError('Unexpected initial checkpoint hash')
            if len(node['state_exact_rational']) != 6 or len(node['matrix_integer_columns']) != 6:
                raise ValueError('Wrong state/matrix shape')
            for numerator, denominator in node['state_exact_rational']:
                if denominator <= 0 or (arithmetic.Q(numerator, denominator) * arithmetic.S).denominator != 1:
                    raise ValueError('Checkpoint state is not on the exact integer mesh')
            if any(len(col) != 6 or any(type(x) is not int for x in col)
                   for col in node['matrix_integer_columns']):
                raise ValueError('Wrong matrix columns')
            previous = j['output_node']
    if len(jobs) != 2 * len(expected):
        raise ValueError('Unexpected sign or extra job')


def build(args):
    partition = ranges(args.steps_per_sign, args.shard_size)
    if 2 * len(partition) > 256:
        raise ValueError('This bounded plan permits at most256 independent jobs; use a larger shard size')
    if not re.fullmatch(r'(?:[0-9a-f]{40}|worktree-[A-Za-z0-9_-]+)', args.revision):
        raise ValueError('Use an actual Git revision, or an explicitly worktree-prefixed local label')
    directory = args.output.resolve()
    if directory.exists() and any(directory.iterdir()):
        raise ValueError('Output directory must be new or empty')
    directory.mkdir(parents=True, exist_ok=True)
    args._owned_output = True
    sources = {'seed': args.seed.resolve(), 'candidate_initial': args.candidate_source.resolve(),
               'planner': Path(__file__).resolve(), 'proposal_arithmetic': Path(arithmetic.__file__).resolve(),
               'interval_arithmetic': Path(reference.__file__).resolve(),
               'shard_generator': Path(__file__).with_name('generate_production_shard.py').resolve(),
               'state_template': (args.template_root / 'Block16Leaf08State.lean').resolve(),
               'matrix_template': (args.template_root / 'Block16Leaf08Matrix.lean').resolve()}
    fingerprints = {key: {'sha256': sha(path), 'bytes': path.stat().st_size}
                    for key, path in sources.items()}
    seed = json.loads(args.seed.read_text(encoding='utf-8-sig'))
    parameters = list(map(arithmetic.Q, seed['center_exact_decimal']))
    phase = list(map(arithmetic.Q, seed['phase_exact_decimal']))
    if len(parameters) != 5 or len(phase) != 2:
        raise ValueError('Expected five candidate parameters and two phase coordinates')
    step = parameters[2] / 4000
    if step <= 0:
        raise ValueError('Expected a positive nominal step')
    candidate_hash = fingerprints['candidate_initial']['sha256']
    initial = [parameters[0], parameters[3] * phase[0] / 8, parameters[1],
               parameters[3] * phase[1], parameters[4], arithmetic.Q(0)]
    identity = [[arithmetic.S * int(i == j) for i in range(6)] for j in range(6)]
    plan = {'schema': 'rotating.production-plan.v1', 'revision': args.revision,
            'revision_kind': 'worktree' if args.revision.startswith('worktree-') else 'git',
            'candidate_id': 'nonzero_rotation_minus56_over57', 'candidate_hash': candidate_hash,
            'steps_per_sign': args.steps_per_sign, 'full_path_steps_per_sign': 4000,
            'shard_size': args.shard_size, 'orders': {'state': 42, 'matrix': 22},
            'mesh': str(arithmetic.S), 'step': {'num': str(step.numerator), 'den': str(step.denominator)},
            'source_fingerprints': fingerprints, 'jobs': [], 'kernel_checked': False,
            'inter_shard_seams_proved': False,
            'status': 'generating untrusted checkpoints; no Lean proof or trajectory/root conclusion'}
    save(directory / 'plan.json', plan)
    started = time.monotonic()
    for sign, tag in ((1, 'p'), (-1, 'm')):
        state = list(initial)
        matrix = [list(col) for col in identity]
        previous = None
        signed_step = arithmetic.ofq(sign * step)
        for start, count in partition:
            for index in range(start, start + count):
                balls = list(map(arithmetic.ofq, state)) if index == 0 else [(int(v * arithmetic.S), 0) for v in state]
                coefficients, square = arithmetic.state_coefficients(balls, 42)
                variation = [arithmetic.full_variation(coefficients, square, [(v, 0) for v in col])
                             for col in matrix]
                state_out = arithmetic.endpoint(coefficients, signed_step)
                matrix_out = [arithmetic.endpoint(column, signed_step) for column in variation]
                state = [arithmetic.Q(v[0], arithmetic.S) for v in state_out]
                matrix = [[v[0] for v in col] for col in matrix_out]
            relative = f'checkpoints/{tag}_{start + count:04d}.json'
            save(directory / relative, checkpoint(start + count, sign, state, matrix, candidate_hash, step))
            plan['jobs'].append({'key': f'R{tag.upper()}{start:04d}', 'sign': sign,
                                 'start': start, 'count': count, 'input_node': previous,
                                 'input_node_sha256': sha(directory / previous) if previous else None,
                                 'output_node': relative, 'output_node_sha256': sha(directory / relative),
                                 'artifact_name': f'rotating-{args.revision}-{tag}-{start:04d}-{count:04d}'})
            previous = relative
            save(directory / 'plan.json', plan)
            print(f'UNTRUSTED_CHECKPOINT sign={sign} endpoint={start + count}', flush=True)
    validate_plan(plan, directory)
    if any(sha(path) != fingerprints[key]['sha256'] for key, path in sources.items()):
        raise ValueError('Source changed during proposal generation')
    plan.update(status='untrusted checkpoints and disjoint job coverage generated; Lean checks still required',
                generation_wall_seconds=time.monotonic() - started)
    save(directory / 'plan.json', plan)
    save(directory / 'matrix.json', {'include': plan['jobs']})
    print(json.dumps({'jobs': len(plan['jobs']), 'steps_per_sign': args.steps_per_sign,
                      'seconds': plan['generation_wall_seconds'], 'kernel_checked': False}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', type=Path, required=True)
    parser.add_argument('--candidate-source', type=Path, required=True)
    parser.add_argument('--template-root', type=Path,
                        default=arithmetic.ROOT / 'SolitonClassification/Rotating')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--revision', required=True)
    parser.add_argument('--steps-per-sign', type=int, default=32)
    parser.add_argument('--shard-size', type=int, default=32)
    args = parser.parse_args()
    try:
        build(args)
    except Exception as error:
        if getattr(args, '_owned_output', False):
            path = args.output / 'failure.json'
            save(path, {'status': 'failed', 'error': str(error), 'kernel_checked': False})
        raise


if __name__ == '__main__':
    main()
