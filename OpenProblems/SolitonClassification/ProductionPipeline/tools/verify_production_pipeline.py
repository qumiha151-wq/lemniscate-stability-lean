"""Verify the immutable, separate production-tools and untrusted-plan package.

An externally pinned inventory digest is mandatory. This is byte/protocol
verification, never a Lean check, numerical integration or root certificate.
"""
from pathlib import Path, PurePosixPath
from fractions import Fraction
import argparse, hashlib, json, re

SOURCE_REVISION = 'cff971bcac7ac2d83aba04596ce09e44fda1ac29'
SOURCE_TREE = '4b6b13d019143260585f2eee8e6fbb07e3249033'
CORE_SHA = '2c252cf849e22e027ca2630b836e5227b8ff8390cf45f36a6b467db64580c924'
TRANSPORT_SHA = '046b1fa6b7ce9fd52713c94e9913720760831dd84e55484a639a4782bdb08f32'
FINAL_SHA = '51e1abe4b94640773e1fe66f93cfc1ad58a57fafbd050a260eba53da0f61fd72'
FINAL_DRAFT_SHA = '697b53e7bd0546a26c2dc10769a9b93c5d5082a386644d6f9ac908d53f28bb70'
JOB_SHA = '16cf9443c13cb4f7213003cc9dc4a5cb7ac7a248b937210dd9721ed622438103'
RUNNER_SHA = '14c9360c15517658200649cafff904948184ac4b23194ab60aac15926dba8dd5'
ORIGINAL_PLAN_SHA = '0151212bd25d256d328fb52e4db5fb953722c9faf870b31526e91b82e23a60bf'
DRAFT_STATUS_SHA = 'a1d3ef69fbf3cbc9e88707a11defe2c42038a55200a060f406287958a9f5a87f'
EVIDENCE_SHA = {
    'fixture_report': '357b6f887d584c631a9354c7968b3bb13df09205b5cf045e78089228c2faec72',
    'full48_compile_report': 'bd2b2f8ace0fa21a7c8e5935e673080ce9e2c54eaeE64f9e69bd2ace73e9d24e'.lower(),
    'postcheck_evidence': '850b07bd29b69dd788bf30b40db155007d67e7bdc188a3c0dfcfbff0e56913c4',
    'status': '509726a3bd3caa31f49781e23b442f18b4b293cd155780ce8ffd890a16edbc6a'}
SCHEMA = 'rotating.production-pipeline-source.v1'
EXISTING_TOOLS = (
    'production_compile_final_supplement.py', 'production_job.py',
    'production_compile_shard.py', 'production_artifact.py',
    'plan_production_grid.py', 'propose_grid42x22.py',
    'generate_production_shard.py', 'production_core_artifact.py',
    'production_public_consumer.py', 'production_core_import_check.py',
    'production_environment.py')
NEW_TOOLS = ('prepare_production_pipeline.py', 'verify_production_pipeline.py')
SOURCE_MAP = {
    'seed': 'inputs/shooting_certificate.json',
    'candidate_initial': 'inputs/CandidateInitial.original.lean',
    'planner': 'tools/plan_production_grid.py',
    'proposal_arithmetic': 'tools/propose_grid42x22.py',
    'interval_arithmetic': 'performance/reference.py',
    'shard_generator': 'tools/generate_production_shard.py',
    'state_template': 'inputs/templates/Block16Leaf08State.lean',
    'matrix_template': 'inputs/templates/Block16Leaf08Matrix.lean'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def no_links(path):
    for p in [path, *path.parents]:
        require(not p.is_symlink() and not (hasattr(p, 'is_junction') and p.is_junction()),
                'Linked or junction path: ' + str(p))


def confined(root, relative):
    require(isinstance(relative, str) and '\\' not in relative, 'Noncanonical package path')
    part = PurePosixPath(relative)
    require(not part.is_absolute() and part.parts and str(part) == relative
            and all(p not in ('', '.', '..') for p in part.parts), 'Escaping package path')
    p = root.joinpath(*part.parts)
    no_links(p)
    require(p.resolve().is_relative_to(root.resolve()), 'Path escaped package')
    return p


def file_record(path):
    return {'sha256': digest(path), 'bytes': path.stat().st_size}


def expected_paths():
    fixed = {f'tools/{n}' for n in EXISTING_TOOLS + NEW_TOOLS}
    fixed.update(SOURCE_MAP.values())
    fixed.update({'.gitattributes', 'Scope.txt',
        'provenance/ModuleProductionSourceInventory.json',
        'provenance/ProductionToolsInventory.json',
        'provenance/FinalSourcesManifest.json', 'provenance/OriginalWorktreePlan.json',
        'provenance/LocalValidationEvidence.json',
        'plan/plan.json', 'plan/matrix.json', 'plan/PlanRevisionBinding.json',
        'future/uncompiled/FullCandidate.lean', 'future/uncompiled/STATUS.txt'})
    fixed.update(f'plan/checkpoints/{sign}_{i:04d}.json'
                 for sign in ('p', 'm') for i in range(32, 4001, 32))
    return fixed


def production_plan(original):
    result = json.loads(json.dumps(original))
    result['revision'] = SOURCE_REVISION
    result['revision_kind'] = 'git'
    for job in result['jobs']:
        sign = 'p' if job['sign'] == 1 else 'm'
        job['artifact_name'] = f'rotating-{SOURCE_REVISION}-{sign}-{job["start"]:04d}-{job["count"]:04d}'
    return result


def plan_binding(root, original, current):
    return {
        'schema': 'rotating.production-plan-revision-binding.v1',
        'source_revision': SOURCE_REVISION, 'source_tree': SOURCE_TREE,
        'original_revision': original['revision'],
        'original_plan_sha256': digest(root / 'provenance/OriginalWorktreePlan.json'),
        'production_plan_sha256': digest(root / 'plan/plan.json'),
        'changed_fields_only': ['revision', 'revision_kind', 'jobs[*].artifact_name'],
        'source_fingerprints_unchanged': True,
        'checkpoint_bytes_unchanged': True,
        'generation_wall_seconds_is_original_metadata': True,
        'sources': {role: {'package_path': path, 'core_inventory_path': path,
                          **original['source_fingerprints'][role]}
                    for role, path in SOURCE_MAP.items()},
        'checkpoints': [{'path': j['output_node'], 'sha256': j['output_node_sha256']}
                        for j in current['jobs']],
        'checkpoint_computation_repeated': False, 'kernel_checked': False,
        'full_certificate_proved': False}


def verify_plan(root, core):
    old = read_json(root / 'provenance/OriginalWorktreePlan.json')
    plan = read_json(root / 'plan/plan.json')
    require(old['revision'] == 'worktree-full4000-v1' and old['revision_kind'] == 'worktree',
            'Wrong original proposal identity')
    require(plan == production_plan(old), 'Numeric plan or nonapproved metadata changed')
    require(plan['schema'] == 'rotating.production-plan.v1'
            and plan['candidate_id'] == 'nonzero_rotation_minus56_over57'
            and plan['steps_per_sign'] == plan['full_path_steps_per_sign'] == 4000
            and plan['shard_size'] == 32 and plan['orders'] == {'state': 42, 'matrix': 22}
            and plan['mesh'] == str(10**60) and plan['kernel_checked'] is False
            and plan['inter_shard_seams_proved'] is False, 'Wrong fixed untrusted plan scope')
    require(set(plan['source_fingerprints']) == set(SOURCE_MAP), 'Wrong source mapping')
    for role, path in SOURCE_MAP.items():
        require(file_record(root / path) == plan['source_fingerprints'][role],
                'Proposal source mismatch: ' + role)
        require({k: core['files'][path][k] for k in ('sha256', 'bytes')}
                == plan['source_fingerprints'][role], 'Source not bound to core inventory: ' + role)
    require(plan['candidate_hash'] == plan['source_fingerprints']['candidate_initial']['sha256'],
            'Candidate fingerprint differs')
    jobs = plan['jobs']
    require([(j['sign'], j['start'], j['count']) for j in jobs]
            == [(sign, i, 32) for sign in (1, -1) for i in range(0, 4000, 32)],
            'Missing, reordered or duplicated signed leaf coverage')
    for index, job in enumerate(jobs):
        sign = 'p' if job['sign'] == 1 else 'm'
        start = job['start']
        previous = None if start == 0 else f'checkpoints/{sign}_{start:04d}.json'
        require(job['key'] == f'R{sign.upper()}{start:04d}'
                and job['input_node'] == previous
                and job['output_node'] == f'checkpoints/{sign}_{start + 32:04d}.json',
                'Noncanonical endpoint/coverage names')
        require(job['input_node_sha256'] == (None if previous is None else jobs[index - 1]['output_node_sha256']),
                'Input checkpoint chain mismatch')
        node_path = confined(root / 'plan', job['output_node'])
        require(digest(node_path) == job['output_node_sha256'], 'Checkpoint bytes changed')
        node = read_json(node_path)
        require(node['index'] == start + 32 and node['sign'] == job['sign']
                and all(node[k] == plan[k] for k in ('mesh', 'candidate_hash', 'orders', 'step')),
                'Checkpoint metadata differs')
        require(len(node['state_exact_rational']) == 6 and len(node['matrix_integer_columns']) == 6,
                'Wrong endpoint dimension')
        for pair in node['state_exact_rational']:
            require(len(pair) == 2 and all(type(v) is int for v in pair) and pair[1] > 0
                    and (Fraction(*pair) * 10**60).denominator == 1, 'Non-mesh state coordinate')
        require(all(len(col) == 6 and all(type(v) is int for v in col)
                    for col in node['matrix_integer_columns']), 'Wrong full column-major matrix')
    require(read_json(root / 'plan/matrix.json') == {'include': jobs}, 'Matrix plan differs')
    require(read_json(root / 'plan/PlanRevisionBinding.json') == plan_binding(root, old, plan),
            'Plan revision binding differs')
    return plan


def verify(package, expected_sha, core_project=None):
    no_links(package)
    root = package.resolve()
    inventory_path = root / 'ProductionPipelineInventory.json'
    require(re.fullmatch('[0-9a-f]{64}', expected_sha or '') is not None
            and digest(inventory_path) == expected_sha, 'Externally pinned inventory hash differs')
    inventory = read_json(inventory_path)
    require(inventory['schema'] == SCHEMA and inventory['source_revision'] == SOURCE_REVISION
            and inventory['source_tree'] == SOURCE_TREE and inventory['tool_package_revision'] is None
            and inventory['source_only'] is True and inventory['full_certificate_proved'] is False,
            'Wrong package scope/source revision')
    expected = expected_paths()
    require(len(expected) == 280 and set(inventory['files']) == expected, 'Wrong package file inventory')
    actual = set()
    for path in root.rglob('*'):
        no_links(path)
        if path.is_file():
            actual.add(path.relative_to(root).as_posix())
    require(actual == expected | {'ProductionPipelineInventory.json', 'ProductionPipelineInventory.sha256'},
            'Extra or missing package file')
    require((root / 'ProductionPipelineInventory.sha256').read_text() == expected_sha + '\n',
            'Inventory digest sidecar differs')
    for name, record in inventory['files'].items():
        path = confined(root, name)
        require(set(record) == {'sha256', 'bytes', 'role', 'origin'}
                and file_record(path) == {k: record[k] for k in ('sha256', 'bytes')},
                'Missing/modified package file: ' + name)
    for path, sha in {
        'provenance/ModuleProductionSourceInventory.json': CORE_SHA,
        'provenance/ProductionToolsInventory.json': TRANSPORT_SHA,
        'provenance/FinalSourcesManifest.json': FINAL_SHA,
        'provenance/OriginalWorktreePlan.json': ORIGINAL_PLAN_SHA,
        'tools/production_job.py': JOB_SHA,
        'tools/production_compile_final_supplement.py': RUNNER_SHA,
        'future/uncompiled/FullCandidate.lean': FINAL_DRAFT_SHA,
        'future/uncompiled/STATUS.txt': DRAFT_STATUS_SHA}.items():
        require(digest(root / path) == sha, 'Pinned original source changed: ' + path)
    evidence = read_json(root / 'provenance/LocalValidationEvidence.json')
    require({key: row['sha256'] for key, row in evidence['referenced_evidence'].items()} == EVIDENCE_SHA
            and evidence['runner_sha256'] == RUNNER_SHA
            and evidence['full_numeric_grid_instantiated'] is False
            and evidence['linux_final48_executed'] is False
            and evidence['full_candidate_draft_compiled'] is False
            and evidence['full_certificate_proved'] is False, 'Wrong local evidence or execution scope')
    core = read_json(root / 'provenance/ModuleProductionSourceInventory.json')
    transport = read_json(root / 'provenance/ProductionToolsInventory.json')
    for name in EXISTING_TOOLS:
        if name in ('production_job.py', 'production_compile_final_supplement.py'):
            continue
        path = 'tools/' + name
        source = transport['files'] if path in transport['files'] else core['files']
        require(file_record(root / path) == {k: source[path][k] for k in ('sha256', 'bytes')},
                'Reused tool not byte-identical: ' + name)
    plan = verify_plan(root, core)
    if core_project is not None:
        no_links(core_project)
        require(digest(core_project / 'ModuleProductionSourceInventory.json') == CORE_SHA,
                'External core inventory mismatch')
        for relative, record in core['files'].items():
            require(file_record(confined(core_project, relative)) == {k: record[k] for k in ('sha256', 'bytes')},
                    'External core source differs: ' + relative)
    return {'status': 'byte_and_protocol_verified', 'inventory_entries': len(expected),
            'checkpoints': len(plan['jobs']), 'source_revision': SOURCE_REVISION,
            'tool_package_revision': None, 'numerical_kernel_checks_performed': 0,
            'linux_supplement_compiled_by_verifier': False, 'full_certificate_proved': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, required=True)
    parser.add_argument('--inventory-sha256', required=True)
    parser.add_argument('--core-project', type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(args.package, args.inventory_sha256, args.core_project)), flush=True)


if __name__ == '__main__':
    main()
