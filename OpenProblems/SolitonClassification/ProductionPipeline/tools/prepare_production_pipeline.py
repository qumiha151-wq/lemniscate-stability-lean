"""Copy an immutable production package; never integrate, compile or publish.

Rebinding a proposal plan changes only the explicit source revision metadata
and its archive names. Old checkpoints and all mathematical data remain bytes
copied from the original untrusted worktree plan, whose digest is retained.
"""
from pathlib import Path
import argparse, json
import verify_production_pipeline as verifier


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8', newline='\n')


def prepare(formal, plan_dir, output):
    verifier.no_links(output)
    verifier.require(not output.exists(), 'New immutable package directory required')
    for source in (formal, plan_dir):
        verifier.no_links(source)
        verifier.require(not output.resolve().is_relative_to(source.resolve())
                         or output.resolve().parent == formal.resolve(),
                         'Unexpected overlap with inputs')
    core_dir = formal / 'pipeline/module_production_project_v4'
    transport_dir = formal / 'production_tools_package_v4'
    final_dir = formal / 'final_source_package_v3'
    pipeline = formal / 'pipeline'
    core_inventory = core_dir / 'ModuleProductionSourceInventory.json'
    transport_inventory = transport_dir / 'ProductionToolsInventory.json'
    final_inventory = final_dir / 'FinalSourcesManifest.json'
    verifier.require(verifier.digest(core_inventory) == verifier.CORE_SHA
                     and verifier.digest(transport_inventory) == verifier.TRANSPORT_SHA
                     and verifier.digest(final_inventory) == verifier.FINAL_SHA, 'Original inventories differ')
    old = verifier.read_json(plan_dir / 'plan.json')
    verifier.require(verifier.digest(plan_dir / 'plan.json') == verifier.ORIGINAL_PLAN_SHA,
                     'Original worktree plan changed')
    core = verifier.read_json(core_inventory)
    transport = verifier.read_json(transport_inventory)
    files, source_hashes = {}, {}
    output.mkdir(parents=True, exist_ok=False)

    def copy(source, relative, role, origin):
        verifier.no_links(source)
        raw = source.read_bytes()
        target = verifier.confined(output, relative)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
        source_hashes[source] = verifier.file_record(source)
        files[relative] = {**verifier.file_record(target), 'role': role, 'origin': origin}

    def created(relative, text, role):
        target = verifier.confined(output, relative)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding='utf-8', newline='\n')
        files[relative] = {**verifier.file_record(target), 'role': role, 'origin': 'new_package_metadata'}

    for name in verifier.EXISTING_TOOLS:
        relative = 'tools/' + name
        if name in ('production_job.py', 'production_compile_final_supplement.py'):
            source, origin = pipeline / name, 'frozen_independent_runner'
        elif relative in transport['files']:
            source, origin = transport_dir / relative, 'ProductionTools@' + verifier.SOURCE_REVISION
        else:
            source, origin = core_dir / relative, 'ModuleProduction@' + verifier.SOURCE_REVISION
        copy(source, relative, 'frozen_runtime_tool', origin)
    for name in verifier.NEW_TOOLS:
        copy(pipeline / name, 'tools/' + name, 'package_prepare_or_verify', 'new_package_tool')
    for relative in sorted(set(verifier.SOURCE_MAP.values()) - set(files)):
        copy(core_dir / relative, relative, core['files'][relative]['role'],
             'ModuleProduction@' + verifier.SOURCE_REVISION)
    for source, relative in (
        (core_inventory, 'provenance/ModuleProductionSourceInventory.json'),
        (transport_inventory, 'provenance/ProductionToolsInventory.json'),
        (final_inventory, 'provenance/FinalSourcesManifest.json'),
        (plan_dir / 'plan.json', 'provenance/OriginalWorktreePlan.json')):
        copy(source, relative, 'source_binding', 'unchanged_original_inventory_or_plan')
    for job in old['jobs']:
        copy(verifier.confined(plan_dir, job['output_node']), 'plan/' + job['output_node'],
             'untrusted_proposed_checkpoint', 'original_worktree_plan_exact_bytes')
    plan = verifier.production_plan(old)
    for relative, value in [('plan/plan.json', plan), ('plan/matrix.json', {'include': plan['jobs']})]:
        created(relative, json.dumps(value, indent=2) + '\n', 'revision_bound_untrusted_plan')
    created('plan/PlanRevisionBinding.json', json.dumps(verifier.plan_binding(output, old, plan), indent=2) + '\n',
            'exact_metadata_only_rebinding')
    draft_dir = pipeline / 'assembly_final_sources_v1'
    copy(draft_dir / 'SolitonClassification/Rotating/FullCandidate.lean', 'future/uncompiled/FullCandidate.lean',
         'UNCOMPILED_future_application', 'isolated_root_draft_not_part_of_final48')
    copy(draft_dir / 'STATUS.txt', 'future/uncompiled/STATUS.txt', 'UNCOMPILED_scope', 'isolated_root_draft_scope')
    evidence_paths = {
        'fixture_report': pipeline / 'final_runner_fixture_v4/fixture_report.json',
        'full48_compile_report': pipeline / 'final_supplement_portable_check/compile_report.json',
        'postcheck_evidence': formal / 'FinalSupplementPortableCheckEvidence.json',
        'status': formal / 'FinalSupplementPortableCheckStatus.txt'}
    verifier.require({key: verifier.digest(path) for key, path in evidence_paths.items()} == verifier.EVIDENCE_SHA,
                     'Frozen actual local evidence changed')
    evidence = {'schema': 'rotating.pipeline-local-evidence-reference.v1',
        'runner_sha256': verifier.RUNNER_SHA,
        'referenced_evidence': {key: verifier.file_record(path) for key, path in evidence_paths.items()},
        'actual_local_results': {'platform': 'Windows', 'final48_compiled': 48,
            'fresh_audit_declarations': 2205, 'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
            'fixture_modules_compiled': 3, 'rejection_fixtures_passed': 10,
            'new_output_layers_bound': ['.olean', '.olean.private', '.olean.server'],
            'temporary_generated_IR_promoted': False},
        'full_numeric_grid_instantiated': False, 'linux_final48_executed': False,
        'full_candidate_draft_compiled': False, 'full_certificate_proved': False}
    created('provenance/LocalValidationEvidence.json', json.dumps(evidence, indent=2) + '\n', 'evidence_hashes_and_scope')
    created('.gitattributes', '* -text\n', 'exact_byte_checkout')
    created('Scope.txt', '''ProductionPipeline v1 -- tools and UNTRUSTED numerical proposals

This separate immutable package does not modify ModuleProduction (108-file
inventory, 87 generic modules plus audit), ProductionTools, or FinalSources.
Source core revision: cff971bcac7ac2d83aba04596ce09e44fda1ac29.
Core source tree: 4b6b13d019143260585f2eee8e6fbb07e3249033.
The future tool-package Git revision is distinct and must be recorded by the
caller; null in this source inventory means not yet published, never cff.

The original worktree plan and all 250 checkpoint byte strings are preserved.
Only revision, revision_kind and canonical archive names change in the new
production plan. Its numeric fields, eight generator inputs and leaf coverage
remain identical. This is an exact metadata rebinding, not a recomputation or
a numerical/Lean certificate. PlanRevisionBinding records both plan hashes.
All eight original inputs match the separately pinned core source inventory.

Use verify_production_pipeline.py with an externally pinned inventory digest.
Pass explicit --seed, --candidate-source, --template-root to production_job.py;
its old default development paths are not a production interface. The layout
retains performance/reference.py for the frozen tools' relative import.
Fresh output paths belong outside this immutable package.

Future Linux verification should restore one exact original core, including
the prebuilt upstream Arctan dependency, then check RP0000, RP3968, RM0000 and
RM3968 independently with production_job.py prepare/compile-pack and optionally
consume their validated public artifacts. All four successful shards can be
retained for the eventual 250-shard assembly. Use the same restored base for
the actual 48-module final runner and its fresh 2205-declaration audit. The
production Linux run needs no setup-extra override or Mathlib cache rebuild.
The workflow, archive hashes, run results and new tool revision are not invented
by this package. No workflow is installed or executed by its preparation.

The final48 theorem still takes two genuine 4000-step signed blocks and eight
exact initial/terminal identities. The package provides no such blocks.
future/uncompiled/FullCandidate.lean is an uncompiled future application. Its
FullGridPActual and FullGridMActual imports await complete numeric proofs and
assembly. Its source has no executed audit or unconditional theorem status.
Even that eventual result would not classify all self-similar solutions or
resolve the remaining length-growth and migration questions.

Local evidence hashes record real Windows final48 and fixture checks, not
Linux execution. The final runner binds/promotes three olean layers; temporary
generated IR is excluded from imports and not promoted or finally bound.
Original proof/private layers are preserved in full shard archive validation.
''', 'scope_and_future_execution_contract')
    verifier.require(set(files) == verifier.expected_paths(), 'Incomplete package construction')
    inventory = {'schema': verifier.SCHEMA, 'source_only': True,
        'source_revision': verifier.SOURCE_REVISION, 'source_tree': verifier.SOURCE_TREE,
        'tool_package_revision': None, 'core_inventory_sha256': verifier.CORE_SHA,
        'transport_inventory_sha256': verifier.TRANSPORT_SHA,
        'final_sources_manifest_sha256': verifier.FINAL_SHA,
        'full_certificate_proved': False, 'files': dict(sorted(files.items()))}
    save(output / 'ProductionPipelineInventory.json', inventory)
    sha = verifier.digest(output / 'ProductionPipelineInventory.json')
    (output / 'ProductionPipelineInventory.sha256').write_text(sha + '\n', encoding='utf-8', newline='\n')
    verifier.require(all(verifier.file_record(p) == record for p, record in source_hashes.items()),
                     'Original input changed during copying')
    result = verifier.verify(output, sha, core_dir)
    return {**result, 'inventory_sha256': sha, 'plan_sha256': verifier.digest(output / 'plan/plan.json')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--formal-root', type=Path, required=True)
    parser.add_argument('--original-plan', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(prepare(args.formal_root.resolve(), args.original_plan.resolve(), args.output)), flush=True)


if __name__ == '__main__':
    main()
