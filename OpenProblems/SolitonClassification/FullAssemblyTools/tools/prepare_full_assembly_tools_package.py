"""Build a new text-only full-assembly tools/source candidate and partial evidence.

Never modifies published packages, frozen sources, locks or numerical outputs.
No network, Lean execution, workflow or fake complete250 request is generated.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def blob(raw):
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()

def read(path):
    return json.loads(Path(path).read_bytes())

def require(ok, message):
    if not ok:
        raise ValueError(message)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-root', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--first4-evidence-output', type=Path, required=True)
    ap.add_argument('--report', type=Path, required=True)
    a = ap.parse_args()
    source, out, evidence = a.source_root.resolve(), a.output.resolve(), a.first4_evidence_output.resolve()
    require(not out.exists() and not evidence.exists() and not a.report.exists(), 'All outputs must be new')
    require(not out.is_relative_to(evidence) and not evidence.is_relative_to(out), 'Separate package outputs required')
    require(source.is_dir() and not out.is_relative_to(source / 'pipeline'), 'Wrong source/output layout')
    sys.path.insert(0, str(source / 'pipeline'))
    import production_full_assembly_compile as compiler
    validator = compiler.load_validator()
    validator.load_helpers()
    require(sha(compiler.__file__) == 'a0e2b19e60ebefdf1b35ac162df0a5a7f9b67188b4eb26d604d0664a1186456a', 'Compiler moved')
    before = compiler.tools_now(validator)
    tree_path = source / 'full_assembly_tools_package_v1_review/remote_tree.json'
    remote = read(tree_path)
    require(remote['revision'] == '68dccd983c01e9a3222646c826c40c7efcdf035c'
            and remote['observation']['truncated'] is False and len(remote['observation']['tree']) == 1545,
            'Expected complete observed project tree')
    remote_blobs = {r['sha']: r['path'] for r in remote['observation']['tree'] if r['type'] == 'blob'}
    candidate = source / 'pipeline/assembly_final_sources_v1/SolitonClassification/Rotating/FullCandidate.lean'
    candidate_raw = candidate.read_bytes()
    captured = read(source / 'full_assembly_tools_package_v1_review/remote_candidate.json')
    require(captured['revision'] == 'ec3547c9456f47b5bf7c8b9d07ff07bf56ff24d9'
            and captured['content'].encode() == candidate_raw and captured['sha'] == blob(candidate_raw),
            'Actual observed published candidate differs')
    require(sha(candidate) == validator.CANDIDATE_SHA
            and remote_blobs[blob(candidate_raw)] == 'ProductionPipeline/future/uncompiled/FullCandidate.lean', 'Candidate source pin differs')
    records, selected_inputs = {}, {}
    out.mkdir(parents=True)

    def add(raw, relative, role, origin=None):
        require(relative not in records and relative.lower() not in {n.lower() for n in records}, 'Duplicate package path')
        raw.decode('utf-8')
        p = out / relative
        p.parent.mkdir(parents=True, exist_ok=True)
        with p.open('xb') as f:
            f.write(raw)
        records[relative] = {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(), 'role': role}
        if origin is not None:
            records[relative]['origin'] = origin

    def copy(p, relative, role):
        raw = p.read_bytes()
        selected_inputs[str(p)] = hashlib.sha256(raw).hexdigest()
        add(raw, relative, role, p.relative_to(source).as_posix())

    def obj(value, relative, role):
        add((json.dumps(value, sort_keys=True, indent=2) + '\n').encode(), relative, role)

    add(b'* -text\n', '.gitattributes', 'byte-preserving Git transport')
    for name in ['production_full_assembly_compile.py', 'production_full_assembly_plan.py',
                 *validator.HELPERS.keys()]:
        original = source / 'pipeline' / name
        dest = 'performance/reference.py' if name == '../performance/reference.py' else 'tools/' + name
        copy(original.resolve(), dest, 'frozen runtime helper')
    for name in ['prepare_full_assembly_tools_package.py', 'verify_full_assembly_tools_package.py',
                 'test_full_assembly_compile.py', 'test_full_assembly_plan.py', 'test_full_assembly_audit_patch.py']:
        copy(source / 'pipeline' / name, 'tools/' + name, 'package tool' if 'package' in name else 'historical tiny test source')

    assembly = source / 'pipeline/assembly_full_sources'
    endpoints = source / 'pipeline/assembly_endpoint_sources_v2'
    all_rows = []
    for folder, manifest_name, dest, digest, count in [
            (assembly, 'assembly_manifest.json', 'uncompiled/assembly', validator.ASSEMBLY_SHA, 499),
            (endpoints, 'endpoint_links_manifest.json', 'uncompiled/endpoints', validator.ENDPOINT_SHA, 2)]:
        require(sha(folder / manifest_name) == digest, 'Frozen source manifest moved')
        m = read(folder / manifest_name)
        require(len(m['modules']) == count and m['kernel_checked'] is False and m['full_certificate_proved'] is False,
                'Incorrect uncompiled source count/scope')
        copy(folder / manifest_name, dest + '/' + manifest_name, 'original uncompiled source manifest')
        for row in m['modules']:
            p = folder / row['source']
            require(sha(p) == row['sha256'] and blob(p.read_bytes()) not in remote_blobs,
                    'Source changed or already archived; review source selection')
            copy(p, dest + '/' + row['source'], 'uncompiled future assembly source')
            all_rows.append({'name': row['name'], 'source_sha256': row['sha256'], 'package_path': dest + '/' + row['source']})
    require(len(all_rows) == 501, 'Wrong uncompiled local set')
    copy(source / 'FullAssemblyDesignCensus.json', 'inputs/FullAssemblyDesignCensus.json', 'original exact502 source census')
    refs = {
        'schema': 'rotating.full-assembly-external-sources.v1',
        'repository': remote['repository'], 'source_revision': validator.SOURCE_REVISION,
        'candidate': {'revision': captured['revision'], 'path': captured['path'], 'sha256': sha(candidate),
                      'git_blob_sha1': blob(candidate_raw), 'bytes': len(candidate_raw), 'kernel_checked': False},
        'core_project': {'revision': validator.SOURCE_REVISION, 'path': 'OpenProblems/SolitonClassification/ModuleProduction',
                         'inventory_name': 'ModuleProductionSourceInventory.json', 'inventory_sha256': validator.CORE_SHA},
        'production_pipeline': {'revision': captured['revision'], 'path': 'OpenProblems/SolitonClassification/ProductionPipeline',
                                'inventory_sha256': validator.PIPELINE_SHA, 'plan_sha256': validator.PLAN_SHA},
        'final_sources': {'revision': '9b426287c11f61e03c601618aa4268e330d6e7b3',
                          'path': 'OpenProblems/SolitonClassification/FinalSources', 'manifest_sha256': validator.FINAL_SHA},
        'actual_Linux48': {'report_sha256': compiler.LINUX48_SHA, 'run_id': 43354529340, 'artifact_id': 14007325855,
                           'zip_bytes': 56200489, 'zip_sha256': '4664358fbe4b3a93edd5462626b85ba189bd0e43276a0345fb03ce1893eb1378',
                           'included_here': False},
        'base_lock_sha256': validator.BASE_SHA,
        'complete250_ledger_present': False, 'complete250_merge_present': False,
        'execution_request_present': False, 'full_certificate_proved': False}
    obj(refs, 'inputs/ExternalSources.json', 'exact existing-source and future-evidence references')
    copy(tree_path, 'verification/remote_source_tree.json', 'actual read-only remote tree observation')
    obj({'schema': 'rotating.assembly-source-selection.v1', 'observed_revision': remote['revision'],
         'observed_project_tree': remote['observation']['sha'], 'tree_truncated': False,
         'whole_repository_other_namespaces_searched': False,
         'local501_absent_as_Git_blob_from_observed_project_tree': True, 'sources': all_rows,
         'candidate_exact_published_GET': refs['candidate'], 'new_remote_writes': 0,
         'full_certificate_proved': False}, 'verification/SourceSelection.json', 'actual source deduplication observation')

    for name in ['FullAssemblyCompilerFrozenManifest.json', 'FullAssemblyPlanValidatorFrozenManifest.json',
                 'FullAssemblyCompilerStatus.txt', 'FullAssemblyPlanValidatorStatus.txt',
                 'FullAssemblyCompilerImplementationDesign.txt', 'FullAssemblyCompilerDesign.txt',
                 'FullAssemblyLinuxDeploymentDesign.txt']:
        copy(source / name, 'documentation/' + name, 'historical frozen design/status')
    for name in ['FullAssemblyCompilerIndependentReview.txt', 'FullAssemblyCompilerRootReview.txt',
                 'FullAssemblyPlanIndependentReview.txt', 'FullAssemblyPlanValidatorRootReview.txt']:
        copy(source / 'performance' / name, 'verification/' + name, 'existing independent/root review')
    for folder in ['assembly_plan_fixture_v2', 'assembly_plan_audit_patch_check']:
        for p in sorted((source / folder).rglob('*')):
            if p.is_file() and p.suffix in ('.json', '.lean', '.log', '.py'):
                copy(p, p.relative_to(source).as_posix(), 'historical actual tiny/structural evidence')
    tiny = source / 'full_assembly_compiler_tiny_v1'
    copy(tiny / 'report.json', 'full_assembly_compiler_tiny_v1/report.json', 'historical actual tiny report')
    for branch in ['positive', 'bad_binder', 'wrong_header', 'wrong_source']:
        for p in sorted((tiny / branch).rglob('*')):
            relative = p.relative_to(tiny).as_posix()
            if p.is_file() and (relative.endswith('/compile_report.json') or
                               any('/' + x + '/' in relative for x in ('source', 'logs', 'setups'))):
                copy(p, 'full_assembly_compiler_tiny_v1/' + relative, 'historical tiny source/log/setup/report; no binary proof')
    readme = '''FULL ASSEMBLY TOOLS: LOCAL PUBLICATION CANDIDATE, NOT A FULL PROOF

This separate package preserves the frozen A0E2 compiler, D509 validator and
their12 exact helpers. tools/ and performance/reference.py retain the actual
import layout. No old published package, numerical source or base is changed.

uncompiled/ contains499 grid assembly sources and two endpoint links, with
their original unmodified manifests. They have not been compiled against the
complete250 shards. The final FullCandidate source is already published and
is referenced by exact commit/path/SHA/Git blob in inputs/ExternalSources.json;
it is not duplicated or relabelled as proved. The exact502 source census is
preserved. Core87, FinalSources48 and ProductionPipeline also remain external
immutable references. The old source plan and A62 production revision binding
must still be checked by D509; no source manifest is rewritten to hide it.

Historical tiny evidence is text only: actual four-module public import and
five-elaboration compiler fixture, one expected Lean binder failure, structural
rejections and the narrow D509 audit patch. Reports and source/setup/log bytes
are unchanged. Their original Windows paths and compiler hashes are evidence,
not portable path overrides. Full tiny proof binaries/IR are intentionally
omitted; this is not a complete transport of those tests. No tiny test or Lean
call was repeated to prepare the package. Existing tests remain scoped to their
documented input/toolchain expectations; packaging does not certify all502.

Verify with an externally supplied inventory hash:
 python -B tools/verify_full_assembly_tools_package.py --package PACKAGE
   --inventory-sha256 ACTUAL_SHA --report NEW_OUTSIDE_PACKAGE_REPORT.json
This validates all text bytes/source manifests and actually imports the14
compiler/validator/helper modules from this package. It does not invoke Lean.

Future production CLI and all required paths are documented in the unchanged
documentation/FullAssemblyCompilerStatus.txt. Use --assembly-root
PACKAGE/uncompiled/assembly, --endpoint-root PACKAGE/uncompiled/endpoints,
--census PACKAGE/inputs/FullAssemblyDesignCensus.json, and the exact externally
checked-out ProductionPipeline/future/uncompiled/FullCandidate.lean.
Only genuine full250 ledger/merge plus the original actual Linux48 report and
exact Linux base can unlock D509 before compilation. Those objects are not
included or simulated. No compile request, workflow, fabricated ledger or
future-success receipt is generated by this package.

Successful package verification means source/tool preparation only. There is
no new numerical trajectory, final candidate proof, classification, migration
or length-growth result. The root agent owns any eventual GitHub publication.
'''
    add(readme.encode(), 'README.txt', 'current precise package scope')
    for path, digest in selected_inputs.items():
        require(sha(path) == digest, 'Original selected input changed')
    require(compiler.tools_now(validator) == before, 'Frozen runtime changed')
    inventory = {'schema': 'rotating.full-assembly-tools-package.v1', 'source_revision': validator.SOURCE_REVISION,
                 'files': records, 'uncompiled_source_modules_included': 501, 'full250_inputs_supplied': False,
                 'full_assembly_executed': False, 'full_certificate_proved': False, 'cloud_workflow_included': False}
    raw = (json.dumps(inventory, sort_keys=True, indent=2) + '\n').encode()
    (out / 'FullAssemblyToolsInventory.json').write_bytes(raw)

    # Separate partial metadata evidence. Deliberately omit all .olean/IR and
    # transports; the original manifest's references to omitted bytes remain.
    actual = source / 'first_four_durable_projection_v1'
    require(sha(actual / 'report.json') == 'fc407d79793f58507afea955bf1872ae32545e7f5da48aa8585a34457db84fae'
            and sha(actual / 'TerminalPostcheck.json') == '398dc98ba289ee68b95a1c5cba2160fe40e6d56b4d1505705dfa4f39689bba1f',
            'Actual first-four evidence moved')
    evidence.mkdir(parents=True)
    evidence_files = {}
    def ecopy(p, rel):
        data = p.read_bytes(); data.decode('utf-8')
        q = evidence / rel; q.parent.mkdir(parents=True, exist_ok=True)
        with q.open('xb') as f: f.write(data)
        evidence_files[rel] = {'bytes': len(data), 'sha256': sha(p)}
    for name in ['report.json', 'ledger.json', 'input_pins.json', 'CheckedFilesManifest.json', 'TerminalPostcheck.json']:
        ecopy(actual / name, name)
    for directory in ('logs', 'merged/evidence'):
        for p in sorted((actual / directory).rglob('*')):
            if p.is_file():
                ecopy(p, p.relative_to(actual).as_posix())
    for name in ('merged/merge_receipt.json', 'merged/merge_receipt.sha256'):
        ecopy(actual / name, name)
    ecopy(source / 'FirstFourDurableProjectionFrozenStatus.txt', 'FrozenStatus.txt')
    for name in ('FirstFourDurableProjectionIndependentReview.txt', 'FirstFourActualReleaseIndependentReview.txt',
                 'FirstFourActualReleaseIndependentReplay.json', 'run_first_four_durable_projection_v1.py',
                 'postcheck_first_four_durable_projection_v1.py', 'review_first_four_actual_release_independent.py'):
        ecopy(source / 'performance' / name, 'verification/' + name)
    scope = b'Text-only evidence of four actual durable projections and a pilot merge. No binaries or compact transports are included. Original report/manifests retain their exact hashes and refer to omitted binary bytes. This subset is not an independently consumable projection/merged tree and must never be supplied to the full250 compiler. No new Lean/network calls; full certificate not proved.\n'
    (evidence / 'SCOPE.txt').write_bytes(scope)
    evidence_files['SCOPE.txt'] = {'bytes': len(scope), 'sha256': hashlib.sha256(scope).hexdigest()}
    eraw = (json.dumps({'schema': 'rotating.first-four-partial-metadata-package.v1', 'files': evidence_files,
                       'source_revision': validator.SOURCE_REVISION,
                       'publication_revision': '68dccd983c01e9a3222646c826c40c7efcdf035c',
                       'mode': 'pilot', 'binary_artifacts_included': False, 'transports_included': False,
                       'full_certificate_proved': False}, sort_keys=True, indent=2) + '\n').encode()
    (evidence / 'PartialEvidenceInventory.json').write_bytes(eraw)
    result = {'schema': 'rotating.full-assembly-package-preparation.v1', 'status': 'prepared_not_published',
              'package': str(out), 'inventory_sha256': hashlib.sha256(raw).hexdigest(),
              'package_files_including_inventory': len(records) + 1,
              'package_bytes_including_inventory': sum(r['bytes'] for r in records.values()) + len(raw),
              'partial_evidence_package': str(evidence), 'partial_inventory_sha256': hashlib.sha256(eraw).hexdigest(),
              'partial_files_including_inventory': len(evidence_files) + 1,
              'partial_bytes_including_inventory': sum(r['bytes'] for r in evidence_files.values()) + len(eraw),
              'original_input_pins': selected_inputs, 'new_Lean_calls': 0, 'new_network_calls': 0,
              'full250_inputs_supplied': False, 'full_certificate_proved': False}
    a.report.parent.mkdir(parents=True, exist_ok=True)
    with a.report.open('x', encoding='utf-8', newline='\n') as f:
        f.write(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'inventory_sha256', 'package_files_including_inventory',
                    'package_bytes_including_inventory', 'partial_inventory_sha256', 'partial_files_including_inventory')}))

if __name__ == '__main__':
    main()
