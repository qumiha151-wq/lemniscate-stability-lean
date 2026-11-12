"""Preserve the exact successful CI proof sources and evidence in Git.

This is archival validation, not a new Lean run. The original run is pinned.
Compiled binaries are inspected, then omitted from the durable source archive.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import sys

REVISION = '9ef471f7e818029931ad20abaa1119a08819b718'
RUN = 43214648337


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--downloads', type=Path, required=True)
    p.add_argument('--staging', type=Path, required=True)
    p.add_argument('--destination', type=Path, required=True)
    args = p.parse_args()
    project = Path(__file__).resolve().parent
    sys.path.insert(0, str(project / 'tools'))
    import shard_artifact
    import compile_full_assembly as full
    downloads, stage, dest = (x.resolve() for x in (args.downloads, args.staging, args.destination))
    if dest.exists():
        raise ValueError('Refuse to overwrite an existing source archive')
    assembly = downloads / f'full-centroid-assembly-{REVISION}' / 'assembly'
    report_path = assembly / 'full_compile_report.json'
    report = json.loads(report_path.read_text())
    if (report.get('schema') != 'centroid.full-certificate-build.v1'
            or report.get('status') != 'checked' or report.get('full_certificate_proved') is not True
            or report.get('compiler_sha256') != digest(project/'tools/compile_full_assembly.py')):
        raise ValueError('No matching successful full compiler report')
    stage.mkdir(parents=True, exist_ok=True)
    records = []
    cases = ('center','a_plus','a_minus','b_plus','b_minus')
    for case in cases:
        for start in range(0,750,50):
            tag = f'{case}-s{start:04}-n0050'
            target = stage/'shards'/tag
            shard_artifact.unpack(downloads/f'centroid-{REVISION}-{tag}'/'certificate.tar.xz',
                                  target,REVISION,512)
            mpath = target/'manifest.json'
            m = json.loads(mpath.read_text())
            if (m['case'],m['start'],m['count']) != (case,start,50):
                raise ValueError('Wrong shard in archive')
            records.append({'manifest':mpath.relative_to(stage).as_posix(),
                            'sha256':digest(mpath),'case':case,'start':start,'count':50,
                            'checked_theorem':m['checked_theorem']})
    index = stage/'manifest-index.json'
    index.write_text(json.dumps({'schema':'centroid.generated-manifest-index.v1',
                                'revision':REVISION,'manifests':records},indent=2)+'\n')
    manifest, groups = full.validate_assembly(assembly/'manifest.json',index,
                                             project/'CentroidEscape/CandidateEndpointChecks.lean')
    if report.get('manifest_sha256') != digest(assembly/'manifest.json'):
        raise ValueError('Full report refers to a different manifest')
    artifacts,evidence,imports = full.validate_shard_reports(groups,None,report['lean_version'])
    if len(artifacts) != 5325 or report.get('shard_module_count') != len(artifacts):
        raise ValueError('Incomplete original shard module set')
    prior = {e['manifest_sha256']:e['sha256'] for e in report['shard_reports']}
    if {e['manifest_sha256']:e['sha256'] for e in evidence} != prior:
        raise ValueError('Final run used different shard reports')
    modules = manifest['modules']
    if len(modules)!=152 or [e['name'] for e in report['modules']] != [m['name'] for m in modules]:
        raise ValueError('Incomplete full assembly report')
    produced = {name:a['sha256'] for name,a in artifacts.items()}
    for item, result in zip(modules,report['modules']):
        source = full.contained_file(assembly,item['source'])
        log = full.contained_file(assembly,result['log'])
        binary = full.contained_file(assembly,result['checked_olean'])
        if (result['exit_code'] != 0 or result['source_sha256'] != digest(source)
                or digest(source) != item['sha256'] or digest(log) != result['log_sha256']
                or digest(binary) != result['olean_sha256'] or binary.stat().st_size != result['olean_bytes']):
            raise ValueError('Full assembly source/proof/log differs from checked output')
        if set(full.direct_imports(source)) != set(result['import_hashes']):
            raise ValueError('Assembly dependency evidence is incomplete')
        for name,h in result['import_hashes'].items():
            if name in produced and produced[name] != h:
                raise ValueError('Assembly uses inconsistent produced proof')
            if name in imports and imports[name] != h:
                raise ValueError('Assembly uses inconsistent shared dependency')
        produced[item['name']] = result['olean_sha256']
    audit = report['modules'][-1]
    if (modules[-1]['name'] != manifest['audit_module'] or not audit.get('audit_message_seen')
            or full.AUDIT_MESSAGE not in full.contained_file(assembly,audit['log']).read_text()):
        raise ValueError('Missing final strict audit evidence')
    if report.get('escape_theorem') != manifest['escape_theorem']:
        raise ValueError('Mismatched final theorem')
    # All checks finish before the tracked archive is created.
    dest.mkdir(parents=True)
    shutil.copy2(index,dest/'manifest-index.json')
    for record in records:
        src = stage/Path(record['manifest']).parent
        dst = dest/Path(record['manifest']).parent
        dst.mkdir(parents=True)
        for filename in ('manifest.json','compile_report.json'):
            shutil.copy2(src/filename,dst/filename)
        for dirname in ('sources','logs'):
            shutil.copytree(src/dirname,dst/dirname)
    out = dest/'assembly'
    out.mkdir()
    for filename in ('manifest.json','full_compile_report.json'):
        shutil.copy2(assembly/filename,out/filename)
    for dirname in ('sources','logs'):
        shutil.copytree(assembly/dirname,out/dirname)
    inventory = [{'path':f.relative_to(dest).as_posix(),'sha256':digest(f),'bytes':f.stat().st_size}
                 for f in sorted(dest.rglob('*')) if f.is_file()]
    summary = {'source_revision':REVISION,'verified_run':RUN,'archive_validation_passed':True,
               'original_full_lean_check_passed':True,'new_lean_check_performed':False,
               'concrete_steps':3750,'shards':75,'shard_modules':5325,'assembly_modules':152,
               'escape_theorem':manifest['escape_theorem'],
               'full_compile_report_sha256':digest(report_path),'files':inventory}
    (dest/'archive_inventory.json').write_text(json.dumps(summary,indent=2)+'\n')
    compact = {k:v for k,v in summary.items() if k!='files'}
    compact.update(archived_files=len(inventory),archived_bytes=sum(e['bytes'] for e in inventory),
                   inventory_sha256=digest(dest/'archive_inventory.json'))
    (dest/'archive_summary.json').write_text(json.dumps(compact,indent=2)+'\n')
    readme = f'''# Verified centroid-escape certificate

The complete proof was checked at `{REVISION}` in [run {RUN}](https://github.com/qumiha151-wq/lemniscate-stability-lean/actions/runs/{RUN}). All 75 concrete shards and the 152-module assembly passed. The final audit permits only `propext`, `Classical.choice`, and `Quot.sound`.

Final theorem: `{manifest['escape_theorem']}`.

It asserts existence of a smooth closed immersed classical free elastic flow with unbounded arclength centroid. It does not assert migration away from every compact set, unrestricted length growth, or a soliton classification.

This directory permanently preserves the exact checked Lean sources, manifests and logs. It omits compiled binaries. The archival job verifies source, binary and log hashes before copying these files; it is not a new kernel run. Source hashes are listed in `archive_inventory.json`.

Reproduction uses the independent CentroidEscape Lake project and its pinned Lean/mathlib version. Build its core first. Compile all 75 `shards/*/manifest.json` with `tools/compile_shard.py`, using the same `.lake/build/lib/lean` output directory. Then run `tools/compile_full_assembly.py` with this directory's `assembly/manifest.json`, `--manifest-list` pointing to this directory's `manifest-index.json`, and `--candidate-source CentroidEscape/CandidateEndpointChecks.lean`. The path overrides relocate original CI paths; all sources and manifest hashes remain checked. All CentroidEscape compiled modules must share one build root. The full workflow provides the exact bounded compilation commands.
'''
    (dest/'README.md').write_text(readme)
    print(json.dumps({k:v for k,v in summary.items() if k!='files'}))
    print(f'ARCHIVE_READY files={len(inventory)} source_bytes={sum(e["bytes"] for e in inventory)}')


if __name__=='__main__':
    main()
