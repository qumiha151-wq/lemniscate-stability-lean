"""Build local immutable v3 tools bytes; never create deployment inputs."""
from pathlib import Path
import argparse,importlib.util,json,shutil
import production_shard_release_controller as controller

EVIDENCE=(
 'ShardV3ControllerFrozenManifest.json','ShardPublisherV3LocalMilestone.json','ShardZipLibraryLocalMilestone.txt',
 'controller_orchestration_review_v2/report.json','controller_orchestration_review_v2/controller_source.py',
 'controller_orchestration_review_v2/test_source.py','controller_final_recheck_review_v1/report.json',
 'pipeline/review_controller_final_recheck.py','shard_zip_completion_review_v1/report.json',
 'pipeline/review_shard_zip_completion.py','shard_release_v3_review_v1/report.json',
 'shard_release_v3_phase_corrected_v1/report.json','pipeline/review_shard_v3_phase_faults.py',
 'performance/ShardControllerRootReview.txt','performance/ShardControllerIndependentReview.txt',
 'performance/ShardV3OuterDownloadRootReview.txt','performance/ShardV3LauncherPackageDesign.txt')


def trusted_launcher(path):
    spec=importlib.util.spec_from_file_location('trusted_local_v3_launcher',path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


def build(formal_root,output):
    root=formal_root.resolve();launch=root/'pipeline/shard_release_v3_launch.py';v=trusted_launcher(launch)
    v.ordinary(root,'dir');v.require(not output.exists(),'Fresh output required')
    v.require(controller.helpers()==v.FROZEN_RUNTIME,'Frozen runtime closure differs')
    selected={}
    for name,digest in v.FROZEN_RUNTIME.items():
        source=Path(controller.p.planner.reference.__file__) if name=='reference.py' else root/'pipeline'/name
        v.ordinary(source,'file');v.require(v.digest(source)==digest,'Frozen runtime source differs')
        selected['runtime/'+name]=(source,'runtime')
    selected['launcher/launch.py']=(launch,'launcher')
    for name in EVIDENCE:
        v.safe_relative(name);source=root/name;v.ordinary(source,'file')
        selected['evidence/'+name]=(source,'evidence')
    for source in (Path(__file__),root/'pipeline/verify_shard_release_v3_tools.py'):
        v.ordinary(source,'file');selected['evidence/preparation/'+source.name]=(source,'evidence')
    before={str(source):v.digest(source) for source,role in selected.values()}
    output.mkdir(parents=True)
    rows=[]
    for name,(source,role) in sorted(selected.items()):
        target=output/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
        rows.append({'path':name,'bytes':target.stat().st_size,'sha256':v.digest(target),'role':role})
    readme=output/'README.txt'
    readme.write_text('''Rotating shard release tools v3: local library/launcher package.\n
The runtime directory contains exactly 18 frozen helpers. The launcher is a
sibling, and requires Python -I -S -B plus an externally pinned manifest SHA
and actual committed tool revision. Token is read only from GH_TOKEN.

This package creates no real remaining246 catalog, release request or Actions
workflow. Its manifest has no self-hash or P/Q. Root must independently verify
the actual tool commit and the later input/workflow commit before execution.

Tests in evidence distinguish orchestration stubs, local Git identity, local
archive bytes, in-memory HTTP, and actual Lean/cloud evidence. No local test
is promoted to a live release. Large raw fixtures remain in the author's
workspace/original durable archives and are not silently embedded here.

Success compact evidence excludes original ZIP/tar bodies; failure recovery
lists safe original tar paths without copying or deleting those originals.
Evidence retention in Actions is temporary. Complete classification and the
full numerical theorem are not claimed by this publication tool package.
''',encoding='utf-8',newline='\n')
    rows.append({'path':'README.txt','bytes':readme.stat().st_size,'sha256':v.digest(readme),'role':'readme'})
    data={'schema':v.SCHEMA,'runtime_helper_sha256':v.FROZEN_RUNTIME,'launcher_path':'launcher/launch.py',
        'files':sorted(rows,key=lambda x:x['path']),'status':'local_checked_not_deployed',
        'full_certificate_proved':False,'deployment_YAML_generated':False,'production_catalog_generated':False}
    manifest=output/'package_manifest.json';v.write_new(manifest,data);sha=v.digest(manifest)
    v.verify_package(output,sha)
    v.require(all(v.digest(Path(path))==wanted for path,wanted in before.items()),'Source changed during packaging')
    v.verify_package(output,sha)
    return {'schema':'rotating.v3-tools-local-package-build.v1','status':'local_package_checked',
        'manifest_sha256':sha,'files':len(rows),'bytes':sum(x['bytes'] for x in rows),'runtime_helpers':len(v.FROZEN_RUNTIME),
        'source_sha256':before,'actual_network_requests':0,'actual_Lean_calls':0,'deployment_YAML_generated':False,
        'production_catalog_generated':False,'actual_committed_tool_revision':None}


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--formal-root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();print(json.dumps(build(args.formal_root,args.output),sort_keys=True))
