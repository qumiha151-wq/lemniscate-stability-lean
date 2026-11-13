"""Verify with the trusted local launcher, never execute a supplied package."""
from pathlib import Path
import argparse,importlib.util,json


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--package',type=Path,required=True);ap.add_argument('--manifest-sha256',required=True)
    args=ap.parse_args()
    source=Path(__file__).resolve().with_name('shard_release_v3_launch.py')
    spec=importlib.util.spec_from_file_location('trusted_local_v3_launcher',source)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    result=module.verify_package(args.package,args.manifest_sha256)
    print(json.dumps({'status':'local_inventory_checked','manifest_sha256':args.manifest_sha256,
        'runtime_helpers':len(result['manifest']['runtime_helper_sha256']),'files':len(result['files']),
        'actual_committed_revision_checked':False,'actual_network_requests':0,'actual_Lean_calls':0}))
