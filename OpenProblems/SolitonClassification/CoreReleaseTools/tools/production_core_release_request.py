"""Dedicated Layer A-core request checks; a core is never a numerical shard.

This adapter consumes externally pinned successful pack/restore/import evidence.
It hashes the original archive without restoring six gigabytes of libraries. It
does not independently repeat Lean or infer any trajectory-certificate result.
"""
from pathlib import Path
import re
import production_release_preflight as r

c,core,require=r.c,r.core,r.require
SCHEMA='rotating.release-core-request.v1'
MAX_METADATA=16*1024**2


def helpers():
    return {**r.helpers(),Path(__file__).name:c.digest(__file__)}


def validate_request(q,publisher_sha,allow_fixture=False):
    require(set(q)=={'schema','repository','test_fixture','layer','source_revision',
        'publisher_revision','publisher_sha256','helper_sha256','tag','title','base_lock_sha256',
        'source_inventory_sha256','archive','evidence','origins'},'Wrong core request fields')
    require(q['schema']==SCHEMA and q['repository']==r.REPO and q['layer']=='original-core',
            'Wrong core publication scope')
    require(type(q['test_fixture']) is bool and (not q['test_fixture'] or allow_fixture),
            'Fixture core request forbidden in production')
    for name in ['source_revision','publisher_revision']:
        require(isinstance(q[name],str) and core.REVISION.fullmatch(q[name]),'Missing exact revision')
    for name in ['publisher_sha256','base_lock_sha256','source_inventory_sha256']:
        require(isinstance(q[name],str) and c.SHA.fullmatch(q[name]),'Invalid pinned digest')
    require(q['publisher_sha256']==publisher_sha and q['helper_sha256']==helpers(),
            'Publisher/adapter implementation differs')
    require(isinstance(q['tag'],str) and q['tag'].startswith('soliton-rotating-'+q['source_revision'][:12]+'-core-')
        and re.fullmatch('[A-Za-z0-9_.-]{1,160}',q['tag']),'Noncanonical core release tag')
    require(isinstance(q['title'],str) and 1<=len(q['title'])<=200 and '\n' not in q['title']
        and '\r' not in q['title'],'Unsafe title')
    a=q['archive']
    require(set(a)=={'file','sha256','bytes','asset_name'} and a['file']=='exact-core.tar.xz',
            'Wrong core archive fields')
    require(isinstance(a['sha256'],str) and c.SHA.fullmatch(a['sha256'])
        and type(a['bytes']) is int and 0<a['bytes']<2*1024**3,'Invalid core archive size/hash')
    require(a['asset_name']=='SolitonClassification-exact-core-'+a['sha256'][:16]+'.tar.xz',
            'Noncanonical core asset')
    require(set(q['evidence'])=={'pack','restore','imports'},'Missing upstream core evidence')
    for key,row in q['evidence'].items():
        require(set(row)=={'file','sha256','bytes'} and row['file']==key+'.json'
            and isinstance(row['sha256'],str) and c.SHA.fullmatch(row['sha256'])
            and type(row['bytes']) is int and 0<row['bytes']<=MAX_METADATA,'Invalid core evidence pin')
    require(set(q['origins'])=={'archive','producer_evidence','consumer_evidence'},'Missing live Actions origins')
    ids=set();runs=set()
    for row in q['origins'].values():
        require(set(row)=={'origin_run_id','origin_head_sha','origin_artifact_id',
            'origin_artifact_zip_sha256','origin_artifact_zip_bytes'},'Invalid Actions origin fields')
        for name in ['origin_run_id','origin_artifact_id','origin_artifact_zip_bytes']:
            require(type(row[name]) is int and row[name]>0,'Invalid Actions origin integer')
        require(row['origin_head_sha']==q['source_revision']
            and c.SHA.fullmatch(row['origin_artifact_zip_sha256']),'Wrong upstream core revision/digest')
        ids.add(row['origin_artifact_id']);runs.add(row['origin_run_id'])
    require(len(ids)==3 and len(runs)==1,'Core evidence must share one successful transfer run')


def check_evidence(q,pack,restore,imports):
    expected={'archive_sha256':q['archive']['sha256'],'revision':q['source_revision'],
        'base_lock_sha256':q['base_lock_sha256'],'source_inventory_sha256':q['source_inventory_sha256']}
    for data,schema in [(pack,'rotating.production-core-pack.v1'),
        (restore,'rotating.production-core-restore.v1'),(imports,'rotating.restored-core-import.v1')]:
        require(data.get('schema')==schema and data.get('status')=='checked'
            and all(data.get(k)==v for k,v in expected.items())
            and data.get('full_certificate_proved') is False,'Upstream core evidence identity/scope differs')
    require(pack['archive_bytes']==q['archive']['bytes'] and c.SHA.fullmatch(pack['header_sha256'])
        and restore['header_sha256']==pack['header_sha256'],'Core pack/restore disagree')
    require(restore.get('complete_restored_base_twice_checked') is True
        and restore.get('stdlib_before_after_checked') is True,'Incomplete actual restore evidence')
    require(imports.get('complete_base_before_after_checked') is True
        and imports.get('actual_fresh_private_audit') is True and imports.get('actual_arctan_import') is True
        and imports.get('used_lake_or_mathlib_cache') is False
        and imports.get('output_on_library_search_path') is False
        and imports.get('numerical_leaves_checked')==0,'Missing isolated actual import evidence')
    rows=imports['modules']
    require([x['name'] for x in rows]==['SolitonClassification.Rotating.ModuleFullGenericAudit','RestoredArctanProbe']
        and all(x.get('exit_code')==0 for x in rows),'Actual core imports failed/missing')
    require(rows[0].get('declarations')==1704 and rows[0].get('private_declarations')==331,
            'Frozen core private-audit coverage differs')
    for row in rows:
        require(row['imports_before']==row['imports_after'] and row['artifacts'],
                'Actual import identities changed')
    # The raw evidence hashes are externally pinned. No fresh Lean is run.
    return {'upstream_pack_restore_imports_checked':True,'actual_lean_run_here':False,
            'full_certificate_proved':False}


def prepare(request,request_sha,input_root,publisher_sha,allow_fixture=False):
    path=core.plain_path(request,'file');root=core.plain_path(input_root,'dir')
    require(path.stat().st_size<=r.REQUEST_LIMIT and c.digest(path)==request_sha,'External core request pin differs')
    raw=path.read_bytes();q=core.strict_json(raw)
    validate_request(q,publisher_sha,allow_fixture)
    pinned={path:request_sha};evidence={}
    for key,row in q['evidence'].items():
        f=core.plain_path(c.confined(root,row['file']),'file')
        require(f.stat().st_size==row['bytes'] and c.digest(f)==row['sha256'],'Core evidence bytes differ')
        pinned[f]=row['sha256'];evidence[key]=core.strict_json(f.read_bytes())
    checked=check_evidence(q,**evidence)
    a=q['archive'];archive=core.plain_path(c.confined(root,a['file']),'file')
    require(archive.stat().st_size==a['bytes'] and c.digest(archive)==a['sha256'],'Core original bytes differ')
    pinned[archive]=a['sha256']
    return {'request':q,'request_raw':raw,'request_sha256':request_sha,'archive':archive,
        'pinned_files':pinned,'helpers':helpers(),'scope':checked}


def recheck(ctx,publisher_sha):
    require(ctx['helpers']==helpers() and ctx['request']['publisher_sha256']==publisher_sha,
            'Publication helpers changed')
    for path,digest in ctx['pinned_files'].items():
        require(core.plain_path(path,'file')==path and c.digest(path)==digest,'Pinned publication input changed')
