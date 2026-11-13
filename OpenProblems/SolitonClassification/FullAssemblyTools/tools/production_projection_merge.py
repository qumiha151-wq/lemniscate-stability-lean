"""Merge externally pinned compact projections with explicit pilot/full scope.

Preparing public inputs is not a Lean execution or a proof of seam equalities.
Full mode requires250 durable receipts; pilot mode admits at most8 named jobs.
"""
from pathlib import Path
from types import SimpleNamespace
import argparse, json, shutil
import production_projection_transport as transport

p = transport.projection
core, compiler, require = transport.core, transport.compiler, transport.require
SCHEMA = 'rotating.public-projection-ledger.v1'
LEDGER_LIMIT = 4*1024*1024
CAPS = {'public_bytes':1024**3, 'metadata_bytes':256*1024**2, 'receipt_bytes':16*1024**2}


def helpers():
    return {**transport.helpers(), Path(__file__).name:compiler.digest(__file__)}


def base_primary_paths(base):
    return {name.split('/',1)[1].casefold() for name in base['files']
            if name.casefold().endswith('.olean')}


def check_no_core_shadow(relative, base_paths):
    require(relative.casefold() not in base_paths, 'Projection shadows a core module (case-folded)')


def validate_ledger(ledger, plan, mode):
    require(set(ledger) == {'schema','mode','source_revision','publication_revision','plan_sha256',
        'base_lock_sha256','candidate_id','candidate_hash','orders','mesh','step','jobs',
        'projection_helper_sha256','transport_helper_sha256'}, 'Wrong ledger fields')
    require(ledger['schema'] == SCHEMA and ledger['mode'] == mode, 'Wrong ledger scope')
    require(mode in ('pilot','full') and ledger['source_revision'] == plan['revision'], 'Wrong source identity')
    pub = ledger['publication_revision']
    require((pub is None and mode == 'pilot') or (isinstance(pub,str) and core.REVISION.fullmatch(pub)),
            'Full ledger needs an explicit publication revision')
    for field in ['candidate_id','candidate_hash','orders','mesh','step']:
        require(ledger[field] == plan[field], 'Ledger candidate mismatch: '+field)
    require(ledger['projection_helper_sha256'] == p.helpers()
            and ledger['transport_helper_sha256'] == transport.helpers(), 'Wrong locked projection/transport code')
    jobs = ledger['jobs']
    require(isinstance(jobs,list) and (len(jobs)==250 if mode=='full' else 1<=len(jobs)<=8),
            'Missing/full or oversized pilot coverage')
    expected = {j['key']:(i,j) for i,j in enumerate(plan['jobs'])}
    indexes, seen, files, totals = [], set(), set(), dict.fromkeys(CAPS,0)
    fields = {'key','sign','start','count','input_node_sha256','output_node_sha256',
        'full_archive_sha256','full_archive_bytes','receipt_sha256','durable_record_sha256',
        'transport_file','transport_sha256','transport_bytes','public_bytes','metadata_bytes','receipt_bytes'}
    for job in jobs:
        require(set(job)==fields and job['key'] in expected and job['key'].casefold() not in seen,
                'Unknown/duplicate job or wrong job fields')
        seen.add(job['key'].casefold())
        index, original = expected[job['key']]
        indexes.append(index)
        for field in ['key','sign','start','count','input_node_sha256','output_node_sha256']:
            require(job[field] == original[field], 'Wrong job/checkpoint coverage: '+field)
        for field in ['full_archive_sha256','receipt_sha256','transport_sha256']:
            require(isinstance(job[field],str) and compiler.SHA.fullmatch(job[field]), 'Wrong job digest')
        durable = job['durable_record_sha256']
        require((durable is None and mode=='pilot') or (isinstance(durable,str) and compiler.SHA.fullmatch(durable)),
                'Missing durable publisher record for full mode')
        require(job['transport_file'] == job['key']+'.public.tar.xz'
                and job['transport_file'].casefold() not in files, 'Duplicate/noncanonical transport filename')
        files.add(job['transport_file'].casefold())
        for field in ['full_archive_bytes','transport_bytes',*CAPS]:
            require(type(job[field]) is int and job[field] > 0, 'Wrong job size')
        require(job['public_bytes'] <= 4*1024**2 and job['metadata_bytes'] <= 8*1024**2
                and job['receipt_bytes'] <= p.RECEIPT_LIMIT
                and job['transport_bytes'] <= transport.MAX_EXPANDED, 'Per-job size limit exceeded')
        for field in CAPS:
            totals[field] += job[field]
    require(indexes == sorted(indexes), 'Reordered signed job coverage')
    if mode == 'full':
        require(indexes == list(range(250)), 'Incomplete exact250 coverage')
    require(all(totals[n] <= CAPS[n] for n in CAPS), 'Global aggregate size budget exceeded')
    return totals


def locked_inputs(args):
    ledger_path = core.plain_path(args.ledger,'file')
    require(ledger_path.stat().st_size <= LEDGER_LIMIT and compiler.digest(ledger_path)==args.ledger_sha256,
            'Ledger size or externally pinned digest differs')
    ledger = core.strict_json(ledger_path.read_bytes())
    require(ledger['plan_sha256']==args.plan_sha256 and ledger['base_lock_sha256']==args.base_lock_sha256,
            'Ledger independent plan/core identity differs')
    _, plan, _ = p.bound_plan(args.plan,args.plan_sha256,args.revision,'RP0000')
    totals = validate_ledger(ledger,plan,args.mode)
    base_path = core.plain_path(args.base_lock,'file')
    require(compiler.digest(base_path)==args.base_lock_sha256, 'Base-lock bytes differ')
    base = core.strict_json(base_path.read_bytes())
    core.validate_lock(base)
    return ledger,plan,base,totals


def merge(args):
    ledger,plan,base,totals = locked_inputs(args)
    archives = core.plain_path(args.archive_root,'dir')
    output = core.fresh_path(args.output)
    require(not output.is_relative_to(archives) and not archives.is_relative_to(output),
            'Merge output and input archives overlap')
    before = helpers()
    core_primaries = base_primary_paths(base)
    # Fresh runner capacity is measured, never inferred from its advertised size.
    existing = output.parent
    while not existing.exists():
        existing = existing.parent
    required = sum(totals.values()) + transport.MAX_EXPANDED + args.reserve_bytes
    require(args.reserve_bytes >= 0 and shutil.disk_usage(existing).free >= required,
            'Insufficient actual free disk for bounded merge and reserve')
    output.mkdir(parents=True,exist_ok=False)
    scratch = output/'_one_projection_stage'
    files, modules, folded, jobs = {}, {}, set(), []

    def copy(source, relative, expected):
        require(relative not in files, 'Repeated destination')
        target = compiler.confined(output,relative)
        core.plain_path(source,'file')
        data = source.read_bytes()
        require(len(data)==expected['bytes'] and p.sha(data)==expected['sha256'], 'Changed staged input')
        core.write_new(target,data)
        files[relative] = expected

    for job in ledger['jobs']:
        archive = compiler.confined(archives,job['transport_file'])
        require(archive.stat().st_size==job['transport_bytes'], 'Compact transport size differs')
        context = SimpleNamespace(plan=args.plan,plan_sha256=args.plan_sha256,revision=args.revision,
            key=job['key'],archive_sha256=job['full_archive_sha256'],
            base_lock_sha256=args.base_lock_sha256,receipt_sha256=job['receipt_sha256'],
            durable_record_sha256=job['durable_record_sha256'],require_durable=args.mode=='full',
            max_public_mb=4,max_metadata_mb=8,archive=archive,output=scratch,
            transport_sha256=job['transport_sha256'])
        try:
            receipt = transport.unpack(context)
            for field in ['public_bytes','metadata_bytes','full_archive_bytes']:
                require(receipt[field]==job[field], 'Ledger and actual projection size differ')
            require((scratch/'projection.json').stat().st_size==job['receipt_bytes'], 'Receipt size differs')
            if args.mode=='full':
                publisher = core.strict_json((scratch/'metadata/durable_record.json').read_bytes())
                require(publisher['release'].get('draft') is False
                    and isinstance(publisher['release'].get('published_at'),str)
                    and publisher['release']['published_at'], 'Full ledger requires a published release record')
            for name in receipt['modules']:
                require(name.casefold() not in folded, 'Duplicate/case-fold module across projections')
                relative = compiler.module_file(name)
                check_no_core_shadow(relative,core_primaries)
                folded.add(name.casefold())
                record = receipt['files']['public/'+relative]
                copy(scratch/'public'/relative, 'public/'+relative, record)
                modules[name] = record
            for name, record in receipt['files'].items():
                if name.startswith('metadata/'):
                    copy(scratch/name,'evidence/'+job['key']+'/'+name,record)
            for name in ['projection.json','projection.sha256']:
                path = scratch/name
                copy(path,'evidence/'+job['key']+'/'+name,
                     {'bytes':path.stat().st_size,'sha256':compiler.digest(path)})
            jobs.append({'key':job['key'],'receipt_sha256':job['receipt_sha256'],
                         'full_archive_sha256':job['full_archive_sha256']})
        finally:
            if scratch.exists():
                target = core.plain_path(scratch,'dir').resolve()
                require(target.parent==output.resolve() and target.name=='_one_projection_stage',
                        'Unsafe owned scratch cleanup')
                shutil.rmtree(target)
    # Recheck exact files, all transport bytes and all externally pinned inputs.
    actual = set()
    for path in output.rglob('*'):
        core.plain_path(path)
        if path.is_file():
            actual.add(path.relative_to(output).as_posix())
    require(actual==set(files), 'Extra/missing merged file')
    for relative,record in files.items():
        path = compiler.confined(output,relative)
        require(path.stat().st_size==record['bytes'] and compiler.digest(path)==record['sha256'],
                'Merged file changed before finalization')
    for job in ledger['jobs']:
        archive = compiler.confined(archives,job['transport_file'])
        require(compiler.digest(archive)==job['transport_sha256'], 'Original compact archive changed')
    again = locked_inputs(args)
    require(again==(ledger,plan,base,totals) and helpers()==before, 'Merge bindings/tools changed')
    result = {'schema':'rotating.public-merge-receipt.v1','status':'inputs_prepared',
        'mode':args.mode,'revision':args.revision,'ledger_sha256':args.ledger_sha256,
        'plan_sha256':args.plan_sha256,'base_lock_sha256':args.base_lock_sha256,
        'jobs':jobs,'modules':modules,'files':files,'aggregate_bytes':totals,'helper_sha256':before,
        'all_250_projections_validated':args.mode=='full',
        'actual_lean_import_checked':False,'external_library_snapshot_checked':False,
        'inter_shard_seams_proved':False,'full_certificate_proved':False,
        'original_archives_deleted':False}
    raw = core.json_bytes(result)
    core.write_new(output/'merge_receipt.json',raw)
    core.write_new(output/'merge_receipt.sha256',(p.sha(raw)+'\n').encode())
    print(json.dumps({'status':'inputs_prepared','mode':args.mode,'jobs':len(jobs),
                     'modules':len(modules),'receipt_sha256':p.sha(raw),
                     'actual_lean_import_checked':False,'full_certificate_proved':False}),flush=True)
    return result


def main():
    cli=argparse.ArgumentParser(description=__doc__)
    for name in ['ledger','plan','base-lock','archive-root','output']:
        cli.add_argument('--'+name,type=Path,required=True)
    for name in ['ledger-sha256','plan-sha256','base-lock-sha256','revision']:
        cli.add_argument('--'+name,required=True)
    cli.add_argument('--mode',choices=['pilot','full'],required=True)
    cli.add_argument('--reserve-bytes',type=int,default=2*1024**3)
    merge(cli.parse_args())


if __name__=='__main__':
    main()
