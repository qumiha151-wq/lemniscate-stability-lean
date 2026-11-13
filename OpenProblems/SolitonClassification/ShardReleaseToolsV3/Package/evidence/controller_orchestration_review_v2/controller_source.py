"""One-batch orchestration library; no CLI, retries, waits or remote cleanup.

Production uses only the frozen public outer/publisher entry points. The
separate fixture entry injects orchestration phases and cannot emit a
production result. It does not patch any production library.
"""
from pathlib import Path
from dataclasses import dataclass
from urllib.error import HTTPError
import os,re,subprocess
import production_shard_zip_download as d

v,w,p,c,core,require=d.v,d.w,d.p,d.c,d.core,d.require
SCHEMA='rotating.shard-release-controller.v1'
OUTER_SHA='8e9905c801cf08d4f4697b2fabae3b22ee5c4dfed28267d7b1f0dc2eb7e30f65'


def helpers():
    values={**d.helpers(),Path(__file__).name:c.digest(__file__)}
    require(values.get(Path(d.__file__).name)==OUTER_SHA,'Frozen outer library differs')
    return values


def git(root,*args):
    env=os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):env.pop(key)
    return subprocess.run(['git','-C',str(root),*args],env=env,check=True,
        stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30).stdout


def checked_tools():
    revision=d.checked_tool_revision();directory=Path(__file__).resolve().parent
    top=core.plain_path(Path(git(directory,'rev-parse','--show-toplevel').decode().strip()),'dir').resolve()
    expected=helpers()
    require({x.name for x in directory.glob('*.py')}==set(expected),'Extra/missing Python tool helper')
    require(not list(directory.rglob('__pycache__')),'Cached Python inputs forbidden')
    require({x.resolve() for x in directory.rglob('*.py')}=={directory/n for n in expected},
        'Nested Python tool helper forbidden')
    for name,digest in expected.items():
        source=core.plain_path(directory/name,'file').resolve()
        require(source.parent==directory and source.is_relative_to(top)
            and c.digest(source)==digest and git(top,'show','HEAD:'+source.relative_to(top).as_posix())==source.read_bytes(),
            'Controller/helper is not its actual committed blob')
    require(git(directory,'rev-parse','HEAD').decode().strip()==revision,'Tool revision changed')
    return revision


def input_identity(ctx,environment):
    qrev=environment.get('GITHUB_SHA','');require(core.REVISION.fullmatch(qrev),'Missing actual workflow revision')
    root=core.plain_path(ctx['input_checkout'],'dir').resolve()
    require(Path(git(root,'rev-parse','--show-toplevel').decode().strip()).resolve()==root
        and git(root,'rev-parse','HEAD').decode().strip()==qrev,'Input checkout is not this workflow revision')
    require(qrev!=ctx['request']['publisher_revision'],'Tool and later input commit must be distinct')
    for path,digest in ctx['pins'].items():
        source=core.plain_path(path,'file').resolve()
        require(source.is_relative_to(root) and c.digest(source)==digest
            and git(root,'show','HEAD:'+source.relative_to(root).as_posix())==source.read_bytes(),
            'Input is not its actual workflow-commit blob')
    return {'input_revision':qrev,'same_execution_GITHUB_SHA_check':True,
        'independent_external_Q_pin_performed_here':False}


def prepare(*,request,request_sha256,plan,plan_sha256,catalog,catalog_sha256,
            output,helper_sha256,input_checkout=None,_fixture=False):
    require(type(_fixture) is bool,'Explicit fixture boundary')
    paths=[core.plain_path(x,'file') for x in (request,plan,catalog)]
    request,plan,catalog=paths;output=core.fresh_path(output)
    require(helper_sha256==helpers(),'Controller/helper hash set differs')
    pins=dict(zip(paths,(request_sha256,plan_sha256,catalog_sha256)))
    require(len(pins)==3 and all(c.SHA.fullmatch(h) and c.digest(f)==h for f,h in pins.items()),'Wrong immutable input tuple')
    require(request.stat().st_size<=v.r.REQUEST_LIMIT and catalog.stat().st_size<=v.origin.LIMIT,'Oversized controller input')
    envelope=core.strict_json(request.read_bytes());cat=core.strict_json(catalog.read_bytes());q=envelope['original_request']
    _,plan_data,_=p.bound_plan(plan,plan_sha256,q['source_revision'],'RP0000')
    # bound_plan also reads every checkpoint. They are an explicit immutable
    # part of the plan closure, not ambient unrecorded files.
    for job in plan_data['jobs']:
        node=core.plain_path(c.confined(plan.parent,job['output_node']),'file')
        require(node not in pins and c.digest(node)==job['output_node_sha256'],'Mixed plan attachment')
        pins[node]=job['output_node_sha256']
    v.validate_envelope(envelope,plan_data,cat,_fixture)
    require(q['test_fixture'] is _fixture and envelope['origin_catalog_sha256']==catalog_sha256
        and q['plan_sha256']==plan_sha256,'Mixed fixture/plan/catalog inputs')
    require(all(not f.resolve().is_relative_to(output.resolve()) for f in paths),'Output overlaps inputs')
    require(not output.resolve().is_relative_to(Path(__file__).resolve().parent),'Output overlaps tool directory')
    if not _fixture:
        root=core.plain_path(input_checkout,'dir').resolve()
        require(not output.resolve().is_relative_to(root) and not root.is_relative_to(output.resolve()),'Output overlaps input checkout')
    else:root=None
    return {'request_path':request,'request_sha256':request_sha256,'plan_path':plan,'plan_sha256':plan_sha256,
        'catalog_path':catalog,'catalog_sha256':catalog_sha256,'envelope':envelope,'request':q,'catalog':cat,
        'output':output,'helper_sha256':helper_sha256,'pins':pins,'fixture':_fixture,'input_checkout':root}


def recheck(ctx,environment):
    require(helpers()==ctx['helper_sha256'] and all(c.digest(core.plain_path(f,'file'))==h for f,h in ctx['pins'].items()),
        'Controller input/helper changed')
    require(core.strict_json(ctx['request_path'].read_bytes())==ctx['envelope']
        and ctx['envelope']['original_request']==ctx['request']
        and core.strict_json(ctx['catalog_path'].read_bytes())==ctx['catalog'],'Controller context changed')
    if not ctx['fixture']:
        actual=checked_tools();w.actions_context(ctx['request'],environment,actual)
        input_identity(ctx,environment)


def arguments(ctx):
    return (ctx['request_path'],ctx['request_sha256'],ctx['plan_path'],ctx['plan_sha256'],
        ctx['catalog_path'],ctx['catalog_sha256'])


def inventory(root):
    out={}
    for path in root.rglob('*'):
        require(not path.is_symlink() and not getattr(path,'is_junction',lambda:False)(),'Link in controller evidence')
        if path.is_file():
            core.plain_path(path,'file');out[path.relative_to(root).as_posix()]={'sha256':c.digest(path),'bytes':path.stat().st_size}
        else:require(path.is_dir(),'Special controller evidence')
    return out


def exact_files(root,expected):
    actual=inventory(root);require(set(actual)==set(expected),'Extra/missing stage evidence')
    for name,wanted in expected.items():require(actual[name]==wanted,'Changed stage evidence')
    return actual


def verify_download(ctx,receipt):
    root=ctx['output']/'download';q=ctx['request'];fixture=ctx['fixture']
    require(receipt==core.strict_json((root/'receipt.json').read_bytes())
        and receipt['schema']=='rotating.original-zip-download.v1'
        and receipt['status']==('fixture_only' if fixture else 'checked')
        and receipt['test_fixture'] is fixture and receipt['remote_writes']==0
        and receipt['full_bundle_preflight_here'] is False,'Invalid outer-stage result')
    for key in ('request_sha256','plan_sha256','catalog_sha256'):
        require(receipt[key]==ctx[key],'Outer immutable input differs')
    require(receipt['source_revision']==q['source_revision'] and receipt['publisher_revision']==q['publisher_revision']
        and receipt['base_lock_sha256']==q['base_lock_sha256'],'Outer identity differs')
    require([x['key'] for x in receipt['records']]==[j['key'] for j in q['jobs']],'Outer coverage differs')
    for row,job in zip(receipt['records'],q['jobs']):
        require(row['origin_artifact_id']==job['origin_artifact_id']
            and row['archive_sha256']==job['archive_sha256'] and row['archive_bytes']==job['archive_bytes'],
            'Outer archive identity differs')
    expected=dict(receipt['checked_files']);f=root/'receipt.json'
    require('receipt.json' not in expected,'Self-referential outer receipt')
    expected['receipt.json']={'sha256':c.digest(f),'bytes':f.stat().st_size}
    return exact_files(root,expected)


def verify_preflight(ctx,pctx):
    require(pctx['request_path']==ctx['request_path'] and pctx['plan_path']==ctx['plan_path']
        and pctx['catalog_path']==ctx['catalog_path'] and pctx['archive_root']==ctx['output']/'download/archives'
        and pctx['output']==ctx['output']/'publication','Different preflight paths')
    for key in ('request_sha256','plan_sha256','catalog_sha256'):
        require(pctx[key]==ctx[key],'Different preflight hashes')
    report=pctx['preflight'];q=ctx['request']
    require(report['status']=='local_preflight_checked' and report['test_fixture'] is ctx['fixture']
        and [x['key'] for x in report['archives']]==[j['key'] for j in q['jobs']],'Invalid preflight/coverage')
    require(all(x['complete_original_archive_validated'] is True and x['original_retained'] is True
        and x['archive_sha256']==j['archive_sha256'] and x['archive_bytes']==j['archive_bytes']
        for x,j in zip(report['archives'],q['jobs'])),'Preflight original differs')
    root=pctx['output'];paths=['envelope.json','original_request.json','preflight/dry_run_plan.json']
    require(core.strict_json((root/paths[2]).read_bytes())==report,'Preflight report file differs')
    return exact_files(root,{n:{'sha256':c.digest(root/n),'bytes':(root/n).stat().st_size} for n in paths})


def journal_files(journal,extra=()):
    root=journal.root;events=[];expected=set(extra);previous=None
    for path in root.glob('*.json'):
        if re.fullmatch('[0-9]{5}_[a-z_]+[.]json',path.name) and not path.name.endswith('_raw_response.json'):
            events.append(path)
    for number,path in enumerate(sorted(events)):
        row=core.strict_json(path.read_bytes())
        require(row['schema']=='rotating.release-journal-event.v1' and row['sequence']==number
            and row['previous_sha256']==previous and path.name==str(number).zfill(5)+'_'+row['event']+'.json',
            'Changed journal hash chain')
        previous=c.digest(path);expected.add(path.relative_to(root).as_posix())
        if row['event']=='api_response':
            data=row['data'];raw=root/data['file']
            require(data['file']==str(number).zfill(5)+'_raw_response.json'
                and c.digest(core.plain_path(raw,'file'))==data['sha256'] and raw.stat().st_size==data['bytes'],
                'Changed raw response')
            expected.add(data['file'])
    require(len(events)==journal.number and previous==journal.previous,'Journal live tail differs')
    require(set(inventory(root))==expected,'Extra/missing journal evidence')
    return inventory(root)


def verify_publication(ctx,summary,journal):
    q=ctx['request'];fixture=ctx['fixture'];root=journal.root
    require(summary==core.strict_json((root/'summary.json').read_bytes())
        and summary['schema']=='rotating.shard-release-summary.v3'
        and summary['status']==('fixture_only' if fixture else 'remote_verified')
        and summary['test_fixture'] is fixture and summary['remote_durability_verified'] is (not fixture)
        and summary['scope']=='partial' and summary['full_certificate_proved'] is False
        and summary['actual_http_writes']==len(q['jobs'])+3,'Invalid publication result')
    for key in ('request_sha256','plan_sha256','catalog_sha256'):
        require(summary[key]==ctx[key],'Publication immutable input differs')
    require(summary['source_revision']==q['source_revision'] and summary['base_lock_sha256']==q['base_lock_sha256']
        and summary['tag']==q['tag'] and summary['publisher']['revision']==q['publisher_revision']
        and summary['publisher']['script_sha256']==c.digest(v.__file__),'Publication source/tool differs')
    require([x['key'] for x in summary['records']]==[j['key'] for j in q['jobs']],'Publication coverage differs')
    extras={'summary.json'}
    for row,job in zip(summary['records'],q['jobs']):
        path=root/'records'/(job['key']+'.json');raw=core.plain_path(path,'file').read_bytes()
        require(p.sha(raw)==row['record_sha256'] and len(raw)==row['record_bytes']
            and row['archive_sha256']==job['archive_sha256'] and row['archive_bytes']==job['archive_bytes']
            and row['release_id']==summary['release_id'],'Durable record identity differs')
        if not fixture:p.durable_record(raw,row['record_sha256'],q['source_revision'],job['archive_sha256'],job['archive_bytes'])
        else:require(core.strict_json(raw).get('test_fixture') is True,'Fixture record cannot impersonate production')
        extras.add(path.relative_to(root).as_posix())
    return journal_files(journal,extras)


@dataclass(frozen=True)
class FixturePhases:
    """Injected orchestration-only phases. Never accepted by execute()."""
    outer_prepare:object
    outer_download:object
    publisher_prepare:object
    publisher_publish:object


def _orchestrate(ctx,phases,token,environment):
    recheck(ctx,environment);w.durable_directory(ctx['output']);log=w.Journal(ctx['output']/'controller')
    phase='started';download=None;pctx=None;release_journal=None;summary=None
    log.event('started',{'schema':SCHEMA,'test_fixture':ctx['fixture'],'request_sha256':ctx['request_sha256'],
        'catalog_sha256':ctx['catalog_sha256'],'helper_sha256':ctx['helper_sha256'],
        'input_identity':None if ctx['fixture'] else input_identity(ctx,environment),
        'automatic_retry':False,'full_certificate_proved':False})
    try:
        phase='outer_prepare';dc=phases.outer_prepare(*arguments(ctx),ctx['output']/'download',allow_fixture=ctx['fixture'])
        phase='outer_download';download=phases.outer_download(dc,token=token,environment=environment)
        download_files=verify_download(ctx,download);recheck(ctx,environment)
        log.event('outer_checked',{'receipt_sha256':c.digest(ctx['output']/'download/receipt.json'),'remote_writes':0})
        phase='full_preflight';pctx=phases.publisher_prepare(*arguments(ctx),ctx['output']/'download/archives',
            ctx['output']/'publication',allow_fixture=ctx['fixture'])
        preflight_files=verify_preflight(ctx,pctx);recheck(ctx,environment)
        log.event('preflight_checked',{'report_sha256':c.digest(ctx['output']/'publication/preflight/dry_run_plan.json'),
            'actual_network_here':False})
        phase='publisher';release_journal=w.Journal(ctx['output']/'release_journal')
        summary=phases.publisher_publish(pctx,release_journal,token=token,environment=environment)
        phase='final_postcheck';release_files=verify_publication(ctx,summary,release_journal)
        require(verify_download(ctx,download)==download_files and verify_preflight(ctx,pctx)==preflight_files,
            'Earlier stage changed during publication')
        recheck(ctx,environment)
        log.event('ready_to_record',{'summary_sha256':c.digest(release_journal.root/'summary.json'),
            'test_fixture':ctx['fixture'],'remote_publication_returned':True})
        expected={}
        for prefix,values in (('controller',journal_files(log)),('download',download_files),
                ('publication',preflight_files),('release_journal',release_files)):
            expected.update({prefix+'/'+name:value for name,value in values.items()})
        exact_files(ctx['output'],expected)
        w.durable_new(ctx['output']/'checked_files.json',core.json_bytes(expected))
        result={'schema':SCHEMA,'status':'fixture_orchestration_only' if ctx['fixture'] else 'checked',
            'test_fixture':ctx['fixture'],'request_sha256':ctx['request_sha256'],'plan_sha256':ctx['plan_sha256'],
            'catalog_sha256':ctx['catalog_sha256'],'helper_sha256':ctx['helper_sha256'],
            'inventory_sha256':c.digest(ctx['output']/'checked_files.json'),
            'release_summary_sha256':c.digest(release_journal.root/'summary.json'),
            'release_id':summary['release_id'],'record_keys':[x['key'] for x in summary['records']],
            'remote_durability_verified':not ctx['fixture'],'actual_Lean_calls':0,
            'full_certificate_proved':False,'automatic_retry':False,'remote_cleanup':False,
            'runner_loss_survival_claimed':False,'independent_external_Q_pin_performed_here':False}
        w.durable_new(ctx['output']/'receipt.json',core.json_bytes(result));return result
    except Exception as error:
        # Do not replace real mutation history with an inferred writes=0 claim.
        try:
            log.event('failed',{'phase':phase,'exception_type':type(error).__name__,
                'http_status':error.code if isinstance(error,HTTPError) else None,
                'publisher_started':release_journal is not None,'publisher_returned':summary is not None,
                'remote_writes_not_inferred':True,'remote_cleanup':False,'automatic_retry':False,
                'originals_explicitly_deleted':False,'recovery_requires_separate_review':release_journal is not None})
            try:observed={'files':inventory(ctx['output'])}
            except Exception as inventory_error:observed={'inventory_failed':type(inventory_error).__name__}
            w.durable_new(ctx['output']/'failure_inventory.json',core.json_bytes({
                'status':'observed_partial_not_verified',**observed,'phase':phase,
                'test_fixture':ctx['fixture'],'full_certificate_proved':False}))
        except Exception:
            # A failed disk/journal operation cannot turn the original failure
            # into success or replace its diagnostic exception with a new one.
            pass
        raise


def execute(ctx,*,token,environment=None):
    """Production only: fixed public phases, no caller-supplied HTTP/hooks."""
    require(ctx['fixture'] is False and ctx['request']['test_fixture'] is False,'Fixture cannot execute production')
    require(isinstance(token,str) and token,'Explicit publisher credential required')
    phases=FixturePhases(d.prepare,d.download_with_budget,v.prepare,v.publish_with_budget)
    return _orchestrate(ctx,phases,token,dict(os.environ if environment is None else environment))


def execute_fixture(ctx,phases):
    """Local orchestration fixture. No production credential or result."""
    require(ctx['fixture'] is True and ctx['request']['test_fixture'] is True
        and isinstance(phases,FixturePhases),'Not an explicit orchestration fixture')
    return _orchestrate(ctx,phases,'fixture-only-no-production-token',{})
