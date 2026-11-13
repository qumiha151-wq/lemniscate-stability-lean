from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent;sys.path.insert(0,str(root/'rotating_formal/pipeline'))
import production_shard_release_publisher_v2 as w
import review_core_release_publisher as journal_check
where=root/'first_four_release_execution_publication';data=where/'downloaded_evidence/unpacked'
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipt=read(where/'downloaded_evidence/download_verification.json')
assert receipt['zip_sha256']=='b691f0ae337d109e522b6b5a0a6c8fac08dad9a7fed2d43e04f6d4f14401d029'
assert receipt['zip_bytes']==238825
for name,pin in receipt['files'].items():
    p=data/name;assert p.stat().st_size==pin['bytes'] and sha(p)==pin['sha256']
request=data/'evidence/approved_envelope.json';assert sha(request)=='43825fd353fc7fe02c244b30393f4f4221e9d18799950bc73c72adcc4c1b7cef'
env=read(request);q=env['original_request'];plan=data/'evidence/plan.json'
assert sha(plan)==q['plan_sha256'];w.validate_envelope(env,read(plan))
counts={}
for relative in ['origin_journal','download_journal','publication/journal']:
    events=journal_check.verify_journal(data/relative);counts[relative]=len(events)
    if relative!='publication/journal':assert all(x['event']!='mutation_intent' for x in events)
j=data/'publication/journal';events=journal_check.verify_journal(j)
assert events[0]['event']=='started' and events[-1]['event']=='finished'
intents=[x['data'] for x in events if x['event']=='mutation_intent']
assert len(intents)==7 and [x['method'] for x in intents]==['POST']*6+['PATCH']
assert intents[0]['endpoint']==w.API+'/git/refs' and intents[0]['payload']=={'ref':'refs/tags/'+q['tag'],'sha':q['source_revision']}
assert intents[1]['endpoint']==w.API+'/releases'
assert intents[-1]['endpoint']==w.API+'/releases/443812088' and intents[-1]['payload']=={'draft':False}
for job,intent in zip(q['jobs'],intents[2:6]):
    assert intent['endpoint']==w.API+'/releases/443812088/assets' and intent['upload_name']==job['asset_name']
    assert intent['bytes']==job['archive_bytes']
summary=read(j/'summary.json')
assert events[-1]['data']['summary_sha256']==sha(j/'summary.json')
assert summary['publisher']['journal_previous_sha256']==events[-1]['previous_sha256']
assert summary['status']=='remote_verified' and summary['test_fixture'] is False
assert summary['scope']=='partial' and summary['actual_http_writes']==7 and summary['full_certificate_proved'] is False
assert summary['remote_durability_verified'] is True and summary['release_id']==443812088
assert summary['publisher']['actions']=={'event':'push','run_id':43364989743,
    'tool_revision':'eab61f0d4210d8e05d27a8b5a55f2bf3df34140f',
    'workflow_revision':'340e682f87e3b89dd3a7d7f0f0ab5b838d4c27ea'}
assert summary['publisher']['script_sha256']==w.c.digest(w.__file__)
assert summary['publisher']['request_sha256']==sha(request)
downloads=read(data/'evidence/downloads.json');preflight=read(data/'publication/preflight/dry_run_plan.json')
assert len(downloads)==len(preflight['archives'])==4
raws={sha(p):read(p) for p in j.glob('*_raw_response.json')}
published=read(where/'observed_release.json')
identity=w.protocol.validate_release(published,443812088,q['tag'],q['source_revision'],draft=False)
assert len(published['assets'])==4
records=[]
for job,row,dl,pre in zip(q['jobs'],summary['records'],downloads,preflight['archives']):
    key=job['key'];assert row['key']==dl['key']==pre['key']==key
    assert dl['actual_network_download'] is True and dl['new_Lean_calls']==0
    assert dl['artifact_id']==job['origin_artifact_id'] and dl['zip_sha256']==job['origin_artifact_zip_sha256']
    assert dl['zip_bytes']==job['origin_artifact_zip_bytes'] and dl['archive_sha256']==job['archive_sha256']
    assert dl['archive_bytes']==job['archive_bytes'] and pre['complete_original_archive_validated'] is True
    path=j/'records'/(key+'.json');raw=path.read_bytes();record=json.loads(raw)
    assert len(raw)==row['record_bytes'] and sha(path)==row['record_sha256']
    w.p.durable_record(raw,row['record_sha256'],q['source_revision'],job['archive_sha256'],job['archive_bytes'])
    assert record['key']==key and record['publisher']==summary['publisher']
    assert record['plan_sha256']==q['plan_sha256'] and record['base_lock_sha256']==q['base_lock_sha256']
    assert record['release']['id']==row['release_id']==443812088
    asset=next(x for x in published['assets'] if x['id']==row['asset_id'])
    normalized=w.protocol.validate_asset(asset,identity,row['asset_id'],job['asset_name'],job['archive_sha256'],job['archive_bytes'])
    assert normalized==record['asset']
    api_asset=raws[record['verification']['asset_api_sha256']]
    assert w.protocol.validate_asset(api_asset,identity,row['asset_id'],job['asset_name'],job['archive_sha256'],job['archive_bytes'])==normalized
    api_release=raws[record['verification']['release_api_sha256']]
    assert w.protocol.validate_release(api_release,443812088,q['tag'],q['source_revision'],draft=False)==identity
    records.append({'key':key,'record_sha256':row['record_sha256'],'asset_id':row['asset_id'],
        'archive_sha256':job['archive_sha256'],'archive_bytes':job['archive_bytes']})
run=read(where/'observed_run.json')
assert run['id']==43364989743 and run['status']=='completed' and run['conclusion']=='success'
assert run['head_sha']==summary['publisher']['actions']['workflow_revision']
log=(where/'job.log').read_text(encoding='utf-8')
assert 'four_remote_records_verified' in log and '"actual_http_writes": 7' in log
result={'schema':'rotating.actual-first-four-publication-root-review.v1','status':'checked',
    'run_id':43364989743,'job_id':131687183141,'release_id':443812088,'artifact_id':14009912036,
    'downloaded_files':len(receipt['files']),'journal_event_counts':counts,
    'summary_sha256':sha(j/'summary.json'),'records':records,
    'all_downloaded_evidence_hashes_checked':True,'actual_seven_mutation_intents_checked':True,
    'actual_original_zip_download_receipts_and_full_archive_preflight_checked':True,
    'draft_and_published_full_downloads_required_by_executed_frozen_control_flow':True,
    'local_repeat_redownload_of_four_release_archives_performed':False,
    'new_Lean_calls':0,'full_certificate_proved':False}
(where/'root_postcheck.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
