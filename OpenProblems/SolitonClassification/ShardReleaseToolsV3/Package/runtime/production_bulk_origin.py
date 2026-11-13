"""Strict bulk origin catalog observations; never creates a production catalog."""
import re
import production_shard_release_publisher_v2 as v

SCHEMA='rotating.bulk-origin-catalog.v1'
SOURCE='cff971bcac7ac2d83aba04596ce09e44fda1ac29'
PLAN='a62ef654ec4f2fd01d55b6dae19c28483dba137c424c3068a372c514b89559c1'
BASE='dcf9b162c42c30f387803fc9f395fcb1183f0e8179f5b46004782ba4bbf1f10d'
RUN=43359142508
HEAD='b15751dd62291814b2daef85909526178dcd5c30'
LIMIT=1024**2
require=v.require


def positive(x):return type(x) is int and x>0


def validate(catalog,q,allow_fixture=False):
    require(isinstance(catalog,dict) and set(catalog)=={'schema','test_fixture','repository',
        'source_revision','plan_sha256','base_lock_sha256','run','artifacts'},'Wrong catalog fields')
    require(catalog['schema']==SCHEMA and type(catalog['test_fixture']) is bool
        and catalog['test_fixture']==q['test_fixture'] and (not catalog['test_fixture'] or allow_fixture),
        'Catalog fixture boundary differs')
    require(catalog['repository']==v.r.REPO and all(catalog[k]==q[k] for k in
        ('source_revision','plan_sha256','base_lock_sha256')),'Catalog/request source identity differs')
    run=catalog['run'];rows=catalog['artifacts']
    require(isinstance(run,dict) and set(run)=={'id','head_sha','run_attempt','artifact_count'}
        and positive(run['id']) and isinstance(run['head_sha'],str) and v.core.REVISION.fullmatch(run['head_sha'])
        and positive(run['run_attempt']) and type(run['artifact_count']) is int
        and 1<=run['artifact_count']<=250,'Invalid catalog run')
    require(isinstance(rows,list) and len(rows)==run['artifact_count'],'Wrong catalog count')
    ids,names,keys=set(),set(),set()
    for row in rows:
        require(isinstance(row,dict) and set(row)=={'key','id','name','size_in_bytes','digest'},'Wrong catalog artifact fields')
        require(isinstance(row['key'],str) and re.fullmatch('R[PM][0-9]{4}',row['key'])
            and positive(row['id']) and positive(row['size_in_bytes'])
            and isinstance(row['name'],str) and re.fullmatch('[A-Za-z0-9_.-]{1,200}',row['name'])
            and isinstance(row['digest'],str) and re.fullmatch('sha256:[0-9a-f]{64}',row['digest']),
            'Invalid catalog artifact identity')
        require(row['id'] not in ids and row['name'] not in names and row['key'] not in keys,
            'Duplicate catalog id/name/key')
        ids.add(row['id']);names.add(row['name']);keys.add(row['key'])
    if not catalog['test_fixture']:
        want={s+str(i).zfill(4) for s in ('RP','RM') for i in range(32,3968,32)}
        require(catalog['source_revision']==SOURCE and catalog['plan_sha256']==PLAN
            and catalog['base_lock_sha256']==BASE and run=={'id':RUN,'head_sha':HEAD,'run_attempt':1,'artifact_count':246}
            and keys==want,'Not the exact remaining246 production origin')
        require(all(x['name']=='rotating-remaining-'+x['key']+'-'+str(RUN)+'-1' for x in rows),
            'Wrong production artifact names')
    require(q['scope']=='partial' and 1<=len(q['jobs'])<=32,'Only partial publication is supported')
    lookup={x['key']:x for x in rows}
    for job in q['jobs']:
        require(job['key'] in lookup,'Requested archive missing from catalog')
        row=lookup[job['key']]
        require(job['origin_run_id']==run['id'] and job['origin_head_sha']==run['head_sha']
            and job['origin_artifact_id']==row['id'] and job['origin_artifact_zip_bytes']==row['size_in_bytes']
            and 'sha256:'+job['origin_artifact_zip_sha256']==row['digest'],'Requested origin differs from catalog')
    return lookup


def request_count(catalog):
    return 2+catalog['run']['artifact_count']//100+1


def run_identity(row,wanted):
    require(isinstance(row,dict) and type(row.get('id')) is int and row['id']==wanted['id']
        and row.get('repository',{}).get('full_name')==v.r.REPO and row.get('head_sha')==wanted['head_sha']
        and type(row.get('run_attempt')) is int and row['run_attempt']==wanted['run_attempt']
        and row.get('status')=='completed' and row.get('conclusion')=='success',
        'Original whole run is not the exact completed success')
    return {k:row[k] for k in ('id','head_sha','run_attempt','status','conclusion')}


def observe(client,catalog,q):
    validate(catalog,q,client.fixture)
    run=catalog['run'];prefix=v.API+'/actions/runs/'+str(run['id'])
    first,first_sha=client.metadata(prefix);identity=run_identity(first,run)
    expected={x['id']:x for x in catalog['artifacts']};actual={};pages=[]
    count=run['artifact_count'];last_page=count//100+1
    for page in range(1,last_page+1):
        response,digest=client.metadata(prefix+'/artifacts?per_page=100&page='+str(page))
        require(isinstance(response,dict) and type(response.get('total_count')) is int
            and response['total_count']==count and isinstance(response.get('artifacts'),list),
            'Origin catalog pagination total differs')
        rows=response['artifacts'];wanted_count=min(100,count-100*(page-1))
        require(len(rows)==wanted_count,'Missing/overlong origin page')
        pages.append(digest)
        for row in rows:
            require(isinstance(row,dict) and type(row.get('id')) is int and row['id'] in expected
                and row['id'] not in actual,'Unknown/duplicate observed origin artifact')
            wanted=expected[row['id']]
            require(row.get('expired') is False and row.get('workflow_run',{}).get('id')==run['id']
                and row.get('workflow_run',{}).get('head_sha')==run['head_sha']
                and type(row.get('size_in_bytes')) is int
                and all(row.get(k)==wanted[k] for k in ('id','name','size_in_bytes','digest')),
                'Expired/changed observed origin artifact')
            actual[row['id']]={k:row[k] for k in ('id','name','size_in_bytes','digest')}
    require(set(actual)==set(expected),'Incomplete observed origin collection')
    last,last_sha=client.metadata(prefix);require(run_identity(last,run)==identity,'Run changed across pagination')
    observation={'run':identity,'artifacts':{str(i):actual[i] for i in sorted(actual)}}
    client.journal.event('bulk_origin_checked',{'catalog_sha256':v.p.sha(v.core.json_bytes(catalog)),
        'run_response_sha256':[first_sha,last_sha],'page_response_sha256':pages,
        'requests':request_count(catalog),'artifacts':len(actual),'test_fixture':client.fixture})
    return observation
