"""Postcheck completed N1..32 traces; correct Windows fixture and finish narrow tests."""
from pathlib import Path
from types import SimpleNamespace
import argparse,copy,json,os,shutil,stat,struct,subprocess,sys,warnings,zipfile
import review_shard_zip_download as old
d,t,s,o,w,p,c,core=old.d,old.t,old.s,old.o,old.w,old.p,old.c,old.core


def main():
    ap=argparse.ArgumentParser()
    for name in ('prior','plan','actual-zip','prior-actual','output'):ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();out=core.fresh_path(a.output);out.mkdir(parents=True)
    helper=d.helpers();test_sha=c.digest(__file__);post=[];cases=[]
    assert c.digest(a.prior/'test_source.py')==c.digest(old.__file__)
    for n in range(1,33):
        root=a.prior/('count_'+str(n));receipt=core.strict_json((root/'receipt.json').read_bytes())
        assert receipt['status']=='fixture_only' and receipt['helper_sha256']==helper and receipt['remote_writes']==0
        expected={root/k for k in receipt['checked_files']}
        assert {x for x in root.rglob('*') if x.is_file()}==expected|{root/'receipt.json'}
        for path in expected:
            wanted=receipt['checked_files'][path.relative_to(root).as_posix()]
            assert c.digest(path)==wanted['sha256'] and path.stat().st_size==wanted['bytes']
        events=[core.strict_json(x.read_bytes()) for x in (root/'journal').glob('*.json') if not x.name.endswith('_raw_response.json')]
        journal=SimpleNamespace(root=root/'journal',number=len(events),previous=receipt['journal_tail'])
        d.journal_files(journal)
        observations=[x['data'] for x in events if x['event']=='quota_observation']
        assert len(observations)==n+10 and all(x['method']=='GET' and x['test_fixture'] is True for x in observations)
        assert sum(x['endpoint_path'].endswith('/zip') for x in observations)==n
        gates=[x['data']['decision'] for x in events if x['event']=='zip_quota_gate']
        assert len(gates)==1 and gates[0]['allowed'] and gates[0]['required_remaining']==n+110
        assert sum(x['event']=='original_zip_checked' for x in events)==n
        post.append({'N':n,'actual_recorded_memory_API_GETs':len(observations),
            'receipt_sha256':c.digest(root/'receipt.json'),'all_checked_files_rehashed':True,'journal_chain_checked':True})
    template=core.strict_json((a.prior/'count_1_inputs/request.json').read_bytes())['original_request'];job0=template['jobs'][0]
    def reject(name,fn,kind,message=None):
        try:fn()
        except kind as error:
            if message is not None:assert str(error)==message
            cases.append({'case':name,'rejected':True,'exception_type':type(error).__name__,'message':str(error)})
        else:raise AssertionError('Accepted '+name)
    patterns=[('traversal','../escape',None),('absolute','/escape',None),('backslash','x/y',None),
        ('colon','x:y',None),('symlink','link',stat.S_IFLNK|0o777),('parent_file','job',stat.S_IFREG|0o644),
        ('directory_metadata','bad_dir',stat.S_IFDIR|0o755)]
    for label,name,mode in patterns:
        path=out/(label+'.zip');job=copy.deepcopy(job0);old.make_zip(path,template,job,[(name,b'bad',mode)])
        if label=='backslash':
            raw=path.read_bytes();assert raw.count(b'x/y')==2
            path.write_bytes(raw.replace(b'x/y',b'x'+bytes([92])+b'y'))
            with zipfile.ZipFile(path) as z:assert any('\\' in i.orig_filename for i in z.infolist())
        job.update(origin_artifact_zip_bytes=path.stat().st_size,origin_artifact_zip_sha256=c.digest(path))
        wanted={'traversal':'Unsafe/noncanonical ZIP member','absolute':'Unsafe/noncanonical ZIP member',
            'backslash':'Unsafe/noncanonical ZIP member','colon':'Unsafe/noncanonical ZIP member',
            'symlink':'Special/encrypted ZIP member','parent_file':'Ambiguous ZIP parent file/directory',
            'directory_metadata':'Contradictory ZIP file/directory metadata'}[label]
        reject(label,lambda:d.extract_archive(path,out/(label+'.tar.xz'),template,job),ValueError,wanted)
    for label,extras in [('case_collision',[('A',b'a',None),('a',b'b',None)]),('duplicate',[('same',b'a',None),('same',b'b',None)])]:
        path=out/(label+'.zip');job=copy.deepcopy(job0)
        with warnings.catch_warnings():warnings.simplefilter('ignore');old.make_zip(path,template,job,extras)
        job.update(origin_artifact_zip_bytes=path.stat().st_size,origin_artifact_zip_sha256=c.digest(path))
        reject(label,lambda:d.extract_archive(path,out/(label+'.tar.xz'),template,job),ValueError,'Duplicate/casefold ZIP member')
    for label in ('wrong_member','wrong_archive_hash','bad_crc','expanded_cap','encrypted','too_many'):
        path=out/(label+'.zip');job=copy.deepcopy(job0)
        if label=='wrong_member':
            with zipfile.ZipFile(path,'w') as z:z.writestr('different',b'wrong')
        else:old.make_zip(path,template,job)
        if label in ('bad_crc','expanded_cap','encrypted'):
            raw=bytearray(path.read_bytes());central=raw.index(b'PK\x01\x02')
            if label=='bad_crc':
                offset=30+struct.unpack_from('<H',raw,26)[0]+struct.unpack_from('<H',raw,28)[0];raw[offset]^=1
            elif label=='expanded_cap':struct.pack_into('<I',raw,central+24,d.ZIP_EXPANDED_CAP+1)
            else:struct.pack_into('<H',raw,central+8,struct.unpack_from('<H',raw,central+8)[0]|1)
            path.write_bytes(raw)
        if label=='too_many':
            with zipfile.ZipFile(path,'a') as z:
                for i in range(5000):z.writestr('extra/'+str(i),b'')
        job.update(origin_artifact_zip_bytes=path.stat().st_size,origin_artifact_zip_sha256=c.digest(path))
        if label=='wrong_archive_hash':job['archive_sha256']='0'*64
        kind=KeyError if label=='wrong_member' else (zipfile.BadZipFile if label=='bad_crc' else ValueError)
        reject(label,lambda:d.extract_archive(path,out/(label+'.tar.xz'),template,job),kind)
    # Actual retained ZIP and archive, through file-backed fake HTTP.
    aq=copy.deepcopy(core.strict_json((a.prior_actual/'actual_preflight_request.json').read_bytes())['original_request'])
    aq['jobs']=aq['jobs'][:1];aj=aq['jobs'][0]
    assert a.actual_zip.stat().st_size==aj['origin_artifact_zip_bytes'] and c.digest(a.actual_zip)==aj['origin_artifact_zip_sha256']
    cat=t.make_catalog(aq,[{'key':aj['key'],'id':aj['origin_artifact_id'],'name':'actual-first4-'+aj['key'],
        'size_in_bytes':aj['origin_artifact_zip_bytes'],'digest':'sha256:'+aj['origin_artifact_zip_sha256']}])
    fake=t.write_context(out/'actual_inputs',aq,cat,a.plan)
    ctx=d.prepare(fake['request_path'],fake['request_sha256'],a.plan,c.digest(a.plan),fake['catalog_path'],
        fake['catalog_sha256'],out/'actual_original',True)
    journal=w.Journal(ctx['output']/'journal');client=d.ReadOnlyHTTP(ctx,journal,token='fixture-token',fixture=True,api='http://127.0.0.1:1')
    wire=old.Wire(ctx,{aj['key']:a.actual_zip});client.opener=s.budget._ObservedOpener(wire,client)
    actual=d._download(ctx,client,journal);assert c.digest(ctx['output']/'archives'/aj['archive'])==aj['archive_sha256']
    assert len(wire.calls)==7 and wire.zip_calls==1 and client.writes==0
    # Real, isolated LOCAL Git commit for the new outer source and all helpers.
    gitroot=out/'local_git_fixture';tools=gitroot/'tools';tools.mkdir(parents=True)
    for name,digest in helper.items():
        source=Path(p.planner.reference.__file__) if name=='reference.py' else Path(d.__file__).parent/name
        assert c.digest(source)==digest;shutil.copyfile(source,tools/name)
    hooks=gitroot/'empty_hooks';hooks.mkdir();env=os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):env.pop(key)
    env.update(GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL=os.devnull)
    def git(*args):return subprocess.run(['git',*args],cwd=gitroot,env=env,check=True,stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,timeout=30).stdout.decode().strip()
    git('init','-q');git('add','--','tools');git('-c','core.hooksPath='+str(hooks.resolve()),'-c','commit.gpgsign=false',
        '-c','user.name=Local fixture','-c','user.email=fixture@example.invalid','commit','-q','-m','Local-only outer identity fixture')
    revision=git('rev-parse','HEAD')
    def check():return subprocess.run([sys.executable,'-B','-c','import production_shard_zip_download as d; print(d.checked_tool_revision())'],
        cwd=tools,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
    result=check();assert result.returncode==0 and result.stdout.decode().strip()==revision
    path=tools/Path(d.__file__).name;raw=path.read_bytes();path.write_bytes(raw+b'\n# LOCAL OUTER TAMPER FIXTURE\n')
    try:
        result=check();assert result.returncode!=0 and b'Outer source is not its actual committed tool blob' in result.stderr
    finally:path.write_bytes(raw)
    assert check().stdout.decode().strip()==revision
    assert helper==d.helpers() and c.digest(__file__)==test_sha
    report={'schema':'rotating.outer-zip-completion-review.v1','status':'checked','runtime_helper_sha256':helper,
        'test_sha256':test_sha,'original_test_sha256':c.digest(old.__file__),
        'original_primary_test_exit':1,'original_failure':'Windows ZipInfo normalized the intended malicious backslash name before writing',
        'full_N1_to_N32_repeated':False,'actual_completed_count_trace_postchecks':post,'layout_rejections':cases,
        'actual_original_ZIP':{'source':str(a.actual_zip),'sha256':c.digest(a.actual_zip),'bytes':a.actual_zip.stat().st_size,
            'archive_sha256':aj['archive_sha256'],'archive_bytes':aj['archive_bytes'],'receipt_sha256':c.digest(ctx['output']/'receipt.json')},
        'CRC_scope':'Only the selected extracted archive member is read and CRC checked. All ZIP bytes are SHA checked; other members have directory-metadata checks only.',
        'actual_local_Git_outer_commit':revision,'actual_dirty_outer_child_exit':result.returncode,
        'actual_network_requests':0,'actual_GitHub_writes':0,'new_Lean_calls':0,'production_catalog_generated':False,
        'actual_GitHub_checkout_claimed':False,'full_certificate_proved':False}
    core.write_new(out/'report.json',core.json_bytes(report));print(json.dumps({'status':'checked','prior_count_trace_postchecks':len(post),
        'layout_rejections':len(cases),'report_sha256':c.digest(out/'report.json')}))


if __name__=='__main__':main()
