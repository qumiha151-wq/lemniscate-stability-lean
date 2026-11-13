"""Pure protocol checks against retained actual draft responses; no HTTP."""
from pathlib import Path
import argparse,copy,hashlib,json
import production_release_url_protocol as protocol


def main():
    parser=argparse.ArgumentParser()
    for name in ['journal','request','output']:parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args();sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
    read=lambda name:json.loads((args.journal/name).read_bytes())
    q=json.loads(args.request.read_bytes());release=read('00023_raw_response.json');asset=read('00024_raw_response.json')
    def check(r,a,draft=True):
        identity=protocol.validate_release(r,443789076,q['tag'],q['source_revision'],draft=draft)
        return protocol.validate_asset(a,identity,742149339,q['archive']['asset_name'],
            q['archive']['sha256'],q['archive']['bytes'])
    checked=check(release,asset);assert checked['browser_download_url']==asset['browser_download_url']
    draft_tag=copy.deepcopy(release);draft_asset=copy.deepcopy(asset)
    draft_tag['html_url']='https://github.com/'+protocol.REPOSITORY+'/releases/tag/'+q['tag']
    final_url='https://github.com/'+protocol.REPOSITORY+'/releases/download/'+q['tag']+'/'+asset['name']
    draft_asset['browser_download_url']=final_url;check(draft_tag,draft_asset)
    published=copy.deepcopy(draft_tag);published.update(draft=False,published_at='2026-11-13T00:00:00Z')
    check(published,draft_asset,False)  # Synthetic phase transition, not a published record.
    cases=[]
    def reject(name,r,a,draft=True):
        try:check(r,a,draft)
        except Exception as error:cases.append({'case':name,'rejected':True,'exception_type':type(error).__name__})
        else:raise AssertionError('Accepted '+name)
    for name,field,value in [
        ('release_other_repo','url','https://api.github.com/repos/other/repo/releases/443789076'),
        ('release_wrong_id','id',443789077),('release_bool_id','id',True),
        ('release_wrong_tag','tag_name','different'),('release_wrong_source','target_commitish','0'*40),
        ('release_http','html_url',release['html_url'].replace('https:','http:')),
        ('release_other_host','html_url',release['html_url'].replace('github.com','github.example')),
        ('release_query','html_url',release['html_url']+'?token=x'),
        ('release_fragment','html_url',release['html_url']+'#asset'),
        ('release_arbitrary_slug','html_url',release['html_url'].rsplit('/',1)[0]+'/different'),
        ('release_bad_hex_slug','html_url',release['html_url'].rsplit('/',1)[0]+'/untagged-'+('x'*20)),
        ('draft_has_timestamp','published_at','2026-11-13T00:00:00Z')]:
        bad=copy.deepcopy(release);bad[field]=value;reject(name,bad,asset)
    for name,field,value in [
        ('asset_wrong_id','id',742149340),('asset_bool_id','id',True),('asset_wrong_name','name','other.tar.xz'),
        ('asset_starter','state','starter'),('asset_wrong_size','size',1),('asset_bool_size','size',True),
        ('asset_wrong_hash','digest','sha256:'+'0'*64),
        ('asset_other_repo_api','url','https://api.github.com/repos/other/repo/releases/assets/742149339'),
        ('asset_other_slug','browser_download_url',asset['browser_download_url'].replace('390c5b0e380000cfceb8','0'*20)),
        ('asset_other_host','browser_download_url',asset['browser_download_url'].replace('github.com','github.example')),
        ('asset_query','browser_download_url',asset['browser_download_url']+'?download=1'),
        ('asset_encoded_name','browser_download_url',asset['browser_download_url'].replace('.tar.xz','%2Etar.xz'))]:
        bad=copy.deepcopy(asset);bad[field]=value;reject(name,release,bad)
    reject('published_untagged_html',dict(release,draft=False,published_at='2026-11-13T00:00:00Z'),asset,False)
    reject('published_untagged_asset',published,asset,False)
    reject('published_missing_timestamp',dict(published,published_at=None),draft_asset,False)
    result={'schema':'rotating.release-url-protocol-review.v1','status':'checked',
        'helper_sha256':sha(Path(protocol.__file__)),'test_sha256':sha(Path(__file__)),
        'actual_release_response_sha256':sha(args.journal/'00023_raw_response.json'),
        'actual_asset_response_sha256':sha(args.journal/'00024_raw_response.json'),
        'actual_draft_release_id':443789076,'actual_draft_asset_id':742149339,
        'actual_recorded_draft_accepted':True,'canonical_draft_and_published_cases_are_synthetic':True,
        'rejections':cases,'new_network_requests':0,'new_github_writes':0,'release_published':False}
    assert not args.output.exists();args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'checked','actual_draft_accepted':True,'rejections':len(cases),'new_github_writes':0}))


if __name__=='__main__':main()
