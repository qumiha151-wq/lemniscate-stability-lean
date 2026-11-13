"""Pure draft/published identity checks based on observed GitHub draft URLs.

Presentation URLs are validated but never used to authorize or perform downloads.
Binary verification must still use the separately pinned repository/asset ID.
"""
import re

REPOSITORY='qumiha151-wq/lemniscate-stability-lean'


def require(ok,message):
    if not ok:raise ValueError(message)


def validate_release(release,release_id,tag,revision,*,draft):
    require(type(release_id) is int and release_id>0 and type(draft) is bool,
            'Invalid expected release identity')
    require(isinstance(tag,str) and re.fullmatch('[A-Za-z0-9_.-]{1,160}',tag)
        and isinstance(revision,str) and re.fullmatch('[0-9a-f]{40}',revision),
        'Invalid expected tag/source revision')
    require(type(release.get('id')) is int and release['id']==release_id
        and release.get('tag_name')==tag and release.get('target_commitish')==revision
        and release.get('draft') is draft,'Release id/tag/source/draft differs')
    require(release.get('url')=='https://api.github.com/repos/'+REPOSITORY+'/releases/'+str(release_id),
            'Release API URL is not the expected repository/id')
    published=release.get('published_at')
    require(published is None if draft else isinstance(published,str) and bool(published),
            'Release publication timestamp disagrees with its phase')
    prefix='https://github.com/'+REPOSITORY+'/releases/tag/'
    url=release.get('html_url')
    require(isinstance(url,str) and url.startswith(prefix),'Foreign/malformed release presentation URL')
    slug=url[len(prefix):]
    if draft:
        require(slug==tag or re.fullmatch('untagged-[0-9a-f]{20}',slug),
                'Unexpected draft presentation slug')
    else:require(slug==tag,'Published release must use its exact final tag URL')
    return {'repository':REPOSITORY,'id':release_id,'tag_name':tag,'target_commitish':revision,
        'draft':draft,'published_at':published,'immutable':release.get('immutable'),
        'html_url':url,'presentation_slug':slug}


def validate_asset(asset,identity,asset_id,name,sha256,size):
    require(identity.get('repository')==REPOSITORY and type(identity.get('id')) is int
        and type(identity.get('draft')) is bool,'Invalid normalized release identity')
    require(type(asset_id) is int and asset_id>0 and type(size) is int and size>0
        and isinstance(name,str) and re.fullmatch('[A-Za-z0-9_.-]+',name)
        and isinstance(sha256,str) and re.fullmatch('[0-9a-f]{64}',sha256),'Invalid expected asset identity')
    require(type(asset.get('id')) is int and asset['id']==asset_id and asset.get('name')==name
        and asset.get('state')=='uploaded' and type(asset.get('size')) is int and asset['size']==size
        and asset.get('digest')=='sha256:'+sha256,'Asset id/name/state/size/digest differs')
    require(asset.get('url')=='https://api.github.com/repos/'+REPOSITORY+'/releases/assets/'+str(asset_id),
            'Asset API URL is not the expected repository/id')
    expected='https://github.com/'+REPOSITORY+'/releases/download/'+identity['presentation_slug']+'/'+name
    require(asset.get('browser_download_url')==expected,
            'Asset presentation URL does not match the bound release phase/slug/name')
    return {'id':asset_id,'name':name,'state':'uploaded','size':size,'digest':'sha256:'+sha256,
            'browser_download_url':expected}
