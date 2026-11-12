"""Copy only state-independent rational/fixed-ball lemmas into this project.

The original CentroidEscape files remain unchanged. New source imports only
Mathlib or SolitonClassification.Rotating; no cross-problem Lean dependency.
"""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
source=HERE.parent/'centroid_formal'
target=HERE/'SolitonClassification'/'Rotating';target.mkdir(parents=True,exist_ok=True)
manifest=[]
for name in ['RationalBall.lean','FixedBall.lean']:
    raw=(source/name).read_bytes();text=raw.decode('utf-8-sig').replace('\r\n','\n').replace('\r','\n')
    text=text.replace('CentroidEscape','SolitonClassification.Rotating')
    (target/name).write_text(text,encoding='utf-8')
    manifest.append(dict(module=name,original_source=str(source/name),
        original_sha256=hashlib.sha256(raw).hexdigest(),
        change='namespace/import rename and line-ending normalization; independently recompiled under SolitonClassification.Rotating'))
(HERE/'generic_source_provenance.json').write_text(json.dumps(manifest,indent=2)+'\n')
