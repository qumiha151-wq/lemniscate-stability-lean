"""Reproduce the 32 small rational centres embedded in FloquetPencil.lean."""
from fractions import Fraction as Q
from pathlib import Path
import json,sys
from floquet import here,old,interval
scale=10**12

def source():
    lines=[]
    for tag in ("plus","minus"):
        data=json.loads((old/f"metric_{tag}_o60_n4000.json").read_bytes())
        rows=[]
        for row in data["endpoint_fundamental"][:4]:
            coeff=[]
            for v in row[:4]:
                lo,hi=interval(v)
                n=round(scale*(hi+lo)/2)
                assert max(abs(hi-Q(n,scale)),abs(lo-Q(n,scale)))<=Q(1,scale)
                coeff.append(f"({n}:ℚ)/10^12")
            rows.append("!["+",".join(coeff)+"]")
        lines.append(f"def {tag} : Four ℚ := !["+",\n  ".join(rows)+"]")
    return "\n\n".join(lines)

path=here/"FloquetPencil.lean"
if not path.exists():
    path=here.parents[1]/"SolitonClassification/Rotating/FloquetPencil.lean"
data=source()
if "--insert" in sys.argv:
    text=path.read_text(encoding="utf-8")
    assert "-- DATA" in text
    path.write_text(text.replace("-- DATA",data),encoding="utf-8")
else:
    assert data in path.read_text(encoding="utf-8")
    print("32 rational centres reproduced from the archived variational endpoints.")
