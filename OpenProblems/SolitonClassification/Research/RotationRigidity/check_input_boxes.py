"""Check exported Arb decimal balls against the exact input constants in Lean."""
from pathlib import Path
from fractions import Fraction
import json
import re
import sys

root=Path(__file__).resolve().parent
source=root/"QuarterRankIntervals.lean"
if not source.is_file():
    source=root.parents[1]/"SolitonClassification"/"QuarterRankIntervals.lean"
if len(sys.argv)>1:
    source=Path(sys.argv[1])
section=source.read_text(encoding="utf8").split("def units :",1)[1].split("def enclosure ",1)[0]
rows=[list(map(int,x.split(","))) for x in re.findall(r"!\[([-\d,]+)\]",section)]
records=sorted((json.loads(p.read_bytes()) for p in root.glob("*_odd_rank.json")),key=lambda r:r["base_case"])
if len(records)!=12 or len(rows)!=12:
    raise ValueError("Expected twelve ordered roots and rational tables")
for i,(u,r) in enumerate(zip(rows,records)):
    entries=[s for line in r["fundamental_matrix"] for s in line]+[line[3] for line in r["projected_matrix"]]
    if r["base_case"]!=i or len(u)!=18 or len(entries)!=18:
        raise ValueError("Invalid case or input dimension")
    for s,j in zip(entries,u):
        c,e=map(Fraction,s.strip("[]").split(" +/- "))
        if abs(c-Fraction(j,10**6))+e>Fraction(1,10**6):
            raise ValueError((i,s,j))
print("All 216 exported variational intervals lie in the exact rational boxes used by Lean.")
