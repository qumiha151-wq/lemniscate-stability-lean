"""Replay the twelve certified reflected elastic expanders from dyadic centres."""
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
import argparse
import json
import sys
from certify import arb, ctx, enclosure


def exact(pair):
    mantissa, exponent = pair
    return Fraction(int(mantissa)) * Fraction(2) ** exponent


def replay(rec):
    ctx.prec=rec["precision_bits"]
    b,t=[arb(int(n))*arb(2)**e for n,e in rec["center_dyadic"]]
    computed=enclosure(b,t,arb(rec["radius_input"]),rec["steps"],rec["order"])
    computed["radius_input"]=rec["radius_input"]
    assert computed==rec
    return str(exact(rec["center_dyadic"][0]))


if __name__=="__main__":
    if not __debug__:
        raise SystemExit("Run Python without -O so the interval inequalities are checked.")
    ap=argparse.ArgumentParser()
    ap.add_argument("--jobs",type=int,default=1)
    args=ap.parse_args()
    collection=json.loads(Path(__file__).with_name("certificates.json").read_bytes())
    assert len(collection["cases"])==12
    intervals=[]
    for case in collection["cases"]:
        b,t=map(exact,case["center_dyadic"])
        r=Fraction(case["radius_input"])
        assert b-r>0 and t-r>0 and ((b+r)**2<Fraction(6,5) or (b-r)**2>Fraction(6,5))
        intervals.append((b-r,b+r))
    intervals.sort()
    assert all(i[1]<j[0] for i,j in zip(intervals,intervals[1:]))
    if args.jobs==1:
        list(map(replay,collection["cases"]))
    else:
        with ProcessPoolExecutor(max_workers=args.jobs) as pool:
            list(pool.map(replay,collection["cases"]))
    print("12 exact shooting boxes, all mutual separations, and the Bernoulli separation passed.")
