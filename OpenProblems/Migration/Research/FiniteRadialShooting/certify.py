"""Outward-rounded interval shooting for a radial-minimum section, without reflection assumptions."""
import json
from itertools import product
from pathlib import Path

here=Path(__file__).resolve().parent
from flint import arb, ctx

ctx.prec=112
h=arb(1)/32


def segment(pair,den):
    lo,hi=pair
    return arb(lo+hi,hi-lo)/(2*den)


def field(z,b):
    x,y,t,k,v=z
    S,C=t.sin(),t.cos()
    F=x*C+y*S+b*(x*S-y*C)
    return [-S,C,k,v,F-k**3/2]


def second(z,b):
    x,y,t,k,v=z
    S,C=t.sin(),t.cos()
    p=-x*C-y*S
    q=-x*S+y*C
    acc=-p-b*q-k**3/2
    return [-k*C,-k*S,v,acc,k*q-b*(1+k*p)-3*k*k*v/2]


def step(z,b):
    rhs=field(z,b)
    widths=[2*h*abs(f).upper()+h/8 for f in rhs]
    for _ in range(14):
        tube=[u+arb(0,r.upper()) for u,r in zip(z,widths)]
        needed=[h*abs(f).upper() for f in field(tube,b)]
        if all(a<b for a,b in zip(needed,widths)):
            return [u+h*f+h*h*g/2 for u,f,g in zip(z,rhs,second(tube,b))]
        widths=[max(a,2*t+h/8) for a,t in zip(widths,needed)]
    raise ArithmeticError()


def hit(d,k,v,b):
    z=[d,arb(0),arb(0),k,v]
    try:
        for i in range(1,65):
            z=step(z,b)
            if z[0]<-arb(1)/1024 and z[1]>arb(1)/32:
                return i
    except ArithmeticError:
        pass
    return 0


def main():
    # All parameters have denominator 16. A box interior is counted once.
    intervals=[[(a,a+1) for a in range(1,5)],
               [(a,a+4) for a in range(8,32,4)],
               [(a,a+8) for a in range(-16,16,8)],
               [(a,a+16) for a in range(-32,32,16)]]
    records=[]
    for box in product(*intervals):
        d,k,v,b=[segment(a,16) for a in box]
        t=hit(d,k,v,b)
        if t:
            n=hit(d,k,-v,-b)
            if n:
                records.append([*box,t,n])
    report=dict(precision_bits=ctx.prec,grid_denominator=16,step_denominator=32,
                certified_boxes=records,attempted=4*6*4*4,
                x_upper="-1/1024",positive_y_lower="1/32")
    (here/"certified.json").write_text(json.dumps(report,separators=(",",":"))+"\n")
    print("certified",len(records),"of",report["attempted"])
    for cell in range(1,5):
        print("d cell",cell,"count",sum(r[0][0]==cell for r in records))
    print("sample",records[:2])


if __name__=="__main__":
    main()
