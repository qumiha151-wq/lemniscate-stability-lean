"""Prove a signed force cover for the published periodic rotating immersion."""
import argparse
import gzip
import hashlib
import json
from fractions import Fraction
from pathlib import Path

DIGIT=10**9
ENC=2**240
PLUS="792eb4d79ae72c3a406ec8d89c4289458c37c3c681ad0c1976da73b76a81667e"
PI_LO=3141592653
PI_HI=3141592654

def interval(n):
    # The validated cube-to-node comparison is below one nanounit.
    return (n*DIGIT//ENC-1,-(-n*DIGIT//ENC)+1)

def add(x,y):return (x[0]+y[0],x[1]+y[1])
def neg(x):return (-x[1],-x[0])
def mul(x,y):
    v=[a*b for a in x for b in y]
    return (min(v)//DIGIT,-(-max(v)//DIGIT))
def absolute(x):return max(-x[0],x[1])
def shift_pi(m):return (min(m*PI_LO,m*PI_HI),max(m*PI_LO,m*PI_HI))

def load(folder):
    data={}
    digests=[]
    for direction,name in ((1,"plus4000"),(-1,"minus4000")):
        text=gzip.decompress((folder/(name+".jsonl.gz")).read_bytes()).replace(b'\r\n',b'\n')
        digests.append(hashlib.sha256(text).hexdigest())
        lines=text.splitlines()
        header=json.loads(lines[0])
        assert int(header["D"])==ENC
        assert 0 < direction*Fraction(header["h"]) < Fraction(1,125)
        assert len(lines)==4002
        for j,raw in enumerate(lines[1:4001]):
            row=json.loads(raw)
            if j:row=row[2]
            state=tuple(map(interval,row[:6]))
            if j==0 and 0 in data:assert data[0]==state
            data[j*direction]=state
    assert digests==[PLUS,"ec1395ecb0db16e75cd641dd3f4c164b59660d799a804dc95bf1e2291194b3ed"]
    return data,digests

def prove_pi_window():
    def bracket(n):
        # Alternating arctan series at x=1/n, with 16 even-numbered terms.
        s=sum(((-1)**j*Fraction(1,(2*j+1)*n**(2*j+1)) for j in range(16)),Fraction())
        return s,s+Fraction(1,33*n**33)
    l,u=bracket(5)
    v,w=bracket(239)
    # Machin's identity pi=16 arctan(1/5)-4 arctan(1/239).
    assert Fraction(PI_LO,DIGIT)<16*l-4*w<=16*u-4*v<Fraction(PI_HI,DIGIT)

def certificate(folder):
    prove_pi_window()
    states,hashes=load(folder)
    accepted=[]
    for j in range(-3999,3999):
        k,u,p,q,b,theta=states[j]
        K,U,P,Q,B,Theta=states[j+1]
        assert b==B and absolute(b) < 11*DIGIT//100
        force=neg(add(p,mul(b,q)))
        end=neg(add(P,mul(b,Q)))
        # Along the whole cell |k'|<=80, |p'|<=100, |q'|<=101;
        # bound |F'|=|k(q-bp)-b| with the nearer endpoint.
        kmax=max(absolute(k),absolute(K))+80*DIGIT//250
        pmax=max(absolute(p),absolute(P))+100*DIGIT//250
        qmax=max(absolute(q),absolute(Q))+101*DIGIT//250
        lip=mul((kmax,kmax),(qmax+mul((absolute(b),)*2,(pmax,pmax))[1],)*2)[1]+absolute(b)
        err=-(-lip//250)
        fmin=min(force[0],end[0])-err
        fmax=max(force[1],end[1])+err
        if fmin>0:sign=1;margin=fmin
        elif fmax<0:sign=-1;margin=-fmax
        else:continue
        lo=min(theta[1],Theta[1]); hi=max(theta[0],Theta[0])
        if hi<=lo:continue
        for winding in range(-6,7):
            shift=shift_pi(2*winding+(0 if sign>0 else 1))
            left=lo+shift[1];right=hi+shift[0]
            if left<2*PI_HI and right>0:
                accepted.append((left,right,margin,j,sign,winding))
    def greedy(level):
        stop=0; selected=[]
        while stop<2*PI_HI:
            options=[v for v in accepted if v[0]<=stop<v[1] and v[2]>=level]
            if not options:return []
            pick=max(options,key=lambda x:x[1])
            stop=pick[1];selected.append(pick)
        return selected
    low,high=0,10*DIGIT
    while high-low>1:
        mid=(low+high)//2
        if greedy(mid):low=mid
        else:high=mid
    chain=greedy(low)
    assert chain and low>=642_000_000
    assert (642_000_000)**2*10_000 >= (638_000_000)**2*(10_000+121)
    return dict(grid_sha256=hashes,units=1_000_000_000,force_floor=low,rows=chain)

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("tapes",type=Path)
    p.add_argument("--out",type=Path)
    args=p.parse_args()
    result=certificate(args.tapes)
    if args.out:args.out.write_text(json.dumps(result,indent=2)+"\n","utf8")
    print("force floor",result["force_floor"],"cells",len(result["rows"]),result["grid_sha256"])
