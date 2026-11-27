"""Read both completed dyadic tapes. Verify inverse witnesses and polygon index."""
import gzip
import json
import sys
from pathlib import Path
from fractions import Fraction as Q
from math import isqrt
from reset_tape import HERE,ROWS,D,seed
sys.path.insert(0,str(HERE.parents[1]/'pydeps'))
from flint import fmpz_mat

B=10**12

def op(X):
    return max(sum(abs(X[i][j]) for j in range(6)) for i in range(6))


def check(sign):
    length=4000
    half=abs(seed(sign)[1])*length
    initial=None
    end=None
    maxK=maxI=defect=xsum=msum=0
    minR=minQ=10**99
    angle=0
    prior=None
    gapBy={}
    gapNodes={}
    for p in range(2,301):
        if any(p%v==0 for v in range(2,isqrt(p)+1)):
            continue
        gapNodes.setdefault((4*length+p)//(2*p),[]).append(p)
    with gzip.open(HERE/f"{'plus' if sign>0 else 'minus'}4000.jsonl.gz",'rt',encoding='utf8') as out:
        header=json.loads(next(out))
        assert int(header['D'])==D
        for step,line in enumerate(out):
            item=json.loads(line)
            if step==0:
                node=item
                initial=item
                assert node == seed(sign)[0]
            else:
                sx,sm,node=item
                assert sx>=0 and sm>=0
                xsum+=sx;msum+=sm
            for z,lim in zip(node,[Q('8.4'),Q('4.35'),Q('7.25'),Q('7.25'),Q('.15')]):
                assert abs(z)<lim*D
            matrix=[[0]*6 for i in range(6)]
            for i,row in enumerate(ROWS):
                for j in range(5):
                    matrix[row][j]=node[6+5*j+i]
            matrix[4][4]=matrix[5][5]=D
            Z=fmpz_mat(matrix)
            inv=Z.inv()
            W=[[int(inv[i,j]*(D*B)) for j in range(6)] for i in range(6)]
            V=Z*fmpz_mat(W)
            E=[[int(V[i,j])-int(i==j)*D*B for j in range(6)] for i in range(6)]
            ne=op(E);nw=op(W);nz=op(matrix)
            assert nz<15000*D and ne<D*B and nw*D<15000*(D*B-ne)
            maxK=max(maxK,(nz+D-1)//D)
            maxI=max(maxI,(nw*D+D*B-ne-1)//(D*B-ne))
            defect=max(defect,ne)
            p,q=node[2:4]
            minR=min(minR,isqrt(p*p+q*q))
            minQ=min(minQ,abs(q))
            if prior is not None:
                a,b=prior
                assert a*p+b*q>0
                cross=a*q-b*p
                if b<0<q and cross>0: angle+=1
                if q<0<b and cross<0: angle-=1
            prior=p,q
            if sign==1:
                for d in gapNodes.get(step,[]):
                    dt=abs(2*half/d-step*half/length)+Q(3,10**30)
                    low=max(Q(abs(node[i]-initial[i]),D)-2*Q(1,10**18)-dt*v
                            for i,v in enumerate((40,47,81,82)))
                    assert low>Q(1,1000)
                    gapBy[d]=step
            end=node
        assert step==length
    den=16*seed(sign)[1].denominator*D**3
    assert xsum*10**58<den and msum*10**58<den
    assert minR>Q('0.16')*D and minQ>Q('1e-12')*D
    if sign>0: assert sum(map(len,gapNodes.values()))==len(gapBy)
    print(sign,'matrix',maxK,maxI,'sum defects',float(Q(xsum,den)),float(Q(msum,den)),
          'q margin',float(Q(minQ,D)),'radius',float(Q(minR,D)),'half index',angle,flush=True)
    return dict(sign=sign,matrix_norm_upper=maxK,inverse_norm_upper=maxI,
                inverse_relative_defect=str(Q(defect,D*B)),sum_state_defect=str(Q(xsum,den)),
                sum_matrix_defect=str(Q(msum,den)),radius_lower=str(Q(minR,D)),
                min_abs_q=str(Q(minQ,D)),primes=gapBy,half_crossing_count=angle,
                endpoint=end)


if __name__=='__main__':
    data=[check(1),check(-1)]
    plus,minus=data
    a,b=plus['endpoint'][2:4];p,q=minus['endpoint'][2:4]
    assert b*q>0 and a*p+b*q>0
    assert plus['half_crossing_count']==minus['half_crossing_count']
    (HERE/'exact_nodes.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf8')
