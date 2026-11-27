"""Exact rational contraction and centre correction from the dyadic endpoints."""
from fractions import Fraction as Q
from pathlib import Path
import json
from reset_tape import HERE,D,ROWS


def atan(x,n):
    value=sum((-1)**k*x**(2*k+1)/(2*k+1) for k in range(n))
    error=(-1)**n*x**(2*n+1)/(2*n+1)
    return min(value,value+error),max(value,value+error)


def solve():
    raw=json.loads((HERE/'exact_nodes.json').read_bytes())
    source=HERE.parent/'center.json'
    if not source.is_file():source=HERE.parent/'primitive_rotating_winding/center.json'
    phase=list(map(Q,json.loads(source.read_bytes())['phase']))
    plus,minus=([Q(a,D) for a in row['endpoint']] for row in raw)
    X,Y=plus[:6],minus[:6]
    def f(z):
        k,u,p,q,b,_=z
        return [8*u,-k**3/16-p/8-b*q/8,-k*q,1+k*p,0,k]
    fp,fm=f(X),f(Y)
    A=[]
    for i,k,w in zip(range(5),ROWS,[1,8,1,1,1]):
        jump=[plus[6+5*j+i]-minus[6+5*j+i] for j in range(5)]
        A.append([w*a for a in [jump[0],jump[2],fp[k]+fm[k],
                                jump[1]*phase[0]/8+jump[3]*phase[1],jump[4]]])
    aug=[row+[Q(i==j) for j in range(5)] for i,row in enumerate(A)]
    for j in range(5):
        k=next(i for i in range(j,5) if aug[i][j])
        aug[j],aug[k]=aug[k],aug[j]
        lead=aug[j][j]
        aug[j]=[a/lead for a in aug[j]]
        for i in range(5):
            if i!=j:
                a=aug[i][j]
                aug[i]=[b-a*c for b,c in zip(aug[i],aug[j])]
    B=[row[5:] for row in aug]
    assert all(sum(B[i][k]*A[k][j] for k in range(5))==int(i==j)
               for i in range(5) for j in range(5))
    bn=max(sum(map(abs,row)) for row in B)
    l,u=atan(Q(1,5),92);v,w=atan(Q(1,239),31)
    pl,pu=16*l-4*w,16*u-4*v
    assert pu-pl<Q(1,10**129)
    vals=[w*(X[k]-Y[k]) for k,w in zip(ROWS,[1,8,1,1,1])]
    vals[-1]+=pl+pu
    error=Q(32,10**59)+(pu-pl)
    eta=max(abs(sum(b*a for b,a in zip(row,vals)))+sum(map(abs,row))*error for row in B)
    r=Q(1,10**30)
    lip=bn*Q(2,10**12)
    assert bn<13 and lip<Q(3,10**11) and eta+lip*r<r
    print('B',float(bn),'eta',float(eta),'lip',float(lip),'correction',float(eta/(1-lip)),flush=True)
    return dict(inverse_norm_le_13=True,lip_upper='3/10^11',eta_upper_scaled_1e64=(eta*10**64).__ceil__(),
                correction_upper_scaled_1e64=(eta/(1-lip)*10**64).__ceil__(),
                exact_preconditioner=[[str(a) for a in row] for row in B])
if __name__=='__main__':
    (HERE/'contraction.json').write_text(json.dumps(solve(),indent=2)+'\n',encoding='ascii')
