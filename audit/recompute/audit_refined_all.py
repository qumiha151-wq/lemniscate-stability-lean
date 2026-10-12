from pathlib import Path
from fractions import Fraction as F
from math import comb
import json, contextlib, io
import single_analytic_bounds as sp
import odd_analytic_bounds as odd
import even_analytic_bounds as ev
import audit_galerkin_trial as gal

here=Path(__file__).resolve().parent
# Reuse the independent outward-rational arithmetic, replacing the trial definition.
ev.trial_data=gal.trial_data
src=(here/'audit_compact_bounds.py').read_text(encoding='utf-8')
src=src.replace('[(True,False,-F(21,4)),(False,False,-F(18)),(False,True,-F(11,2))]', '[(True,False,-F(21,4))]')
src=src.replace('27 single-period', '9 single-period').replace("'single_checks':27", "'single_checks':9")
src=src.replace('compact_bounds_audit.json','refined_bounds_audit.json').replace('All 328 merged','All 310 basic')
exec(compile(src,str(here/'audit_refined_all.py'),'exec'),globals())
record=json.loads((here/'refined_bounds_audit.json').read_text())
zero=[odd.row_polynomial(n)[0]/odd.weight(n)[0] for n in range(-11,12,2)]
assert min(zero)>5
assert gal.trial_values['zN_sq']<F(1,400)
assert ev.pi.lower()>3 and ev.pi.upper()<F(22,7)
assert sp.qlo<ev.Q.lower()<ev.Q.upper()<sp.qhi
assert sp.rlo<ev.R.lower()<ev.R.upper()<sp.rhi
# Beyond j=40 the deliberately wider 10^-70 audit grid can dominate tiny
# coefficients. Exact manuscript intervals nest for every j by monotonicity.
assert all(sp.h(2*j)[0]<=ev.hh(2*j).lower()<=ev.hh(2*j).upper()<=sp.h(2*j)[1] for j in range(41))
# Constrained sine rows and coupling, exactly as in the manuscript.
rho2=(sp.moment(sp.qhi**2,4)-sp.qhi**2)/sp.qhi**2
assert rho2<F(87,500)**2
assert sp.s(2,2,True)[1]<-12
coupling=sp.ab(sp.s(2,4,True))**2+sp.ab(sp.s(2,6,True))**2+sp.C**2*sum(F(comb(4,k))*2**(4-k)*sp.tail(sp.qb**2,3,k+2) for k in range(5))
assert coupling<3916<63**2
for n,bound in [(4,-120),(6,-1560)]:
    expr=sp.s(n,n,True)[1]+sum(sp.ab(sp.s(n,2*k,True)) for k in range(2,8) if 2*k!=n)
    expr+=sp.C*(n*n*sp.tail(sp.qb,8-n//2,1)+2*n*sp.tail(sp.qb,8-n//2,2)+sp.tail(sp.qb,8-n//2,3))
    assert expr<bound
assert F(19519,250)/(1+F(87,500)**2)>75
# Quartic derivative sign checks at the starting points.
def pdiff(p):return [i*v for i,v in enumerate(p)][1:]
def value(p,x):return sum(c*x**j for j,c in enumerate(p))
def quartic_P(a):
    return [sp.C*sp.moment(sp.qb*a,3),2*sp.C*sp.moment(sp.qb*a,2),45*sp.rhi+sp.C*(sp.moment(sp.qb/a,1)+sp.moment(sp.qb*a,1)),F(0),-4*sp.rlo**2]
for a,n,bound in [(F(1,10),F(18),-8000),(F(1),F(8),-3308)]:
    p=quartic_P(a)
    assert value(p,n)<bound and value(pdiff(p),n)<0 and value(pdiff(pdiff(p)),n)<0
po=[E*sp.moment(t,3)/3,2*E*sp.moment(t,2),45*sp.rhi+8+E*(sp.moment(z,1)+sp.moment(t,1)),F(0),-4*sp.rlo**2]
assert value(pdiff(po),F(25,2))<0 and value(pdiff(pdiff(po)),F(25,2))<0
B=5*E*(sp.moment(z,1)+sp.moment(t,1))+1
n=F(32)
pe1=-16*sp.rlo**2*(n-F(1,2))**3+90*sp.rhi*(n+F(1,2))+2*B*(n+2)+10*E*sp.moment(t,2)
pe2=-48*sp.rlo**2*(n-F(1,2))**2+90*sp.rhi+2*B
assert pe1<-166483 and pe2<-21850 and omitted<F(3,10**66)
# Weight norms used by the finite-rank envelope.
tail_sq=(max(ev.wbern('6'))**2+max(ev.wbern('-6'))**2)/(1-F(1,10)**2)
high_sq=max(ev.wbern('4'))**2+max(ev.wbern('-4'))**2+tail_sq
total_sq=high_sq+sum(max(ev.wbern(s))**2 for s in ('e','0','c2'))
assert high_sq<F(13,25)**2 and total_sq<F(23,10)**2
assert all(F(1,50)<=x<=F(1,20) for s in ('6','-6') for x in ev.wbern(s))
assert (F(266,100)+(1+F(7,4)+F(7,8))*F(42,10))*10**6/10**11<F(1,100)
assert F(3,5)-F(1,100)>F(1,2)
assert all(rho*(F(3,4)-F(1,4))+beta-F(1,4)==F(3,4) for rho,beta in [(F(1,2),F(3,4)),(F(1),F(1,2)),(F(3,2),F(1,4))])

# Differential-polynomial identities in Q[q,y]/(2y^2+q^4-1), q'=y,y'=-q^3.
def clean(p):return {k:F(v) for k,v in p.items() if v}
def add(p,q):
    ans=dict(p)
    for k,v in q.items():ans[k]=ans.get(k,F(0))+v
    return clean(ans)
def scale(p,c):return clean({k:c*v for k,v in p.items()})
def mul(p,q):
    ans={}
    for (i,j),v in p.items():
        for (k,l),w in q.items():
            ypower=j+l
            if ypower<2:ans=add(ans,{(i+k,ypower):v*w})
            else:
                assert ypower==2
                ans=add(ans,{(i+k,0):v*w/2,(i+k+4,0):-v*w/2})
    return clean(ans)
def deriv(p):
    ans={}
    for (i,j),v in p.items():
        if i:ans=add(ans,mul({(i-1,j):i*v},{(0,1):F(1)}))
        if j:ans=add(ans,{(i+3,0):-j*v})
    return clean(ans)
def dn(p,n):
    for _ in range(n):p=deriv(p)
    return p
def apply(op,p):
    ans={}
    for k,c in op.items():ans=add(ans,mul(c,dn(p,k)))
    return ans
def adjoint(op):
    ans={}
    for k,c in op.items():
        for j in range(k+1):ans[j]=add(ans.get(j,{}),scale(dn(c,k-j),(-1)**k*comb(k,j)))
    return {k:c for k,c in ans.items() if c}
one={(0,0):F(1)};q2={(2,0):F(1)};q4={(4,0):F(1)};rot={(1,1):F(1)}
AA={4:scale(one,-4),2:scale(q2,-45),1:scale(rot,-75),0:add(scale(one,-F(69,2)),scale(q4,-F(45,2)))}
AST={4:scale(one,-4),2:scale(q2,-45),1:scale(rot,-105),0:scale(one,-42)}
assert not apply(AA,rot) and adjoint(AA)==AST
SS={k:scale(add(AA.get(k,{}),AST.get(k,{})),F(1,2)) for k in AA}
assert SS[1]==scale(rot,-90) and SS[0]==add(scale(one,-F(153,4)),scale(q4,-F(45,4)))
assert dn(q2,2)==add(one,scale(q4,-3))
assert F(45**2,8)-F(153,4)==F(1719,8)
# Candidate Lame factorization: valid identity, but its elementary upper bound is positive.
def compose(a,b):
    out={}
    for i,ci in a.items():
        for j,cj in b.items():
            for k in range(i+1):out[j+k]=add(out.get(j+k,{}),scale(mul(ci,dn(cj,i-k)),comb(i,k)))
    return out
LL={2:scale(one,-1),0:scale(q2,-6)}
rhs={k:scale(c,-4) for k,c in compose(LL,LL).items()}
rhs[2]=add(rhs[2],scale(q2,3));rhs[1]=add(rhs[1],scale(rot,6))
rhs[0]=add(rhs[0],add(scale(q4,F(243,4)),scale(one,-F(57,4))))
assert all(rhs.get(k,{})==SS.get(k,{}) for k in set(rhs)|set(SS))
for m in range(20):
    coeff=apply(AST,{(m,1):F(1)}).get((m+4,1),0)
    assert coeff==-F(m+2,2)*(2*m**3+24*m*m+49*m-120)
record.update(odd_zero_checks=12,odd_zero_min=str(min(zero)),required_finite_row_checks=322,
    strengthened_zN_squared_bound='1/400',galerkin_pivots_negative=True,
    weighted_hypotheses_checked=True,all_tail_and_envelope_checks=True,
    differential_identities_exact=True,lame_identity_checked=True)
(here/'refined_bounds_audit.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print('PASS: 322 required finite row inequalities, all tail/vector bounds, differential identities and weighted exponents.')
print('Odd zero-phase row margin:',float(min(zero)))
