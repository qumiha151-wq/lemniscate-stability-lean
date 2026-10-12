from pathlib import Path
from fractions import Fraction as F
from math import comb
import json

# Load the exact Laurent-polynomial engine without its report-writing tail.
ns={}
source=Path(__file__).with_name('strict_geometry_algebra.py').read_text(encoding='utf-8')
exec(source.split('record=dict(')[0],ns)
V=ns['V'];add=ns['add'];mul=ns['mul'];scale=ns['scale'];var=ns['var'];D=ns['D']
k,k1,k2,k3,f,v,w,z,y,a,g,h,b,c=[V[x] for x in ('k','k1','k2','k3','f','v','w','z','y','a','g','h','b','c')]
sq=lambda x:mul(x,x)
cube=lambda x:mul(x,x,x)
d0=scale(add(mul(k1,f),mul(k,v)),-1)
e0=scale(add(mul(k2,f),scale(mul(k1,v),2)),-1)
N0=add(mul(k,sq(a)),scale(mul(k,sq(v)),2),mul(k1,f,v))
J0=mul(a,d0);J00=add(sq(d0),mul(a,e0))
N1=add(mul(k1,sq(a)),scale(mul(k,a,d0),2),scale(mul(k1,sq(v)),3),mul(k2,f,v))
N00=add(mul(k2,sq(a)),scale(mul(k1,a,d0),4),scale(mul(k,sq(d0)),2),scale(mul(k,a,e0),2),scale(mul(k2,sq(v)),4),mul(k3,f,v))
N01=add(scale(mul(sq(k),a),-2),scale(mul(k1,v),9),mul(k2,f))
N03=add(scale(mul(k,v),2),scale(mul(k1,f),-1))
N=add(N0,mul(a,w));J=add(J0,mul(v,w))
Ns=add(N1,scale(mul(k,v,w),3),mul(a,z))
Js=add(J00,scale(mul(a,k,w),-1),sq(w),mul(v,z))
Nss=add(N00,mul(N01,w),scale(mul(k,sq(w)),3),mul(N03,z),mul(a,y))
assert D(N)==Ns
assert D(J)==Js
assert D(Ns)==Nss
div=lambda p,an,gn:mul(p,var('a',-an),var('g',-gn))
B1=scale(div(v,0,6),10)
B2=add(scale(div(N03,1,4),-1),div(add(scale(mul(a,J0),7),scale(mul(N0,v),3)),1,6))
B3=add(scale(div(ns['const'](1),0,6),3),scale(div(add(scale(sq(v),18),scale(sq(a),F(1,2))),0,8),-1))
B4=add(scale(div(k,1,4),-3),div(add(scale(mul(k,sq(v)),21),scale(N0,3),scale(mul(sq(a),k),-3)),1,6),scale(div(add(scale(mul(N0,sq(v)),18),scale(mul(a,J0,v),36),scale(mul(N0,sq(a)),F(3,2))),1,8),-1))
B5=add(scale(div(N01,1,4),-1),div(add(scale(mul(N1,v),7),scale(mul(k,v,J0),21),scale(mul(a,J00),3),scale(mul(N0,a,k),-3)),1,6),scale(div(add(scale(mul(N0,J0,v),36),scale(mul(a,sq(J0)),18),scale(mul(sq(N0),a),F(3,2))),1,8),-1))
B6=add(scale(div(N00,1,4),-1),div(add(scale(mul(N1,J0),7),scale(mul(N0,J00),3)),1,6),scale(div(add(scale(mul(N0,sq(J0)),18),scale(cube(N0),F(1,2))),1,8),-1),scale(mul(c,add(h,f)),-1),div(mul(c,b,v),1,0))
expanded=add(scale(div(y,0,4),-1),mul(B1,w,z),mul(B2,z),mul(B3,cube(w)),mul(B4,sq(w)),mul(B5,w),B6)
assert expanded==ns['graph_flow']
bern6=[[1],[1,F(1,12)],[1,F(1,6),F(1,60)],[1,F(1,4),F(1,20),F(1,160)],[1,F(1,3),F(1,10),F(1,40),F(1,240)],[1,F(5,12),F(1,6),F(1,16),F(1,48),F(1,192)],[1,F(1,2),F(1,4),F(1,8),F(1,16),F(1,32),F(1,64)]]
bern4=[[1],[1,F(1,8)],[1,F(1,4),F(1,24)],[1,F(3,8),F(1,8),F(1,32)],[1,F(1,2),F(1,4),F(1,8),F(1,16)]]
for degree,rows in [(6,bern6),(4,bern4)]:
    for j,row in enumerate(rows):
        assert row==[F(comb(j,l),2**l*comb(degree,l)) for l in range(j+1)]
assert (2660000+(1+F(7,4)+F(7,8))*4200000)/10**11==F(17885,10**8)
assert F(9,10)*75-F(1,10)*F(1719,8)==F(3681,80)
record={'N_first_derivative':True,'J_first_derivative':True,'N_second_derivative':True,'all_six_explicit_nonlinear_coefficients':True,'degree_6_and_degree_4_Bernstein_conversions':True,'finite_rank_total_exact':True,'residual_coercivity_constant_exact':True,'arithmetic':'exact rational Laurent polynomials; no eigenvalue calculation'}
Path(__file__).with_name('expanded_algebra_verification.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps(record,indent=2))
