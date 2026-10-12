"""Exact independent algebra for the normal-graph formula and linearization.

This is an internal review aid. The manuscript defines all coefficients and
contains its own analytic proof; it does not depend on executing this file.
"""
from fractions import Fraction as F
from pathlib import Path
import json

names=('k','k1','k2','k3','k4','f','v','w','z','y','a','g','h','b','c')
size=len(names)
zero=(0,)*size
def clean(p): return {m:F(c) for m,c in p.items() if c}
def const(c): return {zero:F(c)} if c else {}
def var(n,power=1):
    m=list(zero);m[names.index(n)]=power
    return {tuple(m):F(1)}
def add(*ps):
    out={}
    for p in ps:
        for m,c in p.items():out[m]=out.get(m,F(0))+c
    return clean(out)
def scale(p,c):return clean({m:x*c for m,x in p.items()})
def mul(*ps):
    out=const(1)
    for p in ps:
        nextp={}
        for m,c in out.items():
            for n,d in p.items():
                power=tuple(x+y for x,y in zip(m,n))
                nextp[power]=nextp.get(power,F(0))+c*d
        out=clean(nextp)
    return out
def partial(p,n):
    index=names.index(n);out={}
    for m,c in p.items():
        if m[index]:
            power=list(m);power[index]-=1
            out[tuple(power)]=c*m[index]
    return clean(out)
V={n:var(n) for n in names}
Da=scale(add(mul(V['k1'],V['f']),mul(V['k'],V['v'])),-1)
Dg=mul(add(mul(V['a'],Da),mul(V['v'],V['w'])),var('g',-1))
derivative={
    'k':V['k1'],'k1':V['k2'],'k2':V['k3'],'k3':V['k4'],
    'f':V['v'],'v':V['w'],'w':V['z'],'z':V['y'],
    'a':Da,'g':Dg,'h':scale(mul(V['k'],V['b']),-1),
    'b':add(const(1),mul(V['k'],V['h']))}
def D(p):
    return add(*(mul(partial(p,n),dp) for n,dp in derivative.items()))

kgraph=mul(add(mul(V['k'],var('a',2)),scale(mul(V['k'],var('v',2)),2),mul(V['a'],V['w']),mul(V['k1'],V['f'],V['v'])),var('g',-3))
hgraph=mul(add(mul(V['a'],add(V['h'],V['f'])),scale(mul(V['b'],V['v']),-1)),var('g',-1))
laplacian=mul(var('g',-1),D(mul(var('g',-1),D(kgraph))))
graph_flow=scale(mul(V['g'],var('a',-1),add(laplacian,scale(mul(kgraph,kgraph,kgraph),F(1,2)),mul(V['c'],hgraph))),-1)
remainder=add(graph_flow,mul(var('g',-4),V['y']))
jet_indices=[names.index(n) for n in ('w','z','y')]
monomials=set(tuple(m[i] for i in jet_indices) for m in remainder)
allowed={(1,1,0),(0,1,0),(3,0,0),(2,0,0),(1,0,0),(0,0,0)}
assert monomials == allowed,monomials

def at_origin(p):
    out={}
    zero_indices=[names.index(n) for n in ('f','v','w','z','y')]
    unit_indices=[names.index(n) for n in ('a','g')]
    for m,c in p.items():
        if any(m[i]!=0 for i in zero_indices):continue
        power=list(m)
        for i in unit_indices:power[i]=0
        power=tuple(power)
        out[power]=out.get(power,F(0))+c
    return clean(out)
linear={n:at_origin(partial(graph_flow,n)) for n in ('f','v','w','z','y')}
# a=1-k*f and g=sqrt(a*a+v*v) imply da=-k*f, dg=-k*f at zero.
linear['f']=add(linear['f'],scale(mul(V['k'],at_origin(add(partial(graph_flow,'a'),partial(graph_flow,'g')))),-1))
expected={
    'y':const(-1),'z':{},'w':scale(var('k',2),-F(5,2)),
    'v':add(scale(mul(V['k'],V['k1']),-5),mul(V['c'],V['b'])),
    'f':scale(add(scale(var('k1',2),3),scale(mul(V['k'],V['k2']),4),scale(var('k',4),F(3,2)),V['c']),-1)}
assert linear==expected, {n:(linear[n],expected[n]) for n in expected if linear[n]!=expected[n]}
assert at_origin(graph_flow)==scale(add(V['k2'],scale(var('k',3),F(1,2)),mul(V['c'],V['h'])),-1)

# Exact elementary arithmetic behind the length and interval constructions.
tan2=F(2,5)/(1-F(1,25))
tan4=2*tan2/(1-tan2*tan2)
assert (tan4-F(1,239))/(1+tan4/F(239))==1
record=dict(graph_curvature_and_support_formula_used=True,
    fourth_order_coefficient_exact='-g_f^-4',
    remainder_monomials=['w*z','z','w^3','w^2','w','1'],
    all_six_coefficients_defined_by_extraction=True,
    graph_linearization_in_arclength_exact=True,
    machin_tangent_identity_exact=True,
    polynomial_terms=len(graph_flow),all_arithmetic='exact rational Laurent polynomials')
Path(__file__).with_name('strict_geometry_algebra.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps(record,indent=2))
