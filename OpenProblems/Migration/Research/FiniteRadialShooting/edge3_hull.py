"""Validated local exclusion at both nontrivial integer-holonomy passages of edge 3."""

from flint import arb, arb_poly, ctx


def field(z,b):
    k,v,p,q,t=z
    return [v,-k**3/2-p-b*q,-k*q,1+k*p,k]


def jets(z,b,n):
    polys=[arb_poly([v]) for v in z]
    k,v,p,q,t=polys
    for i in range(n):
        row=(v[i],-(k*k*k)[i]/2-p[i]-b*q[i],-(k*q)[i],int(i==0)+(k*p)[i],k[i])
        for poly,c in zip(polys,row):poly[i+1]=c/(i+1)
    return polys


def cross(p,q): return p[0]*q[1]-p[1]*q[0]
