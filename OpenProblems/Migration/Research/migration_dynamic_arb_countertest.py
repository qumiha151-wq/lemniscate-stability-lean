"""Certified Arb quadrature of the ACTUAL initial (E^3 J)' on a smooth curve.
No ODE enclosure or Lean certificate is asserted. All sqrt calls forward
the analytic flag required by acb.integral. The parameter b is exact 99/100.
"""
import sys, json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'pydeps'))
from flint import arb, acb, ctx

def run(bits, tol):
    ctx.prec=bits
    b=acb(99)/100
    b2=b*b
    def quantities(u, analytic):
        s,c=u.sin(),u.cos()
        r=s*s
        H=1+r
        P=r**3+(9*b2-6)*r*r+(9-6*b2)*r+b2
        P1=3*r*r+2*(9*b2-6)*r+9-6*b2
        P2=6*r+2*(9*b2-6)
        root=P.sqrt(analytic=analytic)
        g=root/(H*H)
        f=3*b*H**4/root**3
        ell=4/H-acb(3)/2*P1/P
        ell1=-4/(H*H)-acb(3)/2*(P2/P-(P1/P)**2)
        h=P1/(2*P)-2/H
        U=-1+2*(1-r)*ell
        U1=-2*ell+2*(1-r)*ell1
        k=c*f
        F=c*(f*(U+2*r*(ell*U+U1)-2*r*h*U)/(g*g)+(1-r)*f**3/2)
        p=-b*c**3/root
        q=s*c*(-3+r+b2*(1-3*r))/(H*root)
        Q=2*q*q-p*p
        return [k*k*g/2,p*p*g,F*F*g,k*F*Q*g,F*p*g,k*p*Q*g]
    names=['E','J','D','KQF','force_virial','geometric_identity']
    vals={}
    for i,name in enumerate(names):
        v=4*acb.integral(lambda z,analytic: quantities(z,analytic)[i],
            0,acb.pi()/2,abs_tol=arb(tol),rel_tol=arb(tol),
            eval_limit=200000,depth_limit=40,deg_limit=100)
        assert v.is_finite(),(name,v)
        assert v.imag.contains(0),(name,v)
        vals[name]=v.real
    E,J,D,KQF=[vals[k] for k in ['E','J','D','KQF']]
    derivative=E**3*KQF+4*E**4-3*E**2*J*D
    assert J>0
    assert derivative>0,derivative
    assert (vals['force_virial']+E).contains(0)
    assert (vals['geometric_identity']-J).contains(0)
    return dict(bits=bits,tolerance=tol,b='99/100',
                enclosures={k:str(v) for k,v in vals.items()},
                E3J_flow_derivative=str(derivative),strictly_positive=True,
                force_virial_error=str(vals['force_virial']+E),
                geometric_identity_error=str(vals['geometric_identity']-J))

results=[run(192,'1e-35'),run(320,'1e-65')]
data={'status':'Certified complex-ball quadrature with analytic branch checks; not a Lean or ODE certificate.',
      'curve':'(cos(u)/(1+sin(u)^2), (99/100)*sin(u)*cos(u)/(1+sin(u)^2))',
      'statement':'The actual initial free-elastic-flow derivative of E^3 J is positive.',
      'runs':results}
Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(data,indent=2))
