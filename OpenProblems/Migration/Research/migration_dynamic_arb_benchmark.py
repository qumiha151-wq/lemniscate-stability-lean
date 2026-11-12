"""Independent b=1 baseline for the actual-flow E^3 J quadrature.

This evaluates the unsimplified anisotropic-lemniscate formulas, then tests
them against F=-(15/2)p. It does not modify the b=99/100 countertest.
Numerical ball quadrature only; the exact identity is proved in the note.
"""
import sys, json
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'pydeps'))
from flint import arb, acb, ctx

def run(bits, tol):
    ctx.prec = bits
    b = acb(1)
    def quantities(u, analytic):
        s, c = u.sin(), u.cos()
        r = s*s
        H = 1+r
        P = r**3 + (9*b*b-6)*r*r + (9-6*b*b)*r + b*b
        P1 = 3*r*r + 2*(9*b*b-6)*r + 9-6*b*b
        P2 = 6*r + 2*(9*b*b-6)
        root = P.sqrt(analytic=analytic)
        g = root/(H*H)
        f = 3*b*H**4/root**3
        ell = 4/H-acb(3)/2*P1/P
        ell1 = -4/H**2-acb(3)/2*(P2/P-(P1/P)**2)
        h = P1/(2*P)-2/H
        U = -1+2*(1-r)*ell
        U1 = -2*ell+2*(1-r)*ell1
        k = c*f
        F = c*(f*(U+2*r*(ell*U+U1)-2*r*h*U)/g**2+(1-r)*f**3/2)
        p = -b*c**3/root
        q = s*c*(-3+r+b*b*(1-3*r))/(H*root)
        Q = 2*q*q-p*p
        return [k*k*g/2, p*p*g, F*F*g, k*F*Q*g,
                F*p*g, k*p*Q*g, (F+acb(15)/2*p)**2*g]
    names = ['E','J','D','KQF','force_virial','geometric_identity','soliton_residual_square']
    vals = {}
    for i, name in enumerate(names):
        v = 4*acb.integral(lambda z, analytic: quantities(z,analytic)[i],
            0, acb.pi()/2, abs_tol=arb(tol), rel_tol=arb(tol),
            eval_limit=200000, depth_limit=40, deg_limit=100)
        assert v.is_finite() and v.imag.contains(0), (name,v)
        vals[name] = v.real
    E,J,D,I = [vals[k] for k in ['E','J','D','KQF']]
    errors = dict(E_minus_15J_over_2=E-arb(15)/2*J,
        D_minus_15E_over_2=D-arb(15)/2*E,
        I_plus_E=I+E,
        force_virial=vals['force_virial']+E,
        geometric_identity=vals['geometric_identity']-J,
        soliton_residual_square=vals['soliton_residual_square'],
        Delta=D-E*E/J,
        E3J_flow_derivative=E**3*I+4*E**4-3*E**2*J*D)
    assert all(x.contains(0) for x in errors.values()), errors
    return dict(bits=bits,tolerance=tol,b='1',
        enclosures={k:str(v) for k,v in vals.items()},
        zero_tests={k:str(v) for k,v in errors.items()},all_zero_tests_contain_zero=True)

if __name__ == '__main__':
    report = dict(status='Arb baseline quadrature, not a Lean or ODE certificate',
        curve='(cos(u)/(1+sin(u)^2), sin(u)*cos(u)/(1+sin(u)^2))',
        exact_identity='F=-(15/2)p; E=(15/2)J; D=(15/2)E; Delta=0; (E^3 J)prime=0',
        runs=[run(192,'1e-35'),run(320,'1e-65')])
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
