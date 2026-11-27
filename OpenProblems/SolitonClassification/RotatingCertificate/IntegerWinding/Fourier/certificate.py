"""Global Fourier defect for the four support equations, in normalized periodic time."""
from fractions import Fraction
from pathlib import Path
import argparse
import json
import sys
here = Path(__file__).resolve().parent

from flint import fmpz_poly

D = 10**42
names = ("k","v","p","q")


def verify(path, raw=False):
    packet = json.loads(path.read_bytes())
    assert packet["version"] == 1 and packet["scale"] == D
    N,lam,b=packet["N"],packet["length_scale"],packet["pitch"]
    X = fmpz_poly([0,1])
    den = 16*D**4
    zero = fmpz_poly([])
    def make(row):
        assert len(row)==N+1 and row[0][1]==0
        data = [(a,-i) for a,i in row[:0:-1]]+row
        return tuple(fmpz_poly([int(x[j]) for x in data]) for j in range(2))
    def add(*args):
        return tuple(sum((g[j] for g in args),zero) for j in range(2))
    def times(a,b):
        return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
    def scl(g,a):
        return tuple(z*a for z in g)
    def deriv(g):
        return tuple(fmpz_poly([(-1 if j==0 else 1)*(i-N)*g[1-j][i]
                               for i in range(2*N+1)]) for j in range(2))
    def size(g):
        return sum(abs(int(i)) for z in g for i in z)
    k,v,p,q = [make(packet["rows"][key]) for key in names]
    # All residuals have the shared shift 3N and denominator 16 D^4.
    shift = X**N
    linear = 16*D**3*shift**2
    constant = (16*D**3*lam*shift**3,zero)
    residual = [
        add(scl(deriv(k),linear),scl(v,-128*D**2*lam*shift**2)),
        add(scl(deriv(v),linear),scl(times(times(k,k),k),lam),
            scl(p,2*D**2*lam*shift**2),scl(q,2*D*lam*b*shift**2)),
        add(scl(deriv(p),linear),scl(times(k,q),16*D*lam*shift)),
        add(scl(deriv(q),linear),scl(constant,-1),scl(times(k,p),-16*D*lam*shift))]
    if raw:
        return residual, den
    def atzero(poly):
        return sum(int(x) for x in poly[0])
    def cceil(x,q):
        return (x*q).__ceil__()
    phaseE,phaseG=map(Fraction,("-0.05995393111634394","-0.9982011451324311"))
    return dict(modes=N,residual_denominator=str(den),
                l1_residual_numerators=[str(size(g)) for g in residual],
                residual_times_1e12_upper=[cceil(Fraction(size(g),den),10**12) for g in residual],
                residual_times_1e30_upper=[cceil(Fraction(size(g),den),10**30) for g in residual],
                mean_turn_error_times_1e12_upper=cceil(abs(1+Fraction(lam*int(k[0][N]),D**2)),10**12),
                phase_error_times_1e12_upper=cceil(abs((8*atzero(v)*phaseG-atzero(q)*phaseE)/D),10**12))


