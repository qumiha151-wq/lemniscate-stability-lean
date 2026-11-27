"""Isolate the two distinguished radial components and their angular apertures."""
from fractions import Fraction
import json

from flint import arb, acb, acb_poly, ctx

from certificate import D

M = 65536
INNER = Fraction(3, 40)
OUTER = Fraction(101, 2)


def ball(t):
    return arb(t.numerator) / t.denominator


def check_annuli(path, shape):
    ctx.prec = 150
    data = json.loads(path.read_bytes())
    coord_error = arb(0, "1e-19")
    step = arb(61) / M

    def coefficients(key):
        return [acb(arb(a) / D, arb(b) / D) for a, b in data["rows"][key]]

    K, P, Q = [coefficients(c) for c in ("k", "p", "q")]
    def samples(c):
        full = c + [acb(0)] * (M - 2 * len(c) + 1) + [v.conjugate() for v in c[:0:-1]]
        return [z.real * M + coord_error for z in acb.dft(full, inverse=True)]

    ps, qs = samples(P), samples(Q)
    ks = samples(K)
    eligible = set()
    for i in range(M):
        r = (ps[i]**2 + qs[i]**2).sqrt() + arb(0, step)
        assert r > arb("0.17")
        if r*r > ball(INNER):
            continue
        eligible.add(i)
        assert i > M-130 or i < 230
        assert abs(ks[i]) + 90*step < 9 and r < arb("0.29")
        # p_s=-kq, |q|<=r throughout this cell.
        assert ps[i] - 9*arb("0.29")*step > arb("0.005")

    crit = [i for i in shape["crossing_cells"]["q"] if i in eligible]
    assert len(crit) == 1
    j = crit[0]
    assert qs[j] < 0 and qs[(j+1) % M] > 0

    def polynomial(c):
        return acb_poly(c), c[0].real

    def evaluate(poly, z):
        return 2*poly[0](z).real - poly[1]

    lam = arb(data["length_scale"]) / D
    ppoly, qpoly = polynomial(P), polynomial(Q)
    periodic = polynomial([acb(0)] + [lam*c/acb(0,n) for n,c in enumerate(K[1:], 1)])
    offset = evaluate(periodic, acb(1))

    def geometry(t):
        # Signed traversal phase lies in [-1/2,1/2], on either side of the shooting section.
        assert abs(t) < Fraction(1, 2)
        x = 2*arb.pi()*ball(t)
        z = acb(0, x).exp()
        p = evaluate(ppoly,z) + coord_error
        q = evaluate(qpoly,z) + coord_error
        theta = lam*K[0].real*x + evaluate(periodic,z)-offset + arb(0,"1e-16")
        assert p > 0
        return p*p+q*q, theta+arb.pi()/2-(q/p).atan()

    def end_angle(level, lo_i, hi_i, sign):
        lo, hi = Fraction(lo_i,M), Fraction(hi_i,M)
        def residual(t):
            return sign*(geometry(t)[0]-ball(level))
        assert residual(lo) < 0 and residual(hi) > 0
        for _ in range(30):
            mid = (lo+hi)/2
            value = residual(mid)
            if value > 0:
                hi = mid
            elif value < 0:
                lo = mid
            else:
                raise ArithmeticError("cutpoint cannot be isolated at requested precision")
        # The reconstructed curve has unit speed and radius >0.17 everywhere.
        return geometry((lo+hi)/2)[1] + arb(0, ball(hi-lo)*360)

    iw = (end_angle(INNER,-110,-104,-1)-end_angle(INNER,206,211,1))/(2*arb.pi())
    ow = (end_angle(OUTER,49017-M,49020-M,1)-end_angle(OUTER,49429-M,49434-M,-1))/(2*arb.pi())
    assert iw > arb("0.145") and iw < arb("0.15")
    assert ow > arb("0.008") and ow < arb("0.009")
    assert abs(iw-arb("0.1454958365")) < arb("3e-11")
    assert abs(ow-arb("0.00808022533")) < arb("1e-11")
    assert iw+ow > arb("0.1535760617") and iw+ow < arb("0.1535760619")
    return {"inner_critical_cell": j, "inner_turns": str(iw), "outer_turns": str(ow),
            "sum": str(iw+ow)}
