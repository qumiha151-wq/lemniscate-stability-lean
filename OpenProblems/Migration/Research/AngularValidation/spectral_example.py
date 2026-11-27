"""Exact Fourier residual for a noncircular, closed elastic flow on one time slab.

A dictionary key (n,j) denotes exp(i n x) (tau/h)^j. Each coefficient
is a pair of rational numbers. There is no sampling in space or time.
"""
from fractions import Fraction as Q
import json


def add(*series):
    out = {}
    for poly in series:
        for key, (a, b) in poly.items():
            c, d = out.get(key, (0, 0))
            out[key] = c + a, d + b
    return {k: v for k, v in out.items() if any(v)}


def scale(poly, factor):
    return {k: (factor*a, factor*b) for k, (a, b) in poly.items() if factor}


def product(left, right):
    out = {}
    for (n, j), (a, b) in left.items():
        for (m, l), (c, d) in right.items():
            key = n+m, j+l
            p, q = out.get(key, (0, 0))
            out[key] = p+a*c-b*d, q+a*d+b*c
    return {k: v for k, v in out.items() if any(v)}


def dx(poly):
    return {(n, j): (-n*b, n*a) for (n, j), (a, b) in poly.items() if n}


def primitive(poly):
    return {(n, j): (b/Q(n), -a/Q(n)) for (n, j), (a, b) in poly.items() if n}


def dt(poly, h):
    return {(n, j-1): (j*a/h, j*b/h) for (n, j), (a, b) in poly.items() if j}


def rhs(phi):
    # theta = x + phi has rotation index one.
    v = add({(0, 0): (Q(1), Q(0))}, dx(phi))
    w = dx(v)
    v2, w2 = product(v, v), product(w, w)
    source = add(w2, scale(product(v2, v2), Q(-1, 2)))
    return add(scale(dx(dx(w)), -1), scale(product(v2, w), Q(-5, 2)),
               product(v, primitive(source))), v, w


def upper(poly):
    # Sum of coefficient majorants bounds the Fourier l1 norm at each time.
    return sum(abs(a)+abs(b) for a, b in poly.values())


def verify():
    h = Q(1, 10**6)
    phi0 = {(2, 0): (Q(0), Q(-1, 20)), (-2, 0): (Q(0), Q(1, 20))}
    initial_velocity, _, _ = rhs(phi0)
    reference = add(phi0, {(n, 1): (h*a, h*b)
                           for (n, j), (a, b) in initial_velocity.items()})
    ref_rhs, ref_v, ref_w = rhs(reference)
    residual = add(dt(reference, h), scale(ref_rhs, -1))
    assert residual and all(j > 0 for n, j in residual)
    assert all(n % 2 == 0 for n, j in reference)
    # These checks also detect an accidental loss of the real-valued symmetry.
    for poly in (reference, residual):
        for (n, j), (a, b) in poly.items():
            assert poly.get((-n, j)) == (a, -b)
    radius = Q(7, 10**8)
    v = upper(ref_v) + radius/2
    w = upper(ref_w) + radius
    k = (5*v*w + w*w + Q(5, 2)*v**4)/2 + Q(5, 2)*v*v + 2*v*w
    # 1/707 majorizes sqrt(2 h), verified by squaring.
    s = Q(1, 707)
    assert s*s >= 2*h
    defect = upper(residual)
    barrier = (h+s)*(defect+k*radius)
    assert barrier < radius
    def ceil_scaled(x, bits):
        return (x*bits).__ceil__()
    return dict(time_slab=str(h), angle_X_radius=str(radius),
                nonzero_residual_coefficients=len(residual),
                maximal_spatial_mode=max(abs(n) for n,j in residual),
                maximal_time_degree=max(j for n,j in residual),
                residual_times_1e9_upper=ceil_scaled(defect, 10**9),
                lipschitz_times_1e6_upper=ceil_scaled(k, 10**6),
                barrier_times_1e12_upper=ceil_scaled(barrier, 10**12),
                initial_velocity_nonzero_modes=sorted({n for n,j in initial_velocity if n}))


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
