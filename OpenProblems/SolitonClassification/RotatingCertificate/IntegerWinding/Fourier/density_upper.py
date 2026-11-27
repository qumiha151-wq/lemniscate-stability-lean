"""An upper enclosure for the variation density of all radial-arm pairs.

The caller supplies the whole-orbit shape certificate (see shape.py). On
one arm, d psi/ds = -p/r^2 in radians. At an interior radius meeting n
arms, the triangle inequality charges each arm's phase variation at most
n-1 times when summing the variations of all unordered pair differences.
"""
from bisect import bisect_left, bisect_right
from hashlib import sha256
import json

from certificate import D, here
from flint import acb, arb, ctx


def check_density_upper(path, shape):
    ctx.prec = 120
    data = json.loads(path.read_bytes())
    canonical = (json.dumps(data, separators=(",", ":")) + "\n").encode()
    assert sha256(canonical).hexdigest() == shape["packet_sha256"]
    mesh = shape["grid_size"]
    assert mesh == 65536 and shape["transfer_radius"] == "1e-19"
    tips = shape["crossing_cells"]["q"]
    assert len(tips) == len(set(tips)) == 72 and tips == sorted(tips)
    err = arb(0, "1e-19")
    def coefficients(key):
        return [acb(arb(a)/D, arb(b)/D) for a, b in data["rows"][key]]

    def samples(key):
        c = coefficients(key)
        full = c + [acb(0)]*(mesh-2*len(c)+1) + [v.conjugate() for v in c[:0:-1]]
        return [z.real*mesh + err for z in acb.dft(full, inverse=True)]

    # The whole-orbit transfer also bounds pi times the length scale by
    # 2e-30 about its Fourier value (WholeOrbitFourier.md and TwoAnnuli.md).
    step = (2*arb.pi()*arb(data["length_scale"])/D + arb("4e-30"))/mesh
    assert step < arb(61)/mesh
    p, q = samples("p"), samples("q")
    radii = [(a*a + b*b).sqrt() for a,b in zip(p,q)]
    k = coefficients("k")
    max_curvature = abs(k[0]) + 2*sum(abs(z) for z in k[1:]) + arb("1e-19")

    # The radius is 1-Lipschitz in physical arclength. Integer enclosures
    # are used only for searching which radial ranges might overlap.
    scale = 2**24
    def lower(r):
        return int((scale*r.lower()).floor().unique_fmpz())

    def upper(r):
        return int((scale*r.upper()).ceil().unique_fmpz())

    cell_low = [lower(r-step) for r in radii]
    cell_high = [upper(r+step) for r in radii]
    ends = list(zip(tips,tips[1:]+tips[:1]))
    starts = sorted(min(cell_low[a],cell_low[b]) for a,b in ends)
    stops = sorted(max(cell_high[a],cell_high[b]) for a,b in ends)
    budget = arb(0)
    max_overlap = 0
    for j,r in enumerate(radii):
        count = bisect_right(starts,cell_high[j]) - bisect_left(stops,cell_low[j])
        assert count >= 1 and r-step > 0
        # |p_s| = |k q| <= K (r_start+step); p is a signed support coordinate.
        p_bound = abs(p[j]) + step*max_curvature*(r+step)
        angular_speed = p_bound/(r-step)**2
        budget += (count-1)*angular_speed
        max_overlap = max(max_overlap,count)
    total = budget*step/(2*arb.pi())
    assert total < 14
    return {"grid_size":mesh, "maximum_possible_arms":max_overlap,
            "sum_upper_endpoint":str(total.upper()), "strict_density_upper":14}


if __name__ == "__main__":
    report = json.loads((here/"shape_report.json").read_bytes())
    print(json.dumps(check_density_upper(here/"global_reference.json",report),indent=2))
