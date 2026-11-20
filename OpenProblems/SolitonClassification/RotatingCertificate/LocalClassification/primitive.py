"""Replay the archived positive-time state centers and exclude shorter support periods."""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import hashlib, json, sys

here = Path(__file__).resolve().parent
old = here.parent / "classification_odd_branch_interval"
sys.path.insert(0, str(old))
import validated_metric_shoot as original
from flint import arb, arb_poly, ctx

def interval_text(x):
    return x.str(100)

def state_step(state, h):
    # The state part of original.step is independent of all variational variables.
    polys = [arb_poly([x]) for x in state]
    k, u, p, q, _, _ = polys
    b = state[4]
    for n in range(60):
        k2 = k*k
        k3 = k2*k
        kq = k*q
        kp = k*p
        coeff = [8*u[n], -k3[n]/16-p[n]/8-b*q[n]/8, -kq[n],
                 kp[n]+(1 if n == 0 else 0), arb(0), k[n]]
        for poly, c in zip(polys, coeff):
            poly[n+1] = c / (n+1)
    return [poly(h).mid() for poly in polys]

def prime(n):
    return all(n % j for j in range(2, isqrt(n)+1))

def main():
    ctx.dps=100
    report = json.loads((old/"metric_plus_o60_n4000.json").read_bytes())
    assert report["source_sha256"] == hashlib.sha256((old/"validated_metric_shoot.py").read_bytes()).hexdigest()
    k,p,l,a,b = [arb(x) for x in report["center_exact_decimal"]]
    e = [arb(x) for x in report["phase_exact_decimal"]]
    state = [x.mid() for x in [k,a*e[0]/8,p,a*e[1],b,arb(0)]]
    init = state[:]
    h = l/4000
    targets = {}
    for divisor in range(2,2561):
        if prime(divisor):
            index = (16000+divisor)//(2*divisor)
            assert abs(F(8000,divisor)-index)<F(1,2)
            targets.setdefault(index, []).append(divisor)
    bounds = {}
    for j in range(4001):
        for divisor in targets.get(j, []):
            dt = abs(2*l/divisor-j*h) + arb("2e-32")
            # Uniform true trajectory position within 4e-29 of each reference node.
            gaps = [abs(state[i]-init[i])-dt*bound-arb("1e-27")
                    for i,bound in enumerate([36,arb("39.4665625"),arb("72.25"),arb("73.25")])]
            gap=original.vmax(gaps)
            assert gap > arb(".01"), (divisor,j,interval_text(gap))
            ids=[i for i in range(4) if gaps[i] > arb(".01") and
                 abs(state[i]-init[i])-arb("1e-27")>arb(".4")]
            assert ids
            bounds[divisor] = {"node":j,"coordinate":ids[0],"gap_lower":interval_text(gap.lower())}
        if j < 4000:
            state=state_step(state,h)
    assert [interval_text(x) for x in state] == report["endpoint"]
    (here/"PrimitiveChecks.json").write_text(json.dumps(dict(
        original_plus_sha256=hashlib.sha256((old/"metric_plus_o60_n4000.json").read_bytes()).hexdigest(),
        original_integrator_sha256=report["source_sha256"], count=len(bounds), checks=bounds,
        endpoint_bytes_match=True, global_gap_lower="0.01"),indent=2)+"\n")
    print(len(bounds), "prime divisors excluded")

if __name__=="__main__":
    main()
