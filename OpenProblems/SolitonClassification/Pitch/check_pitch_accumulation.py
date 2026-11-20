"""Exact rational post-check of the new finite inequalities in PitchAccumulation.txt."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys

def ball_upper(raw):
    if not raw.startswith('['):
        return F(raw)
    fields = raw.removeprefix('[').removesuffix(']').split('+/-')
    return F(fields[0].strip() or '0') + F(fields[1].strip())

def check(path):
    source = path.read_bytes()
    data = json.loads(source)
    assert data['parameter_order'] == ['k0','p0','half_length','alpha','b']
    q = F('2e-7')
    eta = F('3e-40')
    r = F('1e-32')
    tmax = F('5e-35')
    width = F('5e-34')
    assert ball_upper(data['contraction_bound']) < q
    assert ball_upper(data['center_displacement']) < eta
    matrix = [[F(x) for x in row] for row in data['inverse_exact_decimal']]
    assert max(sum(abs(x) for x in row) for row in matrix) < 82
    b55 = matrix[-1][-1]
    assert b55 == F('-10.555605451421052')
    assert eta + q*r + 82*tmax < r
    error = 82*q/(1-q)
    assert F('-10.556') < b55-error < b55+error < F('-10.555')
    assert width + eta/(1-q) < F('10.555')*tmax
    assert F(data['center_exact_decimal'][4]) - r > F('.009')
    assert ball_upper(data['initial_vprime_ball']) < -200
    kmax = F('8.5')
    assert F('1.5')*kmax**2*36+kmax**2+F('.02')*(1+kmax**2) < 4000
    assert -200+4000*F(1,40) == -100
    return {'sha256':hashlib.sha256(source).hexdigest(),'b0':data['center_exact_decimal'][4],
            'pitch_radius':str(width),'target_radius':str(tmax),
            'slope_error':str(error),'status':'passed exact rational suffix checks'}

if __name__ == '__main__':
    if len(sys.argv) < 2:
        raise SystemExit('Usage: python check_pitch_accumulation.py shooting_certificate.json [...]')
    result = [check(Path(x)) for x in sys.argv[1:]]
    print(json.dumps(result,indent=2))
