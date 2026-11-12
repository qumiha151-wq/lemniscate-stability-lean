"""Second-review diagnostics; does not replace the analytic certificate.

Replays the unmodified lightweight checker with only its output redirected.
Checks local degree-60/72 consistency, but does not rerun all 8000 grid steps.
"""
from pathlib import Path
from unittest.mock import patch
import sys, json, hashlib, importlib.util

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import validated_metric_shoot as vm
from flint import arb, arb_mat, ctx


def load_checker():
    spec = importlib.util.spec_from_file_location('reviewed_checker', HERE/'check_shooting_certificate.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    files = ['AnalyticCertificate.txt', 'validated_metric_shoot.py',
             'check_shooting_certificate.py', 'metric_plus_o60_n4000.json',
             'metric_minus_o60_n4000.json', 'shooting_certificate.json']
    before = {n: hashlib.sha256((HERE/n).read_bytes()).hexdigest() for n in files}
    original_write = Path.write_text

    def redirected_write(path, data, *args, **kwargs):
        if path.resolve() == (HERE/'shooting_certificate.json').resolve():
            path = HERE/'IndependentRecheckCertificate.json'
        return original_write(path, data, *args, **kwargs)

    with patch.object(Path, 'write_text', redirected_write):
        load_checker().main()

    ctx.dps = 100
    pstr, estr, _ = vm.center_data()
    k, p, length, alpha, b = [arb(s) for s in pstr]
    e = [arb(s) for s in estr]
    state0 = [v.mid() for v in [k,alpha*e[0]/8,p,alpha*e[1],b,arb(0)]]
    sens0 = [[arb(int(vm.ROWS[i] == j)) for j in range(5)] for i in range(5)]
    tests = [('initial',state0,sens0)]
    for name in ['plus','minus']:
        rep = json.loads((HERE/f'metric_{name}_o60_n4000.json').read_text())
        state = [arb(s).mid() for s in rep['endpoint']]
        matrix = [[arb(s).mid() for s in row] for row in rep['endpoint_fundamental']]
        sens = [[matrix[i][j] for j in range(5)] for i in vm.ROWS]
        tests.append((name+'_endpoint', state, sens))

    local_results = []
    for label,state,sens in tests:
        initial_norm = vm.matrix_norm(vm.full_matrix(sens))
        for sign in [1,-1]:
            h = sign*length/4000
            s = 15*abs(h)
            x60,m60,rx60,rm60 = vm.step(state,sens,h,60)
            x72,m72,rx72,rm72 = vm.step(state,sens,h,72)
            tailx = lambda n: 10*s**(n+1)/(1-s)
            tailm = lambda n: s**(n+1)*((2*n+3)/(1-s)+2*s/(1-s)**2)
            dx = vm.vmax([abs(a-b) for a,b in zip(x60,x72)])
            dm = vm.matrix_norm(vm.full_matrix(m60)-vm.full_matrix(m72))
            bx = rx60+rx72+tailx(60)+tailx(72)
            bm = rm60+rm72+initial_norm*(tailm(60)+tailm(72))
            vm.need(dx<bx, f'{label} {sign} state order consistency')
            vm.need(dm<bm, f'{label} {sign} matrix order consistency')
            local_results.append(dict(label=label,sign=sign,
                state_difference=dx.str(30),state_budget=bx.str(30),
                matrix_difference=dm.str(30),matrix_budget=bm.str(30)))

    after = {n: hashlib.sha256((HERE/n).read_bytes()).hexdigest() for n in files}
    assert before == after, 'An authoritative input changed during the review run'
    result = dict(status='PASS: lightweight checker and six local degree-60/72 comparisons',
        authoritative_inputs_unchanged=True,sha256=after,local_checks=local_results,
        full_8000_step_replay=False,
        scope='Diagnostic replay plus independent analytic/source review; not Lean verification')
    (HERE/'IndependentReviewChecks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'])


if __name__=='__main__':
    main()
