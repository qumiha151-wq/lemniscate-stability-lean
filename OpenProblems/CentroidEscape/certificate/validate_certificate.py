"""Validate a computer-assisted asymmetric-expander shooting certificate.

This is a rigorous Arb calculation conditional on the analytic estimates in
certificate_plan.txt. It is NOT a full Lean formalization. In particular the
ODE/Taylor/Gronwall/fixed-point/reflection arguments remain human mathematics.

No numerical-center file is modified. All seven evaluations are independent.
"""
import sys, json, time, argparse, hashlib
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'pydeps'))
from flint import arb, arb_mat, ctx
import flint
from arb_shoot import shoot

WEIGHT_STRINGS = ['1','1','4','4','16','64','1']
INNER_STRINGS = ['1.45','2.26','1.001','1.001','3.02','4.15']
TUBE_STRINGS = ['1.6','2.4','1.1','1.1','3.5','6']
ORDER = 160
STEPS = 750
DPS = 180

def enc(x):
    return x.str(DPS)

def max_arb(xs):
    ans = arb(0)
    for x in xs:
        ans = ans.max(x)
    return ans

def norm_vec(xs):
    return max_arb([abs(x) for x in xs])

def norm_matrix(A):
    return max_arb([sum((abs(A[i,j]) for j in range(3)), arb(0)) for i in range(3)])

def need(cond, label):
    if not bool(cond):
        raise AssertionError(label)

def evaluate(job):
    label, center, coord, sign = job
    ctx.dps = DPS
    delta = arb('1e-70')
    p = [arb(x) for x in center]
    if coord is not None:
        p[coord] += sign * delta
    need(p[2] > arb(0), f'{label}: positive time')
    need(p[2] < arb('7.5'), f'{label}: time below 7.5')
    tic = time.perf_counter()
    f, state, bounds = shoot(*p, order=ORDER, nsteps=STEPS)
    for i, limit in enumerate(INNER_STRINGS):
        need(bounds[i] < arb(limit), f'{label}: grid bound index {i}')
    # Arb balls already include all rounding errors of the polynomial
    # iteration. The following additional ball accounts only for truncation.
    error = arb('1e-118')
    inflated = [s + arb(0, arb(w) * error) for s,w in zip(state,WEIGHT_STRINGS)]
    return {
        'label': label,
        'parameter_balls': [enc(x) for x in p],
        'raw_state_balls': [enc(x) for x in state],
        'rounding_radii': [enc(x.rad()) for x in state],
        'grid_abs_bound_balls': [enc(x) for x in bounds],
        'true_state_balls': [enc(x) for x in inflated],
        'true_residual_balls': [enc(inflated[i]) for i in [1,2,5]],
        'seconds': time.perf_counter()-tic,
        'grid_bounds_passed': True,
    }

def analytic_checks():
    h = arb(1)/100
    T = arb('7.5')
    E = (8*T).exp()
    need(E < arb('2e26'), 'exp(60) upper bound')
    tau = (12*h)**(ORDER+1)/(3*(1-12*h))
    trunc = STEPS * E * tau
    need(trunc < arb('1e-118'), 'global Taylor truncation budget')
    excursion = (1/(1-12*h).sqrt()-1)/3
    need(excursion < arb('.023'), 'local Taylor majorant excursion')
    margins = [(arb(t)-arb(i))/arb(w) for t,i,w in
               zip(TUBE_STRINGS,INNER_STRINGS,WEIGHT_STRINGS)]
    # A uniform parameter-neighborhood bootstrap covers every intermediate
    # point on finite-difference segments, not just the seven evaluations.
    parameter_neighborhood = arb('1e-70') + arb('1e-80')
    perturbation = (E+2)*parameter_neighborhood
    for margin in margins:
        need(margin-excursion-arb('1e-118')-perturbation > arb('.001'),
             'uniform tube bootstrap spare margin')
    hessian_formula = 64*(6*E**2+16*E+16)
    need(hessian_formula < arb('1e56'), 'shooting Hessian bound')
    # Elementary rational checks for the polynomial-vector-field envelopes.
    max_first_oscillator = arb('3.5') + 4*arb('1.1')
    max_first_cubic = (2*arb('1.1')+4*(arb('1.6')+arb('2.4'))
                       +arb('1.5')*arb('3.5')**2*16)/64
    need(max_first_oscillator < 8, 'oscillator Jacobian row')
    need(max_first_cubic < 8, 'cubic Jacobian row')
    for field_row in [arb('1.1'), arb('3.5')*arb('1.1')/4,
                      arb(6)/16,
                      (arb('3.5')**3/2+(arb('1.6')+arb('2.4'))*arb('1.1'))/64,
                      arb('1.6')]:
        need(field_row < 2, 'field-value envelope')
    need(12*arb('3.5')+arb(1)/4 < 44, 'Hessian row')
    need(arb(192)/6 <= 54, 'cubic Taylor majorization')
    need(arb(8) <= 18 and arb(44)/2 <= 54, 'lower Taylor majorization')
    return {
        'weights': WEIGHT_STRINGS,
        'inner_grid_bounds': INNER_STRINGS,
        'outer_tube_bounds': TUBE_STRINGS,
        'weighted_field_bound': '2',
        'weighted_jacobian_bound': '8',
        'weighted_hessian_bound': '44',
        'weighted_third_derivative_bound': '192',
        'majorant': 'w(t)=((1-12*t)^(-1/2)-1)/3',
        'step_tail_bound_ball': enc(tau),
        'global_truncation_bound_ball': enc(trunc),
        'global_truncation_budget': '1e-118',
        'local_excursion_ball': enc(excursion),
        'uniform_parameter_perturbation_bound_ball': enc(perturbation),
        'shooting_hessian_formula_ball': enc(hessian_formula),
        'shooting_hessian_budget': '1e56',
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--center',required=True)
    ap.add_argument('--workers',type=int,default=3)
    ap.add_argument('--output',default=str(HERE/'validated_certificate.json'))
    args = ap.parse_args()
    ctx.dps = DPS
    center_path = Path(args.center).resolve()
    center_source = center_path.read_bytes()
    center = json.loads(center_source)['center']
    need(len(center)==3, 'three center coordinates')
    output = Path(args.output)
    log_path = output.with_suffix('.log')
    output.write_text(json.dumps({
        'status':'NOT YET VERIFIED: this invocation has not completed its certificate checks',
        'center':center,
        'center_source_sha256':hashlib.sha256(center_source).hexdigest(),
    },indent=2),encoding='utf-8')
    logs=[]
    def log(s):
        logs.append(s);print(s,flush=True)
        log_path.write_text('\n'.join(logs)+'\n',encoding='utf-8')
    log('Computer-assisted certificate; NOT a full Lean formalization.')
    log(f'center source {center_path.name}; order={ORDER}; steps={STEPS}; dps={DPS}')
    analytic = analytic_checks()
    log('Analytic-envelope numerical inequalities passed.')
    jobs=[('center',center,None,0)]
    for j in range(3):
        jobs += [(f'plus{j}',center,j,1),(f'minus{j}',center,j,-1)]
    results={}
    if args.workers == 1:
        for job in jobs:
            result=evaluate(job);results[result['label']]=result
            log(f"{result['label']} passed grid bounds in {result['seconds']:.2f}s")
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            futures=[pool.submit(evaluate,j) for j in jobs]
            for future in as_completed(futures):
                result=future.result();results[result['label']]=result
                log(f"{result['label']} passed grid bounds in {result['seconds']:.2f}s")
    delta=arb('1e-70');radius=arb('1e-80');H=arb('1e56')
    Jfd=arb_mat(3,3)
    for j in range(3):
        fp=[arb(s) for s in results[f'plus{j}']['true_residual_balls']]
        fm=[arb(s) for s in results[f'minus{j}']['true_residual_balls']]
        for i in range(3):Jfd[i,j]=(fp[i]-fm[i])/(2*delta)
    cfg=json.loads((HERE/'refined_candidate.json').read_text())
    rational_B_strings=[[repr(v) for v in row] for row in cfg['Jinv']]
    B=arb_mat([[arb(s) for s in row] for row in rational_B_strings])
    Bnorm=norm_matrix(B)
    need(Bnorm < 2, 'inverse norm budget')
    need(abs(B.det()) > 0, 'rational inverse matrix nonsingular')
    identity=arb_mat([[1 if i==j else 0 for j in range(3)] for i in range(3)])
    defect=norm_matrix(identity-B*Jfd)
    need(defect < arb('1e-9'), 'finite-difference preconditioned defect')
    fd_entry_error=H*delta/2
    q=defect+Bnorm*(3*fd_entry_error+H*radius)
    need(q < arb('1e-8'), 'contraction derivative bound')
    f0=[arb(s) for s in results['center']['true_residual_balls']]
    Bf=B*arb_mat([[s] for s in f0])
    eta=norm_vec([Bf[i,0] for i in range(3)])
    need(eta < arb('1e-90'), 'center displacement bound')
    need(eta+q*radius < radius, 'strict self-map radius inequality')
    # Propagate from the rational center to the exact fixed-point parameter.
    E=arb(60).exp()
    root_state_change=(E+2)*radius
    center_state=[arb(s) for s in results['center']['true_state_balls']]
    moment_root=center_state[6]+arb(0,root_state_change)
    length_root=arb(center[2])+arb(0,radius)
    need(moment_root > arb('3.7'), 'nonzero arclength moment at exact root')
    need(length_root > 0 and length_root < arb('7.5'), 'positive exact-root period')
    centroid_root=moment_root/length_root
    need(centroid_root > arb('.49'), 'positive exact-root centroid')
    # Also show this example is not a one-half-plane migration profile.
    endpoint_x=center_state[0]+arb(0,root_state_change)
    initial_x=arb(center[0])+arb(0,radius)
    need(endpoint_x < arb('-.22') and initial_x > arb('1.3'),
         'expansion center lies between two symmetry-axis points')
    data={
        'status':'ALL ARB CERTIFICATE CHECKS PASSED; analytic proof linkage not Lean-formalized',
        'center':center,
        'center_source_sha256':hashlib.sha256(center_source).hexdigest(),
        'shoot_source_sha256':hashlib.sha256((HERE/'arb_shoot.py').read_bytes()).hexdigest(),
        'harness_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'python_version':sys.version,
        'python_flint_version':flint.__version__,
        'order':ORDER,'nsteps':STEPS,'decimal_precision':DPS,
        'analytic_envelopes':analytic,
        'evaluations':results,
        'finite_difference_step':'1e-70','fixed_point_radius':'1e-80',
        'inverse_matrix_exact_decimal_entries':rational_B_strings,
        'inverse_norm_ball':enc(Bnorm),'inverse_determinant_ball':enc(B.det()),
        'finite_difference_jacobian_balls':[[enc(Jfd[i,j]) for j in range(3)] for i in range(3)],
        'finite_difference_entry_error_bound_ball':enc(fd_entry_error),
        'preconditioned_fd_defect_ball':enc(defect),
        'contraction_bound_ball':enc(q),'center_displacement_ball':enc(eta),
        'self_map_left_hand_side_ball':enc(eta+q*radius),
        'root_moment_ball':enc(moment_root),'root_half_length_ball':enc(length_root),
        'root_centroid_x_ball':enc(centroid_root),
        'root_initial_x_ball':enc(initial_x),'root_endpoint_x_ball':enc(endpoint_x),
        'scope':'Closed expander with nonzero centroid, via the analytic reflection proof. No migration conclusion. No full classification or unrestricted length theorem.',
    }
    output.write_text(json.dumps(data,indent=2),encoding='utf-8')
    log('All contraction, self-map, and centroid checks passed.')
    log('This validates numerical inequalities for the separate analytic existence proof; it is not a full Lean proof.')

if __name__=='__main__':main()
