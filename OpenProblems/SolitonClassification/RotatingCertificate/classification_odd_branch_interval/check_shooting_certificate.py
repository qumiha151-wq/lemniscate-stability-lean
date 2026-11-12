"""Check the separate analytic metric and Banach-shooting inequalities.

The accompanying AnalyticCertificate.txt supplies the real-analysis proof.
This is a computer-assisted certificate, not a Lean formalization.
"""
from pathlib import Path
import sys,json,hashlib
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[1]/'pydeps'))
from flint import arb,arb_mat,ctx
import flint
import numpy as np
from validated_metric_shoot import need,vmax,matrix_norm

def main():
    ctx.dps=100;enc=lambda x:x.str(100)
    paths=[HERE/f'metric_{s}_o60_n4000.json' for s in ['plus','minus']]
    reports=[json.loads(p.read_text()) for p in paths]
    for rep,sgn in zip(reports,[1,-1]):
        need(rep['complete'] and rep['completed']==4000 and rep['steps']==4000,'both complete trajectories')
        need(rep['sign']==sgn,'positive and negative trajectories')
        need(rep['order']==60 and rep['dps']==100,'frozen order and precision')
        need(arb(rep['grid_K_bound'])<1000,'grid fundamental norm')
        need(arb(rep['grid_I_bound'])<2500,'grid inverse fundamental norm')
        for value,limit in zip(rep['grid_abs_state_bounds'],['8.14','4.125','7.31','7.31','.01']):
            need(arb(value)<arb(limit),'recorded grid-state bound')
        need(abs(arb(rep['step_ball']))<arb('.008'),'recorded time step')
        expected_step=sgn*arb(rep['center_exact_decimal'][2])/4000
        need(arb(rep['step_ball']).contains(expected_step),'stored step encloses signed center length divided by4000')
        need(rep['source_sha256']==hashlib.sha256((HERE/'validated_metric_shoot.py').read_bytes()).hexdigest(),'same integrator source')
    need(reports[0]['center_exact_decimal']==reports[1]['center_exact_decimal'],'same center')
    need(reports[0]['phase_exact_decimal']==reports[1]['phase_exact_decimal'],'same phase')
    K=arb(2000);I=arb(4000);Hfield=arb(4);L=arb(17);A=arb(75);T=arb(32)
    hmax=arb('.008');rbox=arb('1e-32');Rcenter=arb('1e-46')
    field=[arb(36),arb('39.4665625'),arb('72.25'),arb('73.25')]
    margins=[arb('8.5')-arb('8.14'),arb('4.5')-arb('4.125'),arb('8.5')-arb('7.31'),arb('8.5')-arb('7.31')]
    spare=vmax([arb(0)])
    for i in range(4):need(margins[i]-field[i]*hmax>arb('.05'),f'local tube spare {i}')
    need(arb(1000)*(L*hmax).exp()<K,'continuous fundamental norm')
    need(arb(2500)*(L*hmax).exp()<I,'continuous inverse norm')
    # Polynomial coefficient bounds at every outer-tube point.
    jac_v=3*arb('8.5')**2/16+arb(1)/8+arb('.02')/8+arb('8.5')/8
    need(jac_v<17 and 2*arb('8.5')<=17,'weighted Jacobian bound')
    need(3*arb('8.5')/8+arb(1)/4<4,'weighted Hessian bound')
    need(arb('73.25')<75,'weighted field bound')
    need(17<=3*A/10 and 2<=3*A/100 and arb(1)/16<=A/1000,'scalar majorization coefficients')
    metric=[]
    for rep in reports:
        step=abs(arb(rep['step_ball']));ratio=15*step
        tau=10*ratio**61/(1-ratio)
        tauY=ratio**61*(123/(1-ratio)+2*ratio/(1-ratio)**2)
        need(tau<arb('2e-56'),'state tail absolute budget')
        need(tauY<arb('3e-55'),'fundamental tail absolute budget')
        sx=arb(rep['sum_state_rounding'])+4000*arb('2e-56')
        sy=arb(rep['sum_fundamental_rounding'])+4000*1000*arb('3e-55')
        need(arb(rep['sum_state_jump_bound'])<sx,'recorded state jump below independent budget')
        need(arb(rep['sum_fundamental_jump_bound'])<sy,'recorded matrix jump below independent budget')
        sigma=arb(rep['initial_round_bound'])+I*sx;epsilon=I*sy
        C=I*Hfield*K*K/2
        bound=(sigma+T*C*Rcenter**2)*epsilon.exp()
        need(bound<Rcenter,'center metric bootstrap')
        need(K*Rcenter<arb('.001'),'center stays in outer tube')
        gamma=T*I*Hfield*K*K*Rcenter
        D=K*(gamma+epsilon).expm1()
        need(epsilon<arb('.25'),'all jump inverse factors exist')
        # Uniform parameter cube: initial-state map has norm <=1.
        Ru=2*rbox
        need((rbox+sigma+T*C*Ru**2)*epsilon.exp()<Ru,'uniform parameter metric bootstrap')
        gamma_u=T*I*Hfield*K*K*Ru
        need((gamma_u+2*epsilon).exp()<2,'uniform flow and inverse sensitivity bounds')
        need(K*Ru+A*rbox<arb('.001'),'parameter tube and terminal-time extension')
        need((L*rbox).exp()<2,'short terminal-time variational extension')
        metric.append(dict(sign=rep['sign'],sigma=enc(sigma),epsilon=enc(epsilon),
           center_metric_bound=enc(bound),Rcenter=enc(Rcenter),state_endpoint_error=enc(K*Rcenter),
           fundamental_endpoint_error=enc(D),uniform_gamma=enc(gamma_u)))
    Hshoot_formula=16*(T*(4*K)*(4*I)*Hfield*(4*K)**2+2*L*(4*K)+L*A)
    Hshoot=arb('1e20');need(Hshoot_formula<Hshoot,'uniform shooting Hessian budget')
    E=K*Rcenter;D=vmax([arb(m['fundamental_endpoint_error']) for m in metric])
    Jerror=16*D+16*L*E
    endpoints=[[arb(s) for s in rep['endpoint']] for rep in reports]
    Ys=[arb_mat([[arb(s) for s in row] for row in rep['endpoint_fundamental']]) for rep in reports]
    phase=[arb(s) for s in reports[0]['phase_exact_decimal']]
    init=arb_mat(6,5);init[0,0]=1;init[2,1]=1;init[1,3]=phase[0]/8;init[3,3]=phase[1];init[4,4]=1
    need(matrix_norm(init)<=1,'initial data differential norm')
    def field(z):
        k,u,p,q,b,t=z
        return [8*u,-k**3/16-p/8-b*q/8,-k*q,1+k*p,arb(0),k]
    fp,fm=[field(z) for z in endpoints]
    Qrows=[0,1,2,3,5];weights=[1,8,1,1,1]
    Jfull=(Ys[0]-Ys[1])*init
    for i in range(6):Jfull[i,2]=fp[i]+fm[i]
    J=arb_mat([[weights[i]*Jfull[row,j]+arb(0,Jerror) for j in range(5)] for i,row in enumerate(Qrows)])
    pi=arb.pi();f=[]
    for i,row in enumerate(Qrows):
        val=weights[i]*(endpoints[0][row]-endpoints[1][row])
        if row==5:val+=112*pi/57
        f.append(val+arb(0,16*E))
    old=json.loads((HERE.parent/'classification_odd_branch'/'natural_shooting_jacobian.json').read_text())
    Bfloat=np.linalg.inv(np.array(old['unscaled_physical_jacobian']))
    Bstr=[[repr(float(x)) for x in row] for row in Bfloat]
    B=arb_mat([[arb(s) for s in row] for row in Bstr]);Bnorm=matrix_norm(B)
    need(Bnorm<100,'rational inverse norm');need(abs(B.det())>0,'rational inverse nonsingular')
    identity=arb_mat([[int(i==j) for j in range(5)] for i in range(5)])
    defect=matrix_norm(identity-B*J)
    q=defect+Bnorm*Hshoot*rbox
    Bf=B*arb_mat([[x] for x in f]);eta=vmax([abs(Bf[i,0]) for i in range(5)])
    need(q<arb('.01'),'contraction factor below .01')
    need(eta+q*rbox<rbox,'strict self-map')
    center=[arb(s) for s in reports[0]['center_exact_decimal']]
    need(center[4]-rbox>arb('.009'),'strictly nonzero rotation')
    need(center[2]-rbox>31 and center[2]+rbox<32,'half-period between31 and32')
    # A constant-curvature solution has v'=0. Here v'(0) is far from zero.
    z0=[center[0],center[3]*phase[0]/8,center[1],center[3]*phase[1],center[4],arb(0)]
    vprime0=8*field(z0)[1]
    need(vprime0+arb(0,1000*rbox)<-200,'nonconstant curvature near initial point')
    cert=dict(status='ALL INTERVAL INEQUALITIES PASSED; analytic proof in AnalyticCertificate.txt; not Lean formalized',
       center_exact_decimal=reports[0]['center_exact_decimal'],phase_exact_decimal=reports[0]['phase_exact_decimal'],
       parameter_order=['k0','p0','half_length','alpha','b'],box_radius=enc(rbox),
       K=enc(K),I=enc(I),state_Lipschitz=enc(L),state_Hessian=enc(Hfield),field_bound=enc(A),
       metric_checks=metric,shooting_Hessian_formula=enc(Hshoot_formula),shooting_Hessian_budget=enc(Hshoot),
       true_center_residual_balls=[enc(x) for x in f],true_center_Jacobian_balls=[[enc(J[i,j]) for j in range(5)] for i in range(5)],
       pi_ball=enc(pi),inverse_exact_decimal=Bstr,inverse_norm=enc(Bnorm),inverse_det=enc(B.det()),
       preconditioned_defect=enc(defect),contraction_bound=enc(q),center_displacement=enc(eta),
       self_map_lhs=enc(eta+q*rbox),initial_vprime_ball=enc(vprime0+arb(0,1000*rbox)),
       inputs=[dict(name=p.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
       checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       proof_sha256=hashlib.sha256((HERE/'AnalyticCertificate.txt').read_bytes()).hexdigest(),
       python_version=sys.version,python_flint_version=flint.__version__,
       scope='One nonconstant rotating closed similarity profile, conditional only on the accompanying explicit analytic linkage; no complete classification or migration claim')
    (HERE/'shooting_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    print(json.dumps({k:cert[k] for k in ['status','contraction_bound','center_displacement','self_map_lhs','box_radius']},indent=2))
if __name__=='__main__':main()
