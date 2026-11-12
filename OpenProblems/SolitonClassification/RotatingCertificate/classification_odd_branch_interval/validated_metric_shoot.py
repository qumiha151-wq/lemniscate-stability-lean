"""Arb polynomial data with explicit, separate analytic Taylor tail budgets.

All resets are recorded as jumps. A later metric proof bounds their effect.
This file alone does not assert an ODE root exists.
"""
from pathlib import Path
import sys,json,time,argparse,hashlib
from decimal import Decimal,localcontext
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[1]/'pydeps'))
from flint import arb,arb_poly,arb_mat,ctx

ROWS=[0,1,2,3,5]
INNER=['8.14','4.125','7.31','7.31','.01']

def need(c,label):
    if not bool(c):raise AssertionError(label)

def vmax(xs):
    out=arb(0)
    for x in xs:out=out.max(x)
    return out

def matrix_norm(A):
    return vmax([sum((abs(A[i,j]) for j in range(A.ncols())),arb(0)) for i in range(A.nrows())])

def full_matrix(sens):
    Y=arb_mat(6,6)
    for i,row in enumerate(ROWS):
        for j in range(5):Y[row,j]=sens[i][j]
    Y[4,4]=1;Y[5,5]=1
    return Y

def step(state,sens,h,order):
    polys=[arb_poly([x]) for x in state]
    S=[[arb_poly([sens[i][j]]) for j in range(5)] for i in range(5)]
    k,u,p,q,b,theta=polys
    bval=state[4]
    for n in range(order):
        k2=k*k;k3=k2*k;kq=k*q;kp=k*p
        coeff=[8*u[n],-k3[n]/16-p[n]/8-bval*q[n]/8,-kq[n],kp[n]+(1 if n==0 else 0),arb(0),k[n]]
        for poly,c in zip(polys,coeff):poly[n+1]=c/(n+1)
        for j in range(5):
            sk,su,sp,sq,st=[S[i][j] for i in range(5)]
            vals=[8*su[n],-3*(k2*sk)[n]/16-sp[n]/8-bval*sq[n]/8-(q[n]/8 if j==4 else 0),
                  -(q*sk)[n]-(k*sq)[n],(p*sk)[n]+(k*sp)[n],sk[n]]
            for i,c in enumerate(vals):S[i][j][n+1]=c/(n+1)
    out=[poly(h) for poly in polys]
    Sout=[[poly(h) for poly in row] for row in S]
    xround=vmax([x.rad() for x in out])
    Yround=vmax([sum((x.rad() for x in row),arb(0)) for row in Sout])
    return [x.mid() for x in out],[[x.mid() for x in row] for row in Sout],xround,Yround

def center_data():
    source=HERE.parent/'classification_odd_branch'/'arb_rotating_o55_n1800.json'
    r=json.loads(source.read_text());k,p,l,rho,b=r['center']
    # Keep the phase line exactly as frozen in the candidate report.
    e=['-0.05995393111634394','-0.9982011451324311']
    with localcontext() as c:
        c.prec=250;alpha=str(Decimal(rho)*Decimal(b))
    return [k,p,l,alpha,b],e,hashlib.sha256(source.read_bytes()).hexdigest()

def evaluate(sign,order=60,steps=4000,dps=100,limit=None):
    ctx.dps=dps;pstr,estr,source_hash=center_data();k,p,l,alpha,b=[arb(s) for s in pstr]
    e=[arb(s) for s in estr];raw=[k,alpha*e[0]/8,p,alpha*e[1],b,arb(0)]
    state=[x.mid() for x in raw];initial_round=vmax([x.rad() for x in raw])
    sens=[[arb(int(ROWS[i]==j)) for j in range(5)] for i in range(5)]
    h=sign*l/steps;need(abs(h)<arb('.008'),'step below .008')
    r=15*abs(h)
    tau=10*r**(order+1)/(1-r)
    tauY=r**(order+1)*((2*order+3)/(1-r)+2*r/(1-r)**2)
    sum_x_round=arb(0);sum_Y_round=arb(0);sum_x_jump=arb(0);sum_Y_jump=arb(0)
    maxK=arb(0);maxI=arb(0);bounds=[arb(0) for _ in state];tic=time.monotonic();checkpoints=[]
    n=steps if limit is None else min(limit,steps)
    for j in range(n+1):
        for i in range(5):
            bounds[i]=bounds[i].max(abs(state[i]));need(abs(state[i])<arb(INNER[i]),f'grid state {j}:{i}')
        bounds[5]=bounds[5].max(abs(state[5]))
        Y=full_matrix(sens);K=matrix_norm(Y);I=matrix_norm(Y.inv())
        need(K<1000,f'grid Y bound {j}');need(I<2500,f'grid inverse Y bound {j}')
        maxK=maxK.max(K);maxI=maxI.max(I)
        if j==n:break
        state,sens,xround,Yround=step(state,sens,h,order)
        sum_x_round+=xround;sum_Y_round+=Yround
        sum_x_jump+=xround+tau;sum_Y_jump+=Yround+K*tauY
        if (j+1)%200==0 or j+1==n:
            checkpoint=dict(completed=j+1,seconds=time.monotonic()-tic,
              grid_K_upper=str(float(maxK.upper())),grid_I_upper=str(float(maxI.upper())))
            checkpoints.append(checkpoint);print(json.dumps({'sign':sign,**checkpoint}),flush=True)
    enc=lambda x:x.str(dps)
    report=dict(status='GRID DATA VERIFIED; global analytic and root checks still required',
       complete=bool(n==steps),sign=sign,order=order,steps=steps,completed=n,dps=dps,
       center_exact_decimal=pstr,phase_exact_decimal=estr,center_source_sha256=source_hash,
       initial_round_bound=enc(initial_round),step_ball=enc(h),state_tail_per_step=enc(tau),
       fundamental_tail_factor_per_step=enc(tauY),sum_state_rounding=enc(sum_x_round),
       sum_fundamental_rounding=enc(sum_Y_round),sum_state_jump_bound=enc(sum_x_jump),
       sum_fundamental_jump_bound=enc(sum_Y_jump),grid_K_bound=enc(maxK),grid_I_bound=enc(maxI),
       grid_abs_state_bounds=[enc(x) for x in bounds],endpoint=[enc(x) for x in state],
       endpoint_fundamental=[[enc(Y[i,j]) for j in range(6)] for i in range(6)],
       seconds=time.monotonic()-tic,checkpoints=checkpoints,
       source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    return report

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--sign',type=int,default=1,choices=[-1,1])
    ap.add_argument('--order',type=int,default=60);ap.add_argument('--steps',type=int,default=4000)
    ap.add_argument('--dps',type=int,default=100);ap.add_argument('--limit',type=int)
    args=ap.parse_args();result=evaluate(args.sign,args.order,args.steps,args.dps,args.limit)
    name=f'metric_{"plus" if args.sign>0 else "minus"}_o{args.order}_n{args.steps}'
    if args.limit:name+=f'_pilot{args.limit}'
    (HERE/(name+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'complete':result['complete'],'seconds':result['seconds'],
      'sum_state_jump_bound':result['sum_state_jump_bound'],'sum_fundamental_jump_bound':result['sum_fundamental_jump_bound']}),flush=True)
if __name__=='__main__':main()
