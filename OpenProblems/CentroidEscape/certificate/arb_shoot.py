"""High-precision Taylor shooting. Rigorous tail bounds are reported separately.

The polynomial Taylor evaluations enclose all rounding errors through Arb.
Truncation is NOT included in the returned balls unless explicitly inflated.
"""
import sys, json, time, argparse
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'pydeps'))
from flint import arb, arb_poly, arb_mat, ctx

def step(state, h, order):
    p = [arb_poly([v]) for v in state]
    x,y,u,w,k,v,m = p
    for n in range(order):
        nn=n+1
        ku=k*u; kw=k*w; kk=k*k
        cube=kk*k; xw=x*w; yu=y*u
        vals=[u[n],w[n],-kw[n],ku[n],v[n],-cube[n]/2+xw[n]-yu[n],x[n]]
        for pol,c in zip(p,vals): pol[nn]=c/nn
    return [pol(h) for pol in p]

def shoot(a,b,L,order=160,nsteps=750,progress=False):
    h=L/nsteps
    state=[a,arb(0),arb(0),arb(1),b,arb(0),arb(0)]
    bounds=[arb(0) for _ in state]
    for j in range(nsteps):
        for i,s in enumerate(state): bounds[i]=bounds[i].max(abs(s))
        state=step(state,h,order)
        if progress and j%100==99:
            print('step',j+1,'rounding-radius-max',max(float(s.rad()) for s in state),flush=True)
    for i,s in enumerate(state): bounds[i]=bounds[i].max(abs(s))
    return [state[i] for i in [1,2,5]], state, bounds

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--dps',type=int,default=160)
    ap.add_argument('--order',type=int,default=100);ap.add_argument('--steps',type=int,default=375)
    ap.add_argument('--iterations',type=int,default=1);ap.add_argument('--center',default='')
    ap.add_argument('--progress',action='store_true');args=ap.parse_args()
    ctx.dps=args.dps
    cfg=json.loads((Path(__file__).parent/'refined_candidate.json').read_text())
    if args.center:
        center=json.loads(Path(args.center).read_text());p=[arb(t) for t in center['center']]
    else: p=[arb(repr(t)) for t in cfg['p']]
    B=arb_mat([[arb(repr(t)) for t in row] for row in cfg['Jinv']])
    history=[]
    for it in range(args.iterations):
        tic=time.time();f,state,bounds=shoot(*p,order=args.order,nsteps=args.steps,progress=args.progress)
        rec={'iteration':it,'center':[s.mid().str(args.dps, radius=False) for s in p],
             'residual':[s.str(args.dps) for s in f],
             'state':[s.str(args.dps) for s in state],
             'grid_abs_bounds':[float(s.upper()) for s in bounds],
             'seconds':time.time()-tic,'order':args.order,'steps':args.steps,'dps':args.dps}
        history.append(rec); print(json.dumps(rec),flush=True)
        # Chord iteration uses a fixed approximate inverse. Midpoint reset is
        # intentional: every new iterate is an exact dyadic center for a later
        # independent enclosure, not a validated Newton step.
        delta=B*arb_mat([[s] for s in f])
        p=[(s-delta[i,0]).mid() for i,s in enumerate(p)]
        out={'center':[s.str(args.dps,radius=False) for s in p], 'history':history,
             'status':'NUMERICAL CENTER ONLY: truncation bounds not yet applied'}
        (Path(__file__).parent/'arb_center.json').write_text(json.dumps(out,indent=2))

if __name__=='__main__':main()
