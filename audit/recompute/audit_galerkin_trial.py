from pathlib import Path
import contextlib,io,json
from fractions import Fraction as F
import even_analytic_bounds as ev
from single_analytic_bounds import tail,qb,rhi,H

def trial_data():
    # Phi has sine coefficient 1 in mode 2; the other Galerkin rows vanish.
    mat=[[ev.sine(2*i,2*j) for i in range(2,19)] for j in range(2,19)]
    rhs=[-ev.sine(2,2*j) for j in range(2,19)]
    pivots=[]
    for k in range(17):
        pivots.append(mat[k][k].upper())
        assert mat[k][k].upper() < -100
        for i in range(k+1,17):
            factor=mat[i][k]/mat[k][k]
            for j in range(k+1,17):mat[i][j]-=factor*mat[k][j]
            rhs[i]-=factor*rhs[k]
            mat[i][k]=ev.I(0)
    cs=[ev.I(0)]*17
    for i in range(16,-1,-1):
        cs[i]=(rhs[i]-sum((mat[i][j]*cs[j] for j in range(i+1,17)),ev.I(0)))/mat[i][i]
    phi=[ev.I(1)]+cs
    norm=ev.sqrt(2*ev.hh0/(5*ev.R))
    es=[2*j*ev.hh(2*j)/norm for j in range(1,19)]
    pair=ev.dot(phi,es);pt=[v/pair for v in phi]
    residual=sum((ev.dot([ev.sine(2*i,2*j)for i in range(1,19)],pt).ab()**2 for j in range(1,41)),F(0))
    residual+=(480*rhi*H*sum(v.ab()for v in pt))**2*qb**(-36)*tail(qb*qb,41,6)
    N=15;en=ev.sqrt(ev.dot(es[:N],es[:N]));e=[v/en for v in es[:N]]
    ppair=ev.dot(pt[:N],e);psi=[v/ppair for v in pt[:N]]
    assert norm.lower()>F(1,2)
    assert all(v.lower()>F(999,1000) for v in (pair,en,ppair))
    z=[v-w for v,w in zip(psi,e)]
    zt=sum((p-ee).ab()**2 for p,ee in zip(pt,es))+(16*rhi/(1-qb*qb))**2*tail(qb*qb,19,4)/norm.lower()**2
    err_e=ev.kernel_tail(N,norm.lower())+(1/en-1).ab()*ev.h4sum(es[:N])
    err_p=sum(pt[j-1].ab()*sum((2*j)**k for k in range(5))for j in range(16,19))+(1/ppair-1).ab()*ev.h4sum(pt[:N])+F(225,10**14)
    env_e=max(e[j-1].ab()/ev.SQRT2.lower()/F(1,10)**(j-3)for j in range(2,N+1))
    env_z=max(z[j-1].ab()/ev.SQRT2.lower()/F(1,10)**(j-3)for j in range(2,N+1))
    values=dict(residual_sq=residual,ztilde_sq=zt,e_error_H4=err_e,psi_error_H4=err_p,e_H4=ev.h4sum(e)+err_e,psi_H4=ev.h4sum(psi)+err_p,zN_sq=sum(v.ab()**2 for v in z),envelope_e=env_e,envelope_z=env_z,pairing_lower=pair.lower(),largest_pivot=max(pivots))
    assert residual<F(2,10**30)
    assert zt<F(1,400)
    assert err_e<F(2,10**12) and err_p<F(6,10**12)
    assert values['e_H4']<200 and values['psi_H4']<200 and values['zN_sq']<F(1,400)
    assert env_e<F(13,1000) and env_z<F(7,1000) and pair.lower()>1
    global trial_values
    trial_values=values
    return e,psi,{k:float(v) for k,v in values.items()}

if __name__=='__main__':
    ev.trial_data=trial_data
    labels,gg,cols,info=ev.prepare()
    weights={s:ev.wbern(s) for s in labels}
    weights.update({str(m):ev.wbern(str(m)) for m in cols})
    a=F(1,10);E=45*rhi*H
    omitted=F(12,5)*E*a**12*(31**2*tail(qb*a,26,1)+62*tail(qb*a,26,2)+tail(qb*a,26,3))
    lower=[]
    for i,label in enumerate(labels):
        rb=ev.bconv([-v.upper()-F(3,5) for v in ev.bern4([gg[k][i][i] for k in range(5)])],weights[label])
        for j,lab in enumerate(labels):
            if i==j:continue
            sub=ev.bconv([v.ab() for v in ev.bern4([gg[k][i][j] for k in range(5)])],weights[lab])
            rb=[x-y for x,y in zip(rb,sub)]
        for m,gc in cols.items():
            sub=ev.bconv([v.ab() for v in ev.bern4([gc[k][i] for k in range(5)])],weights[str(m)])
            rb=[x-y for x,y in zip(rb,sub)]
        scale=F(1) if label in ['e','0','c2'] else a**((abs(int(label))-6)//2)
        row=[(v-omitted)/scale for v in rb]
        assert min(row)>F(1,100),(label,float(min(row)))
        lower.extend(row)
    info.update(even_bernstein_min=float(min(lower)),even_checks=len(lower))
    out={'approximate_summary':info,'rational_trial_bounds':{k:str(v) for k,v in trial_values.items()},'rational_even_min':str(min(lower))}
    Path(__file__).with_name('galerkin_trial_audit.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
    print(json.dumps(info,indent=2))
