"""Exact rational feasibility only; no concrete grid or Lean certificate."""
from fractions import Fraction as F
from pathlib import Path
import json

h=F(1561,200000); mu=F(122,19)
c=[F(1)]
for n in range(60): c.append(c[-1]*mu*F(2*n+1,n+1))
rows=[]
for N in [36,38,40,42,44,46,48,50,60]:
    u=sum(c[n]*h**n for n in range(N+1))
    du=sum(n*c[n]*h**(n-1) for n in range(1,N+1))
    delta=61*u**3-F(19,2)*du
    assert delta>=0
    # Use the actually proved rounded Lean residual budgets where available.
    proved_budgets={42:F(6,10**40),44:F(6,10**42),60:F(1,10**57)}
    delta_bound=proved_budgets.get(N,delta)
    assert delta<=delta_bound
    # Conditional REFERENCE bounds; actual P/Q are derived later.
    K=F(2400); I=F(5000); T=F(64); rho=F(4,10**16)
    SX=F(8000*10**5,10**60); SM=F(1,10**40)
    reset_mult=1/(1-I*SM)
    R=F(1,10**32)
    forcing=I*(2*K*K*R*R+rho*R+delta_bound)
    center_budget=(forcing*T+I*SX)*reset_mult
    center_ok=center_budget<R
    physical_E=K*R
    # Full parameter neighborhood; actual covered time must include its end.
    # ActualRootFromMatrices needs S inside ball(center,Rinit/4).
    # Rinit=8r leaves a strict radius2r domain around the closed radiusr set.
    r=F(1,10**24); Rinit=8*r; neighborhood_R=16*r; Binit=Rinit
    neighborhood_forcing=I*(2*K*K*neighborhood_R**2+rho*neighborhood_R+delta_bound)
    neighborhood_budget=(Binit+neighborhood_forcing*T+I*SX)*reset_mult
    neighborhood_ok=neighborhood_budget<neighborhood_R
    exponent=I*(4*(K*neighborhood_R)*K+rho)*T+I*SM
    relative_error=exponent/(1-exponent)
    multiplier=1/(1-exponent)
    beta=F(100); H=F(10**20); q0=F(1,10**8)
    # 16 covers both physical projections; input norm<=1 remains assumed.
    # Include the terminal post-reset conventions explicitly. The full
    # nonnegative reset sums also bound their respective last jumps.
    terminal_E=physical_E+SX
    eps=16*((K+SM)*relative_error+17*terminal_E)
    q=q0+beta*(eps+H*r)
    eta=16*terminal_E; zeta=F(1,10**38)
    selfmap=zeta+beta*eta+q*r
    rows.append(dict(state_order=N,residual=str(delta),residual_decimal=float(delta),
      residual_budget=str(delta_bound),uses_proved_Lean_residual_budget=N in proved_budgets,
      center_budget_decimal=float(center_budget),center_radius=str(R),center_strict=center_ok,
      neighborhood_budget_decimal=float(neighborhood_budget),neighborhood_strict=neighborhood_ok,
      derived_P_bound=float(K*multiplier),derived_Q_bound=float(I*multiplier),
      contraction=float(q),selfmap_over_radius=float(selfmap/r),
      analytic_budget_feasible_before_numeric_errors=center_ok and neighborhood_ok and q<1 and selfmap<r))
report=dict(scope='Conditional exact Fraction feasibility, not a grid certificate or Lean proof',
 assumptions=['reference K<=2400,I<=5000 on entire extended time grid',
 'matrix residual rho<=4e-16; matrix node norm<=2000 and order22 residual<=2e-19',
 '8000 resets with uniform new state rounding <=1e5/1e60 and total matrix jump<=1e-40',
 'all state centers in innerTube; all actual reference margins hold',
 'shooting input map norm<=1, H<=1e20, preconditioner norm<=100, numerical q0<=1e-8',
 'initial tube radius=8r, metric neighborhood radius=16r; closed radiusr initial set lies in ball(Rinit/4)',
 'independent computed center residual satisfies norm(B*y)<=1e-38',
 'numeric matrix endpoint/rounding error requires additional budget',
 'generic finite scalar residual formula instantiated here only in Fraction, not Lean'],
 rows=rows)
path=Path(__file__).with_name('ReducedStateOrderFeasibility.json')
path.write_text(json.dumps(report,indent=2),encoding='utf-8')
for row in rows:
    print({k:v for k,v in row.items() if k not in ['residual','residual_budget']})
