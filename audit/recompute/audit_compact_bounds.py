from fractions import Fraction as F
from pathlib import Path
import json
import single_analytic_bounds as sp
import odd_analytic_bounds as odd
import even_analytic_bounds as ev

single=[]
for even,sine,bound in [(True,False,-F(21,4)),(False,False,-F(18)),(False,True,-F(11,2))]:
    values=[sp.row(j,even,sine) for j in range(9)]
    assert all(x<bound for x in values)
    single.append({'maximum':str(max(values)),'claimed':str(bound)})
oddvals=[c for n in range(-11,12,2) for c in odd.bernstein(odd.row_polynomial(n))]
assert len(oddvals)==84 and min(oddvals)>F(1,2)
print('27 single-period and 84 odd-sector inequalities passed.',flush=True)

labels,gg,cols,info=ev.prepare()
target=F(3,5); E=45*sp.rhi*sp.H; a=F(1,10)
wbs={s:ev.wbern(s) for s in labels}
for m in cols:wbs[str(m)]=ev.wbern(str(m))
assert all(x>0 for w in wbs.values() for x in w)
omitted=F(12,5)*E*a**12*(31**2*sp.tail(sp.qb*a,26,1)+62*sp.tail(sp.qb*a,26,2)+sp.tail(sp.qb*a,26,3))
evenvals=[]
for i,label in enumerate(labels):
    db=ev.bern4([gg[k][i][i] for k in range(5)])
    rb=ev.bconv([-v.upper()-target for v in db],wbs[label])
    for j,lab in enumerate(labels):
        if i==j:continue
        cb=ev.bern4([gg[k][i][j] for k in range(5)])
        sub=ev.bconv([v.ab() for v in cb],wbs[lab])
        rb=[x-y for x,y in zip(rb,sub)]
    for m,gc in cols.items():
        sub=ev.bconv([v.ab() for v in ev.bern4([gc[k][i] for k in range(5)])],wbs[str(m)])
        rb=[x-y for x,y in zip(rb,sub)]
    scaling=F(1) if label in ['e','0','c2'] else a**((abs(int(label))-6)//2)
    row=[(x-omitted)/scaling for x in rb]
    assert min(row)>F(1,100),(label,min(row))
    evenvals.extend(row)
assert len(evenvals)==217
print('217 even-sector inequalities passed.',flush=True)

z=sp.qb/a; t=sp.qb*a
M=4*sp.moment(t,0)+8*sp.moment(t,1)+5*sp.moment(t,2)+sp.moment(t,3)
def S(v):return v*v*(sp.moment(z,1)+sp.moment(t,1))+2*v*sp.moment(t,2)+sp.moment(t,3)/3
def compact_odd(v):return -4*sp.rlo**2*v**4+(45*sp.rhi+8)*v*v+E*S(v)
def compact_even(n):return -4*sp.rlo**2*(n-F(1,2))**4+45*sp.rhi*(n+F(1,2))**2+5*E*S(n+2)+(n+2)**2
def old_even(n):return -4*sp.rlo**2*(n-F(1,2))**4+45*sp.rhi*(n+F(1,2))**2+(5*E*(sp.moment(z,1)+sp.moment(t,1))+1)*(n+2)**2+10*E*sp.moment(t,2)*(n+2)+F(5,3)*E*sp.moment(t,3)
# Five distinct values establish equality for polynomials of degree at most four.
for n in map(F,range(5)):
    assert compact_odd(n)==odd.high_polynomial(n)
    assert compact_even(n)==old_even(n)
assert E*F(37,16)*sp.qb*F(27,2)*z**6*M<8
assert 5*E*34*z**16*M<1
assert compact_odd(F(25,2))<-3112 and compact_even(F(32))<-481088
print('Common tail functions preserve both original quartic bounds exactly.',flush=True)
record={'single_checks':27,'odd_checks':84,'even_checks':217,
    'single_maxima':single,'odd_min_lower':str(min(oddvals)),
    'even_min_lower':str(min(evenvals)),'odd_min_for_orientation':float(min(oddvals)),
    'even_min_for_orientation':float(min(evenvals)),
    'tail_polynomials_identical':True,'trial_data':info}
Path(__file__).with_name('compact_bounds_audit.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print('All 328 merged finite inequalities passed using rational bounds.',flush=True)
