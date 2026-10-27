"""Write explicit rational input and every finite comparison into the paper.
All decisions and inequalities below use Fraction / outward rational intervals.
The LaTeX tables, rather than this authoring program, are the proof data.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import json, sys
import single_analytic_bounds as sp
import odd_analytic_bounds as odd
import even_analytic_bounds as ev
sys.stdout.reconfigure(encoding='utf-8')
root=Path(__file__).resolve().parents[1]
freeze=Path(__file__).with_name('expanded_rational_trial.json')
frozen=json.loads(freeze.read_text())
# Scalar input from the current revised manuscript, whose nome bound is proved in Lean.
ev.DEN=10**30
ev.SQRT2=ev.sqrt(ev.I(2))
ev.pi=ev.I(F('3.14159265358979323846'),F('3.14159265358979323847'))
ev.Q=ev.I(F('0.043213918263772249774'),F('0.043213918263772249775'))
theta_three=1+2*sum((ev.Q**(j*j) for j in range(1,4)),ev.I(0))
theta_three+=ev.I(0,(2*ev.Q**16/(1-ev.Q**9)).upper())
ev.theta=ev.I(F(1086434811213308014574,10**21),F(1086434811213308014577,10**21))
assert ev.theta.lower()<=theta_three.lower() and theta_three.upper()<=ev.theta.upper()
ev.R=ev.I(F(717770011046129997816,10**21),F(717770011046129997825,10**21))
theta_reciprocal=ev.theta**-4
assert ev.R.lower()<=theta_reciprocal.lower() and theta_reciprocal.upper()<=ev.R.upper()
ev.hh0=1-sum((16*ev.R*j*ev.Q**j/(1-ev.Q**(2*j)) for j in range(1,41)),ev.I(0))
ev.hh0-=ev.I(0,16*sp.rhi/(1-sp.qb*sp.qb)*sp.tail(sp.qb,41,1))
ev.hh.cache_clear()
phi=[ev.I(F(n,frozen['denominator'])) for n in frozen['numerators']]
data={}
def trial():
    norm=ev.sqrt(2*ev.hh0/(5*ev.R))
    es=[2*j*ev.hh(2*j)/norm for j in range(1,19)]
    pair=ev.dot(phi,es); pt=[v/pair for v in phi]
    rawres=[ev.dot([ev.sine(2*i,2*j) for i in range(1,19)],pt) for j in range(1,41)]
    head=sum((u.ab()**2 for u in rawres),F(0))
    tail=(480*sp.rhi*sp.H*sum(v.ab() for v in pt))**2*sp.qb**(-36)*sp.tail(sp.qb**2,41,6)
    te=ev.sqrt(ev.dot(es[:15],es[:15])); e=[v/te for v in es[:15]]
    tp=ev.dot(pt[:15],e); psi=[v/tp for v in pt[:15]]
    z=[p-q for p,q in zip(psi,e)]
    eta_e_tail=ev.kernel_tail(15,norm.lower())
    eta_e_norm=(1/te-1).ab()*ev.h4sum(es[:15])
    eta_p_tail=sum(pt[j-1].ab()*sum((2*j)**k for k in range(5)) for j in range(16,19))
    eta_p_norm=(1/tp-1).ab()*ev.h4sum(pt[:15])
    eta_p_res=F(177,10**14)
    vals={'residual_head':head,'residual_tail':tail,'residual_sq':head+tail,
      'eta_e_tail':eta_e_tail,'eta_e_norm':eta_e_norm,'eta_e':eta_e_tail+eta_e_norm,
      'eta_p_tail':eta_p_tail,'eta_p_norm':eta_p_norm,'eta_p_res':eta_p_res,
      'eta_p':eta_p_tail+eta_p_norm+eta_p_res,
      'e_H4':ev.h4sum(e)+eta_e_tail+eta_e_norm,
      'psi_H4':ev.h4sum(psi)+eta_p_tail+eta_p_norm+eta_p_res,
      'zN_sq':sum(v.ab()**2 for v in z),
      'envelope_e':max(e[j-1].ab()/ev.SQRT2.lower()/F(1,10)**(j-3) for j in range(2,16)),
      'envelope_z':max(z[j-1].ab()/ev.SQRT2.lower()/F(1,10)**(j-3) for j in range(2,16))}
    assert vals['residual_sq']<F(2,10**30)
    assert vals['eta_e']<F(2,10**12) and vals['eta_p']<F(6,10**12)
    assert vals['e_H4']<200 and vals['psi_H4']<200
    assert vals['zN_sq']<F(1,400)
    assert vals['envelope_e']<F(13,1000) and vals['envelope_z']<F(7,1000)
    assert all(x.lower()>F(999,1000) for x in (pair,te,tp))
    data.update(norm=norm,pair=pair,te=te,tp=tp,es=es,pt=pt,e=e,psi=psi,z=z,res=rawres,vals=vals)
    return e,psi,{k:float(v) for k,v in vals.items()}
ev.trial_data=trial
labels,gg,cols,info=ev.prepare()
def floor(x,scale): return (x*scale).numerator//(x*scale).denominator
def ceil(x,scale): return -floor(-x,scale)
def fixed(x,digits=3,upper=False):
    n=ceil(x,10**digits) if upper else floor(x,10**digits)
    s='-' if n<0 else ''; n=abs(n)
    return s+str(n//10**digits)+'.'+str(n%10**digits).zfill(digits)
def sci(x,upper=True,digits=5):
    x=F(x)
    if x==0:return '0'
    if x<0:return '-'+sci(-x,not upper,digits)
    power=0
    while x>=10:x/=10;power+=1
    while x<1:x*=10;power-=1
    s=fixed(x,digits,upper)
    return s+(r'\cdot10^{'+str(power)+'}' if power else '')
def longtable(spec,caption,label,head,rows,size='small'):
    return '\n{\\'+size+'\n\\setlength{\\tabcolsep}{3pt}\n\\begin{longtable}{'+spec+'}\n'+r'\caption{'+caption+r'}\label{'+label+r'}\\'+'\n'+r'\toprule '+head+r'\\ \midrule'+'\n'+r'\endfirsthead'+'\n'+r'\toprule '+head+r'\\ \midrule'+'\n'+r'\endhead'+'\n'+r'\bottomrule\endfoot'+'\n'+'\n'.join(rows)+'\n\\end{longtable}\n}\n'
def row(cells):return ' & '.join(cells)+r'\\'

out=r'''\section{Expanded finite rational comparisons}\label{app:expanded-data}
This appendix specifies the trial vector by integers and displays each finite
comparison used in the proof. Every terminating decimal in a bound is an exact
rational number. Lower bounds are rounded toward $-\infty$ and upper bounds
toward $+\infty$; none is a floating-point estimate of a spectral value.

\subsection{Arithmetic conventions and fixed trial coefficients}
Use the interval operations of Appendix~\ref{app:arithmetic}. For definiteness,
after each elementary operation one may enlarge $[u,v]$ to
\[
 [10^{-30}\lfloor10^{30}u\rfloor,
  -10^{-30}\lfloor-10^{30}v\rfloor].
\]
For square roots use \eqref{eq:sqrt-envelope}. Inverse powers are evaluated by
reciprocal and multiplication. This convention enlarges, and never narrows,
the exact rational enclosures. It fixes all endpoints in the tables below.
Products of a scalar polynomial and an interval are evaluated coefficientwise.
All comparisons reduce to multiplication of positive integer denominators.

The trial vector in \eqref{eq:adjoint-trial} is defined directly by
$t_i=N_i/10^{30}$, where all $N_i$ are listed in
Table~\ref{tab:trial-integers}. No linear solve is part of this definition.
'''
out+=longtable('rr','Exact integers defining the 18-mode trial.','tab:trial-integers',r'$i$ & $N_i$', [row([str(i),str(n)]) for i,n in enumerate(frozen['numerators'],1)])
out+=r'''
The normalization is also completely specified by
\[
 b_i=2ih_{2i},\quad \mathfrak n=(2h_0/(5r))^{1/2},\quad
 c_\Phi=\frac{\sum_{i=1}^{18}N_ib_i}{10^{30}\mathfrak n},\quad
 p_i=\frac{N_i}{10^{30}c_\Phi}.
\]
In particular only a positive scalar division is required. The input intervals
and normalization factors are displayed next; their construction is
\eqref{eq:fine-Q}--\eqref{eq:fine-input}.
'''
inputs=[(r'\pi',ev.pi),(r'Q',ev.Q),(r'\theta_3(0,Q)',ev.theta),(r'r',ev.R),(r'h_0',ev.hh0),(r'\sqrt2',ev.SQRT2),(r'\mathfrak n',data['norm']),(r'c_\Phi',data['pair']),(r't_e',data['te']),(r't_p',data['tp'])]
out+=longtable('lrr','Outward rational input and normalization bounds.','tab:input-bounds',r'Quantity & Lower bound & Upper bound',[row(['$'+n+'$','$'+fixed(x.lower(),24)+'$','$'+fixed(x.upper(),24,True)+'$']) for n,x in inputs],size='footnotesize')
out+=r'''
\subsection{Single-period rows and scalar tail checks}
For each row in Table~\ref{tab:single-complete}, let
\[
 D_j=s^+_{2j,2j},\quad
 H_j=\sum_{\substack{0\le k<20\\k\ne j}}
 b_{2j,2k}d_k/d_j,\quad T_j=R_j-D_j-H_j.
\]
The columns give outward bounds on these three explicitly defined rational
terms and on their sum. Thus each of the nine comparisons in
\eqref{eq:single-uniform} is displayed separately.
'''
single_rows=[]
for j in range(9):
    n=2*j;D=sp.s(n,n)[1];HH=sum(sp.ab(sp.s(n,2*k))*sp.weights(k,True)/sp.weights(j,True) for k in range(20) if k!=j)
    RR=sp.row(j,True);TT=RR-D-HH
    assert RR<-F(21,4)
    single_rows.append(row([str(j),fixed(D,3,True),fixed(HH,3,True),'$'+sci(TT)+'$',fixed(RR,3,True)]))
out+=longtable('rrrrr','The nine cosine rows; each final upper bound is less than $-21/4$.','tab:single-complete',r'$j$ & $D_j\le$ & $H_j\le$ & $T_j\le$ & $R_j\le$',single_rows)
scalar={}
scalar[r'\rho^2']=(sp.moment(sp.qhi**2,4)-sp.qhi**2)/sp.qhi**2
scalar[r'S^s_{2,2}']=sp.s(2,2,True)[1]
scalar[r'b_{2,4}^2']=sp.ab(sp.s(2,4,True))**2
scalar[r'b_{2,6}^2']=sp.ab(sp.s(2,6,True))**2
scalar[r'\text{coupling tail}']=sp.C**2*sum(F(comb(4,k))*2**(4-k)*sp.tail(sp.qb**2,3,k+2) for k in range(5))
scalar[r'\|B\|^2\text{ upper bound}']=sum(scalar[k] for k in [r'b_{2,4}^2',r'b_{2,6}^2',r'\text{coupling tail}'])
for n in [4,6]:
    scalar[r'\text{sine row }'+str(n)]=sp.s(n,n,True)[1]+sum(sp.ab(sp.s(n,2*k,True)) for k in range(2,8) if 2*k!=n)+sp.C*(n*n*sp.tail(sp.qb,8-n//2,1)+2*n*sp.tail(sp.qb,8-n//2,2)+sp.tail(sp.qb,8-n//2,3))
a=F(1,10);E=45*sp.rhi*sp.H;z=sp.qb/a;t=sp.qb*a
mc=4*sp.moment(t,0)+8*sp.moment(t,1)+5*sp.moment(t,2)+sp.moment(t,3)
for aa,n,name in [(a,F(18),'P_{1/10}'),(F(1),F(8),'P_1')]:
    cc=45*sp.rhi+sp.C*(sp.moment(sp.qb/aa,1)+sp.moment(sp.qb*aa,1))
    dd=2*sp.C*sp.moment(sp.qb*aa,2)
    scalar[name+'('+str(n)+')']=sp.poly(n,aa)
    scalar[name+"'("+str(n)+')']=-16*sp.rlo**2*n**3+2*cc*n+dd
    scalar[name+"''("+str(n)+')']=-48*sp.rlo**2*n**2+2*cc
v=F(25,2);co=45*sp.rhi+8+E*(sp.moment(z,1)+sp.moment(t,1))
scalar[r'\mathcal P_{\rm o}(25/2)']=odd.high_polynomial(v)
scalar[r"\mathcal P_{\rm o}'(25/2)"]=-16*sp.rlo**2*v**3+2*co*v+2*E*sp.moment(t,2)
scalar[r"\mathcal P_{\rm o}''(25/2)"]=-48*sp.rlo**2*v**2+2*co
scalar[r'E_*(37/16)\bar Q(27/2)z^6\mathfrak C']=E*F(37,16)*sp.qb*F(27,2)*z**6*mc
scalar[r'5E_*34z^{16}\mathfrak C']=5*E*34*z**16*mc
n=F(32);cc=5*E*(sp.moment(z,1)+sp.moment(t,1))+1
scalar[r'\mathcal P_{\rm e}(32)']=-4*sp.rlo**2*(n-F(1,2))**4+45*sp.rhi*(n+F(1,2))**2+cc*(n+2)**2+10*E*sp.moment(t,2)*(n+2)+F(5,3)*E*sp.moment(t,3)
scalar[r"\mathcal P_{\rm e}'(32)"]=-16*sp.rlo**2*(n-F(1,2))**3+90*sp.rhi*(n+F(1,2))+2*cc*(n+2)+10*E*sp.moment(t,2)
scalar[r"\mathcal P_{\rm e}''(32)"]=-48*sp.rlo**2*(n-F(1,2))**2+90*sp.rhi+2*cc
out+=longtable('lr','Separate rational upper bounds for coupling and every high-row starting check.','tab:scalar-complete',r'Expression & Upper bound',[row(['$'+k+'$','$'+fixed(v,6,True)+'$']) for k,v in scalar.items()])
out+=r'''
\subsection{All odd-sector Bernstein comparisons}
For a transparent coefficient-by-coefficient evaluation of $F_n$, write
$d_n=\sum_{q=0}^2d_{nq}\alpha^q$ and
$V_{nm}=\sum_{p=0}^2v_{nmp}\alpha^p$, filling missing coefficients by zero.
Set
\begin{align*}
 a_{n0}&=4r_-^2n^4-45r_+U_0n^2+41,&
 a_{n1}&=16r_-^2n^3-90r_+U_0n,\\
 a_{n2}&=24r_-^2n^2-45r_+U_0,&
 a_{n3}&=16r_-^2n,&a_{n4}&=4r_-^2.
\end{align*}
Then, for $0\le l\le6$,
\[
 f_{nl}=\sum_{p+q=l}a_{np}d_{nq}
 -r_+\sum_{\substack{|m|\le25\\m\ {\rm odd},\ m\ne n}}
 U_{|n-m|/2}\sum_{p+q=l}v_{nmp}d_{mq}
 -\delta_{l0}R_n^{\rm o},
 \qquad F_n=\sum_{l=0}^6f_{nl}\alpha^l.
\]
The seven conversions, written without a suppressed coefficient transform, are
\[
\begin{aligned}
 b_0={}&f_0,\quad b_1=f_0+f_1/12,\quad
 b_2=f_0+f_1/6+f_2/60,\\
 b_3={}&f_0+f_1/4+f_2/20+f_3/160,\\
 b_4={}&f_0+f_1/3+f_2/10+f_3/40+f_4/240,\\
 b_5={}&f_0+5f_1/12+f_2/6+f_3/16+f_4/48+f_5/192,\\
 b_6={}&f_0+f_1/2+f_2/4+f_3/8+f_4/16+f_5/32+f_6/64.
\end{aligned}
\]
Here $b_k=[F_n]_{6,k}$ and $f_l=f_{nl}$ for the row under consideration.
Table~\ref{tab:odd-all} lists all 84 lower bounds; the final column lists the
12 additional zero-parameter comparisons. Each of the first seven columns is
greater than $1/2$, and each entry in the last is greater than $5$.
'''
oddrows=[];oddvalues=[]
for n in range(-11,12,2):
    poly=odd.row_polynomial(n);bb=odd.bernstein(poly);zz=poly[0]/odd.weight(n)[0]
    assert min(bb)>F(1,2) and zz>5
    oddvalues+=bb
    oddrows.append(row([str(n)]+[fixed(x) for x in bb]+[fixed(zz)]))
out+=longtable('r'+'r'*8,'All odd-sector comparisons in (4.12).','tab:odd-all',r'$n$ & $b_0\ge$ & $b_1\ge$ & $b_2\ge$ & $b_3\ge$ & $b_4\ge$ & $b_5\ge$ & $b_6\ge$ & $F_n(0)/d_n(0)\ge$',oddrows,'scriptsize')
out+=r'''
\subsection{Every residual coefficient and the vector-error sums}
Put $t_j=0$ for $j>18$. Before normalization, each residual coefficient is
\begin{equation}\label{eq:raw-residual-expanded}
 \mathfrak r_j=30r\sum_{i=1}^{18} i t_i
 \big[(7j-i)h_{2|i-j|}+(7j+i)h_{2(i+j)}\big]
 -(64r^2j^4+42)t_j.
\end{equation}
Thus $u_j$ bounds $|\mathfrak r_j/c_\Phi|$, not the sum of the absolute values
of its individual summands: the signed sum is formed before taking its
interval absolute value. The table gives $u_j\le U_j^{\rm res}$ for every
$1\le j\le40$. Its entries can be substituted directly in the squared sum.
'''
resrows=[];resceil=[]
for j,u in enumerate(data['res'],1):
    # Uniform denominator permits an explicit integer sum-of-squares check.
    num=ceil(u.ab(),10**35);resceil.append(num)
    resrows.append(row([str(j),str(num),str(num*num)]))
out+=longtable('rrr',r'Residual bounds $u_j\le m_j10^{-35}$ and their integer squares.','tab:residual-all',r'$j$ & $m_j$ & $m_j^2$',resrows,'footnotesize')
resnumer=sum(x*x for x in resceil)
tailceil=ceil(data['vals']['residual_tail'],10**70)
assert F(resnumer+tailceil,10**70)<F(2,10**30)
out+=r'Consequently the complete residual comparison is the integer inequality'+'\n'+r'\begin{align*}'+'\n'+r' 10^{30}\|A_0^*\widetilde\psi\|^2&\le '+str(resnumer)+r'\\'+'\n'+r' &\quad+'+str(tailceil)+r'\\'+'\n'+r' &='+str(resnumer+tailceil)+r'<2\cdot10^{40}.'+'\n'+r'\end{align*}'+'\n'
out+=r'''
This includes the whole $j\ge41$ tail from \eqref{eq:residual-finite}; the
comparison proves both \eqref{eq:adjoint-data} and \eqref{eq:residual-finite}.
For the vector estimates, set $W_i=1+2i+(2i)^2+(2i)^3+(2i)^4$.
The following table displays every finite summand required by
\eqref{eq:vector-scalar-checks}. All columns are upper bounds. The last two
columns are needed only for $i\ge2$.
'''
vectorrows=[]
for i in range(1,16):
    ee=data['e'][i-1]; pp=data['psi'][i-1];zz=data['z'][i-1];wi=sum((2*i)**k for k in range(5))
    vectorrows.append(row([str(i),fixed(wi*ee.ab(),8,True),fixed(wi*pp.ab(),8,True),fixed(zz.ab()**2,12,True),fixed(ee.ab()/ev.SQRT2.lower()/a**(i-3),8,True) if i>=2 else '--',fixed(zz.ab()/ev.SQRT2.lower()/a**(i-3),8,True) if i>=2 else '--']))
out+=longtable('r'+'r'*5,'All finite vector summands and individual envelope ratios.','tab:vector-all',r'$i$ & $W_i|E_i|$ & $W_i|\Psi_i|$ & $|Z_i|^2$ & $|E_i|/(\sqrt2 a^{i-3})$ & $|Z_i|/(\sqrt2 a^{i-3})$',vectorrows,'scriptsize')
names={
'eta_e_tail':r'\eta_e:\ \text{kernel tail}', 'eta_e_norm':r'\eta_e:\ \text{normalization}', 'eta_e':r'\eta_e',
'eta_p_tail':r'\eta_p:\ i=16,17,18', 'eta_p_norm':r'\eta_p:\ \text{normalization}', 'eta_p_res':r'\eta_p:\ \text{adjoint error}', 'eta_p':r'\eta_p',
'e_H4':r'L_4(E)+\eta_e','psi_H4':r'L_4(\Psi)+\eta_p','zN_sq':r'\sum_i|Z_i|^2','envelope_e':r'\max |E_i|/(\sqrt2_-a^{i-3})','envelope_z':r'\max |Z_i|/(\sqrt2_-a^{i-3})'}
out+=longtable('lr','Separate summands, totals and envelope maxima for (A.8).','tab:vector-totals',r'Expression & Rational upper bound',[row(['$'+names[k]+'$','$'+sci(data['vals'][k],digits=7)+'$']) for k in names])

# Sum the displayed bounds themselves, so the reader can check the final
# vector inequalities using the printed table without unprinted digits.
se=sum(ceil(sum((2*i)**k for k in range(5))*data['e'][i-1].ab(),10**8) for i in range(1,16))
spv=sum(ceil(sum((2*i)**k for k in range(5))*data['psi'][i-1].ab(),10**8) for i in range(1,16))
sz=sum(ceil(x.ab()**2,10**12) for x in data['z'])
assert sz<10**12//400
assert F(se,10**8)+F(2,10**12)<200 and F(spv,10**8)+F(6,10**12)<200
out+=r'The sums of the printed upper bounds, including their outward rounding, are'+'\n'+r'\['+'\n'
out+=r'L_4(E)\le\frac{'+str(se)+r'}{10^8},\qquad L_4(\Psi)\le\frac{'+str(spv)+r'}{10^8},\qquad \sum_i|Z_i|^2\le\frac{'+str(sz)+r'}{10^{12}}<\frac1{400}.'+'\n'+r'\]'+'\n'
out+=r'The last comparison is the integer inequality $'+str(sz)+r'<2500000000$. For the two normalization errors one may use the simpler rational bounds $\eta_e^{\rm norm}<3\cdot10^{-28}$ and $\eta_p^{\rm norm}<7\cdot10^{-28}$. Hence'+'\n'+r'\['+'\n'+r'\eta_e<1.3309802\cdot10^{-12}+3\cdot10^{-28}<2\cdot10^{-12},'+'\n'+r'\]'+'\n'+r'\['+'\n'+r'\eta_p<2.8858093\cdot10^{-12}+7\cdot10^{-28}+2.25\cdot10^{-12}<6\cdot10^{-12}.'+'\n'+r'\]'+'\n'
out+=r'The discarded-mode contribution in the second inequality has the separate bounds'+'\n'+r'\['+'\n'
out+=r'\begin{array}{c|ccc}i&16&17&18\\\hline W_i p_i^+\le&'+'&'.join(sci(data['pt'][i-1].ab()*sum((2*i)**k for k in range(5)),digits=7) for i in range(16,19))+r'\end{array}'+'\n'+r'\]'+'\n'
out+=r'Adding the two error bounds to the displayed $L_4$ sums gives the bounds $200$ in \eqref{eq:vector-scalar-checks}. The last two columns of Table~\ref{tab:vector-all} separately lie below $13/1000$ and $7/1000$, proving both envelope comparisons.'+'\n'

out+=r'''
\subsection{All even-sector Bernstein rows with their arithmetic components}
The formulas in Appendix~\ref{app:arithmetic} determine $g_{ij,l}$, without
any unspecified matrix. To spell out their polynomial conversion, for each
entry with power coefficients $g_0,\ldots,g_4$ use
\[
 \beta_0=g_0,\quad \beta_1=g_0+g_1/8,\quad
 \beta_2=g_0+g_1/4+g_2/24,\quad
 \beta_3=g_0+3g_1/8+g_2/8+g_3/32,
\]
\[
 \beta_4=g_0+g_1/2+g_2/4+g_3/8+g_4/16.
\]
For $d_i=d_{i0}+d_{i1}\alpha+d_{i2}\alpha^2$, its three coefficients are
$D_{i,0}=d_{i0}$, $D_{i,1}=d_{i0}+d_{i1}/4$,
$D_{i,2}=d_{i0}+d_{i1}/2+d_{i2}/4$.
Define normalized arithmetic components
\begin{align*}
 \mathsf D_{ik}&=s_i^{-1}\sum_{p+q=k}
 \frac{\binom4p\binom2q}{\binom6k}(-\beta^+_{ii,p}-3/5)D_{i,q},\\
 \mathsf H_{ik}&=s_i^{-1}\sum_{p+q=k}
 \frac{\binom4p\binom2q}{\binom6k}
 \sum_{\substack{j\in\mathcal J_{30}\\j\ne i}}B_{ij,p}D_{j,q},\\
 \mathsf O_{ik}&=s_i^{-1}\sum_{p+q=k}
 \frac{\binom4p\binom2q}{\binom6k}
 \sum_{\substack{32\le|m|\le80\\m\ {\rm even}}}B_{im,p}D_{m,q}.
\end{align*}
Then $C_{ik}/s_i=\mathsf D_{ik}-\mathsf H_{ik}-\mathsf O_{ik}-R^{\rm e}/s_i$.
In Table~\ref{tab:even-components}, the displayed integers are
\[
 d_{ik}=\lfloor10^6\mathsf D_{ik}\rfloor,\quad
 h_{ik}=\lceil10^6\mathsf H_{ik}\rceil,\quad
 o_{ik}=\lceil10^6\mathsf O_{ik}\rceil.
\]
The ceiling is $\lceil x\rceil=-\lfloor-x\rfloor$. Since
$R^{\rm e}<3\cdot10^{-66}$ and $s_i\ge10^{-12}$,
$10^6R^{\rm e}/s_i<1$. The last integer in every row is
\[
 m_{ik}=d_{ik}-h_{ik}-o_{ik}-1>10000.
\]
It follows, by the displayed integer subtraction in every row, that
$C_{ik}/s_i>m_{ik}/10^6>1/100$. This lists all 217 comparisons in
\eqref{eq:even-uniform}, including their head, external-column and infinite-tail
contributions, rather than just their common minimum.
'''
weights={lab:ev.wbern(lab) for lab in labels}
weights.update({str(m):ev.wbern(str(m)) for m in cols})
evenrows=[];evenrecords=[]
omitted=F(12,5)*E*a**12*(31**2*sp.tail(t,26,1)+62*sp.tail(t,26,2)+sp.tail(t,26,3))
assert omitted<F(3,10**66)
for i,lab in enumerate(labels):
    D=ev.bconv([-v.upper()-F(3,5) for v in ev.bern4([gg[k][i][i] for k in range(5)])],weights[lab])
    HH=[F(0)]*7;OO=[F(0)]*7
    for j,labj in enumerate(labels):
        if i==j:continue
        term=ev.bconv([v.ab() for v in ev.bern4([gg[k][i][j] for k in range(5)])],weights[labj])
        HH=[x+y for x,y in zip(HH,term)]
    for m,coeffs in cols.items():
        term=ev.bconv([v.ab() for v in ev.bern4([coeffs[k][i] for k in range(5)])],weights[str(m)])
        OO=[x+y for x,y in zip(OO,term)]
    scale=F(1) if lab in ['e','0','c2'] else a**((abs(int(lab))-6)//2)
    for k in range(7):
        d=floor(D[k]/scale,10**6);h=ceil(HH[k]/scale,10**6);o=ceil(OO[k]/scale,10**6)
        margin=d-h-o-1
        assert margin>10000 and (D[k]-HH[k]-OO[k]-omitted)/scale>F(margin,10**6)
        labtex=r'\mathrm e' if lab=='e' else (r'\mathrm c' if lab=='c2' else lab)
        evenrows.append(row(['$'+labtex+'$',str(k),str(d),str(h),str(o),str(margin)]))
        evenrecords.append({'i':lab,'k':k,'d':d,'h':h,'o':o,'margin':margin})
out+=longtable('rrrrrr','All 217 integer subtractions: $d_{ik}-h_{ik}-o_{ik}-1=m_{ik}>10000$.','tab:even-components',r'$i$ & $k$ & $d_{ik}$ & $h_{ik}$ & $o_{ik}$ & $m_{ik}$',evenrows,'scriptsize')
out+=r'''
The odd table, cosine table and even table contain respectively $84+12$, $9$
and $217$ finite comparisons, for a total of $322$. All other comparisons are
listed in the scalar, residual and vector tables. The analytic treatment of
the infinitely many remaining rows is independent of these finite tables.
'''
import argparse
parser=argparse.ArgumentParser()
parser.add_argument('--output-dir',type=Path,default=root/'results')
output_dir=parser.parse_args().output_dir
output_dir.mkdir(parents=True,exist_ok=True)
(output_dir/'recomputed_expanded_arithmetic.tex').write_text(out,encoding='utf-8')
record={'trial':frozen,'even_integer_comparisons':evenrecords,'residual_numerators':resceil,'residual_squares_sum':resnumer,'residual_tail_numerator':tailceil,'scalar_bounds':{k:str(v) for k,v in scalar.items()},'vector_bounds':{k:str(v) for k,v in data['vals'].items()},'counts':{'single':9,'odd':84,'odd_zero':12,'even':217}}
(output_dir/'expanded_arithmetic_data.json').write_text(json.dumps(record,ensure_ascii=False,indent=2),encoding='utf-8')
print('Created expanded rational tables; all 322 inequalities and vector/residual bounds pass.')
print('Rational trial coefficients:',frozen['numerators'])
print('Smallest even integer margin:',min(r['margin'] for r in evenrecords))
print('Residual square bound:',float(data['vals']['residual_sq']))
