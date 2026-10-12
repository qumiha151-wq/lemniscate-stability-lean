"""Development audit of explicit analytic formulas for the even Bloch sector.

The manuscript will state trial coefficients and finite rational inequalities,
not require this script or any numerical eigenvalue calculation.
"""
from fractions import Fraction as F
from math import isqrt,comb
from functools import lru_cache
from pathlib import Path
import json
from single_analytic_bounds import tail,moment,qb,rlo,rhi,H
DEN=10**70
def ceildiv(n,d):return -((-n)//d)
class I:
    def __init__(self,x=0,y=None):
        x=F(x);y=x if y is None else F(y)
        self.lo=x.numerator*DEN//x.denominator;self.hi=ceildiv(y.numerator*DEN,y.denominator)
    @classmethod
    def raw(cls,lo,hi):
        ans=object.__new__(cls);ans.lo=lo;ans.hi=hi;assert lo<=hi;return ans
    def __add__(self,x):
        x=cv(x);return I.raw(self.lo+x.lo,self.hi+x.hi)
    __radd__=__add__
    def __neg__(self):return I.raw(-self.hi,-self.lo)
    def __sub__(self,x):return self+-cv(x)
    def __rsub__(self,x):return cv(x)+-self
    def __mul__(self,x):
        x=cv(x);v=[self.lo*x.lo,self.lo*x.hi,self.hi*x.lo,self.hi*x.hi]
        return I.raw(min(v)//DEN,ceildiv(max(v),DEN))
    __rmul__=__mul__
    def recip(self):
        if self.hi<0:return -(-self).recip()
        assert self.lo>0
        return I.raw(DEN*DEN//self.hi,ceildiv(DEN*DEN,self.lo))
    def __truediv__(self,x):return self*cv(x).recip()
    def __rtruediv__(self,x):return cv(x)*self.recip()
    def __pow__(self,n):
        if n<0:return self.recip()**(-n)
        ans=I(1);base=self
        while n:
            if n%2:ans=ans*base
            base=base*base;n//=2
        return ans
    def lower(self):return F(self.lo,DEN)
    def upper(self):return F(self.hi,DEN)
    def ab(self):return F(max(abs(self.lo),abs(self.hi)),DEN)
    def mid(self):return float(F(self.lo+self.hi,2*DEN))
def cv(x):return x if isinstance(x,I)else I(x)
def sqrt(x):
    assert x.lo>0
    grid=10**30
    return I(F(isqrt(x.lo*grid*grid//DEN),grid),F(isqrt(x.hi*grid*grid//DEN)+1,grid))
def atan(t,N):return sum((F((-1)**k)*t**(2*k+1)/F(2*k+1)for k in range(N)),F(0))
pminus=16*atan(F(1,5),24)-4*atan(F(1,239),9)
pplus=16*atan(F(1,5),25)-4*atan(F(1,239),8)
pi=I(pminus,pplus)
term=I(1);exp=I(1)
for j in range(1,71):term=term*pi/j;exp+=term
exp=exp+I(0,(term*pi/71/(1-pi/72)).upper())
Q=1/exp
theta=1+2*sum((Q**(j*j)for j in range(1,6)),I(0))
theta+=I(0,(2*Q**36/(1-Q**13)).upper())
R=theta**-4
hh0=1-sum((16*R*j*Q**j/(1-Q**(2*j))for j in range(1,41)),I(0))-I(0,16*rhi/(1-qb*qb)*tail(qb,41,1))
SQRT2=sqrt(I(2))
@lru_cache(None)
def hh(n):
    n=abs(n)
    if n==0:return hh0
    assert n%2==0
    j=n//2
    return 8*R*j*Q**j/(1-Q**(2*j))
@lru_cache(None)
def aj(n,m,j):
    h=hh(n-m)
    if j==0:return F(15,2)*R*n*(7*m-n)*h-(4*R**2*n**4+42 if n==m else 0)
    if j==1:return R*(F(75,2)*n+F(105,2)*m)*h-(16*R**2*m**3 if n==m else 0)
    if j==2:return 45*R*h-(24*R**2*m*m if n==m else 0)
    if j==3:return -16*R**2*m if n==m else I(0)
    raise ValueError(j)
def s0(n,m):return (aj(n,m,0)+aj(m,n,0))/2
def sine(n,m):return aj(n,m,0)-aj(n,-m,0)
def dot(x,y):return sum((a*b for a,b in zip(x,y)),I(0))
def tr(mat):return list(map(list,zip(*mat)))
def mm(x,y):return [[dot(row,col)for col in tr(y)]for row in x]
def sym(x):return [[(x[i][j]+x[j][i])/2 for j in range(len(x))]for i in range(len(x))]
def h4sum(x):return sum((v.ab()*sum((2*j)**k for k in range(5))for j,v in enumerate(x,1)),F(0))
def kernel_tail(N,normlower):return 16*rhi/((1-qb*qb)*normlower)*sum(2**k*tail(qb,N+1,k+2)for k in range(5))
def trial_data():
    raw=json.loads(Path(__file__).with_name('adjoint_trial.json').read_text())
    phi=[I(F(v,raw['denominator']))for v in raw['sine_coefficients_numerators']]
    norm=sqrt(2*hh0/(5*R))
    es=[2*j*hh(2*j)/norm for j in range(1,19)]
    pair=dot(phi,es);pt=[v/pair for v in phi]
    residual=sum((dot([sine(2*i,2*j)for i in range(1,19)],pt).ab()**2 for j in range(1,41)),F(0))
    residual+=(480*rhi*H*sum(v.ab()for v in pt))**2*qb**(-36)*tail(qb*qb,41,6)
    N=15;en=sqrt(dot(es[:N],es[:N]));e=[v/en for v in es[:N]]
    ppair=dot(pt[:N],e);psi=[v/ppair for v in pt[:N]]
    z=[v-w for v,w in zip(psi,e)]
    zt=sum((p-ee).ab()**2 for p,ee in zip(pt,es))+(16*rhi/(1-qb*qb))**2*tail(qb*qb,19,4)/norm.lower()**2
    err_e=kernel_tail(N,norm.lower())+(1/en-1).ab()*h4sum(es[:N])
    Rstar=F(1,10**14)
    err_p=sum(pt[j-1].ab()*sum((2*j)**k for k in range(5))for j in range(16,19))+(1/ppair-1).ab()*h4sum(pt[:N])+225*Rstar
    env_e=max(e[j-1].ab()/SQRT2.lower()/F(1,10)**(j-3)for j in range(2,N+1))
    env_z=max(z[j-1].ab()/SQRT2.lower()/F(1,10)**(j-3)for j in range(2,N+1))
    info={'residual_sq':float(residual),'ztilde_sq':float(zt),'e_error_H4':float(err_e),'psi_error_H4':float(err_p),'e_H4':float(h4sum(e)+err_e),'psi_H4':float(h4sum(psi)+err_p),'zN_sq':float(sum(v.ab()**2 for v in z)),'envelope_e':float(env_e),'envelope_z':float(env_z),'pairing':pair.mid()}
    print(info,flush=True)
    assert residual<Rstar*Rstar
    assert zt<F(501,10000)**2
    assert err_e<F(1,10**11) and err_p<F(1,10**11)
    assert h4sum(e)+err_e<1000 and h4sum(psi)+err_p<1000
    assert sum(v.ab()**2 for v in z)<F(1,100)
    assert env_e<F(13,1000) and env_z<F(7,1000)
    return e,psi,info
def weights(label):
    if label=='e':return [F(1),F(0),F(0)]
    if label=='0':return [F(3,4),F(0),F(1,4)]
    if label=='c2':return [F(9,5),F(0),-F(3)]
    n=int(label)
    if n==4:return [F(13,40),-F(19,100),-F(17,100)]
    if n==-4:return [F(13,40),F(19,100),-F(31,100)]
    dd=[F(19,500),-F(1,40),-F(1,100)]if n>0 else[F(19,500),F(3,100),-F(11,500)]
    return [x*F(1,10)**((abs(n)-6)//2)for x in dd]
def wbern(label):
    p=weights(label)
    return [sum(p[j]*F(1,2)**j*F(comb(k,j),comb(2,j))for j in range(k+1))for k in range(3)]
def bern4(cs):
    return [sum((cs[j]*F(1,2)**j*F(comb(k,j),comb(4,j))for j in range(k+1)),I(0))for k in range(5)]
def bconv(x,y):
    n=len(x)-1;m=len(y)-1;ans=[F(0)]*(n+m+1)
    for i,xx in enumerate(x):
        for j,yy in enumerate(y):ans[i+j]+=xx*yy*F(comb(n,i)*comb(m,j),comb(n+m,i+j))
    return ans
def prepare():
    es,ps,info=trial_data();modes=list(range(-30,31,2));N=len(modes)
    e=[I(0)if n==0 else es[abs(n)//2-1]*(1 if n>0 else -1)/SQRT2 for n in modes]
    psi=[I(0)if n==0 else ps[abs(n)//2-1]*(1 if n>0 else -1)/SQRT2 for n in modes]
    z=[p-ee for p,ee in zip(psi,e)];aa=[I(0)if abs(n)!=2 else I(1 if n>0 else -1)/SQRT2 for n in modes]
    u=[p+q for p,q in zip(e,aa)];den=1+dot(e,aa)
    labels=['e','0','c2']+[str(n)for k in range(4,31,2)for n in [k,-k]]
    W=[[-v for v in e],[I(int(n==0))for n in modes],[I(0)if abs(n)!=2 else 1/SQRT2 for n in modes]]
    for label in labels[3:]:
        i=modes.index(int(label));W.append([I(int(i==j))-u[i]*u[j]/den for j in range(N)])
    left=[row.copy()for row in W];left[0]=[-v for v in psi]
    wz=[I(0)]+[dot(row,z)for row in W[1:]]
    wt=tr(W);right=[[wt[i][j]-e[i]*wz[j]for j in range(N)]for i in range(N)]
    hs=[mm(mm(W,[[s0(n,m)for m in modes]for n in modes]),wt)]
    for i in range(N):hs[0][0][i]=hs[0][i][0]=I(0)
    for j in [1,2,3]:hs.append(sym(mm(mm(left,[[aj(n,m,j)for m in modes]for n in modes]),right)))
    assert hs[1][0][0].lo<=0<=hs[1][0][0].hi and hs[3][0][0].lo<=0<=hs[3][0][0].hi
    hs[1][0][0]=hs[3][0][0]=I(0)
    gg=[[[v for v in row]for row in mat]for mat in hs]+[[[-4*R**2 if i==j else I(0)for j in range(N)]for i in range(N)]]
    for j in range(5):
        gg[j][0][0]=hs[2][0][0]if j==0 else(-4*R**2 if j==2 else I(0))
        for i in range(1,N):gg[j][0][i]=gg[j][i][0]=hs[j+1][0][i]if j<=2 else I(0)
    print('Finite coefficient matrices prepared.',flush=True)
    cols={};rt=tr(right)
    for m in range(-80,81,2):
        if abs(m)<=30:continue
        hh=[[dot(row,[s0(n,m)for n in modes])for row in W]];hh[0][0]=I(0)
        for j in [1,2]:
            av=[aj(n,m,j)for n in modes];atv=[aj(m,n,j)for n in modes]
            hh.append([(dot(l,av)+dot(rr,atv))/2 for l,rr in zip(left,rt)])
        gc=[hh[0][:],hh[1][:],hh[2][:],[I(0)]*N,[I(0)]*N]
        gc[0][0]=hh[1][0];gc[1][0]=hh[2][0];gc[2][0]=I(0)
        cols[m]=gc
    return labels,gg,cols,info
def certify():
    labels,gg,cols,info=prepare();N=len(labels);target=F(3,5)
    wbs={s:wbern(s)for s in labels}
    for m in cols:wbs[str(m)]=wbern(str(m))
    assert all(x>0 for w in wbs.values()for x in w)
    E=45*rhi*H;a=F(1,10)
    omitted=F(12,5)*E*a**12*(31**2*tail(qb*a,26,1)+62*tail(qb*a,26,2)+tail(qb*a,26,3))
    result={}
    for i,label in enumerate(labels):
        db=bern4([gg[k][i][i]for k in range(5)])
        rb=bconv([-v.upper()-target for v in db],wbs[label])
        for j,lab in enumerate(labels):
            if i==j:continue
            cb=bern4([gg[k][i][j]for k in range(5)])
            sub=bconv([v.ab()for v in cb],wbs[lab]);rb=[x-y for x,y in zip(rb,sub)]
        for m,gc in cols.items():
            cb=bern4([gc[k][i]for k in range(5)])
            sub=bconv([v.ab()for v in cb],wbs[str(m)]);rb=[x-y for x,y in zip(rb,sub)]
        rb=[x-omitted for x in rb]
        scaling=F(1)if label in ['e','0','c2']else a**((abs(int(label))-6)//2)
        mmr=min(rb)/scaling
        assert mmr>0,(label,float(mmr))
        lower=F((mmr*1000).numerator//(mmr*1000).denominator,1000)
        result[label]={'normalized_bernstein_lower':str(lower),'coefficients_lower_normalized':[float(x/scaling)for x in rb]}
        print(label,'normalized coefficient lower',float(mmr),'simple lower',str(lower),flush=True)
    z=qb/a;t=qb*a;mom=4*moment(t,0)+8*moment(t,1)+5*moment(t,2)+moment(t,3)
    cross=5*E*34*z**16*mom
    def high(n):return -4*rlo*rlo*(n-F(1,2))**4+45*rhi*(n+F(1,2))**2+(5*E*(moment(z,1)+moment(t,1))+1)*(n+2)**2+10*E*moment(t,2)*(n+2)+F(5,3)*E*moment(t,3)
    n=F(32);B=5*E*(moment(z,1)+moment(t,1))+1
    deriv=-16*rlo*rlo*(n-F(1,2))**3+90*rhi*(n+F(1,2))+2*B*(n+2)+10*E*moment(t,2)
    deriv2=-48*rlo*rlo*(n-F(1,2))**2+90*rhi+2*B
    assert cross<1 and high(n)<-1 and deriv<0 and deriv2<0
    info.update({'omitted_weighted_row':float(omitted),'high_cross_factor':float(cross),'high_P32':float(high(n)),'high_Pprime32':float(deriv),'high_Psecond32':float(deriv2)})
    Path(__file__).with_name('even_analytic_bounds.json').write_text(json.dumps({'info':info,'rows':result},indent=2),encoding='utf-8')
    print('All analytical comparison inequalities checked.',info,flush=True)
if __name__=='__main__':certify()
