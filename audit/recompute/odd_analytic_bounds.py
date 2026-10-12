"""Exact development check for analytic polynomial inequalities, not a paper dependency."""
from single_analytic_bounds import F,comb,qb,H,rlo,rhi,h,hzero,moment,tail
a=F(1,10);E=45*rhi*H
def padd(p,q):
    r=[F(0)]*max(len(p),len(q))
    for i,x in enumerate(p):r[i]+=x
    for i,x in enumerate(q):r[i]+=x
    return r
def pscale(p,t):return [x*t for x in p]
def pmul(p,q):
    r=[F(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):r[i+j]+=x*y
    return r
def peval(p,t):return sum(x*t**i for i,x in enumerate(p))
def weight(n):
    if n==1:return [F(1)]
    if n==-1:return [F(1),-F(8,5),F(4,5)]
    if n==3:return [F(1,2),-F(1,2),F(3,25)]
    if n==-3:return [F(1,2),F(0),F(3,10)]
    d=[F(2,25),-F(3,25),F(2,25)]if n>0 else[F(2,25),F(0),F(1,20)]
    if abs(n)==5:return d
    return pscale(d,F(3,25)*a**((abs(n)-7)//2))
def abs_entry_polynomial(n,m):
    p=[45*n*m-F(15,4)*(n-m)**2,F(45*(n+m)),F(45)]
    p0=peval(p,F(0));p1=peval(p,F(1,2))
    if min(p0,p1)>=0:ans=p
    elif max(p0,p1)<=0:ans=pscale(p,-1)
    else:ans=[abs(x)for x in p]
    return pscale(ans,rhi*h(n-m)[1])
def omitted(n):
    v=abs(n)+F(1,2);d=F(3,250);value=F(0)
    for sign in [-1,1]:
        L=(27-sign*n)//2
        value+=E*d*a**((sign*n-7)//2)*(v*v*tail(qb*a,L,1)+2*v*tail(qb*a,L,2)+tail(qb*a,L,3)/3)
    return value
def row_polynomial(n):
    k2=pmul([F(n),F(1)],[F(n),F(1)])
    negdiag=padd(pscale(pmul(k2,k2),4*rlo*rlo),pscale(k2,-45*rhi*hzero[1]))
    negdiag[0]+=41 # -(S_nn+1)
    result=pmul(negdiag,weight(n))
    for m in range(-25,26,2):
        if m!=n:result=padd(result,pscale(pmul(abs_entry_polynomial(n,m),weight(m)),-1))
    result[0]-=omitted(n)
    return result
def bernstein(p,degree=6):
    return [sum(p[j]*F(1,2)**j*F(comb(k,j),comb(degree,j))for j in range(min(k,len(p)-1)+1))for k in range(degree+1)]
def high_polynomial(v):
    return -4*rlo*rlo*v**4+(45*rhi+E*(moment(qb/a,1)+moment(qb*a,1))+8)*v*v+2*E*moment(qb*a,2)*v+E*moment(qb*a,3)/3
if __name__=='__main__':
    for n in range(-11,12,2):
        p=row_polynomial(n)
        print(n, 'bern6/8/12:',*[round(float(min(bernstein(p,d))),8)for d in [6,8,12]],'tail',float(omitted(n)))
    mom=4*moment(qb*a,0)+8*moment(qb*a,1)+5*moment(qb*a,2)+moment(qb*a,3)
    cross=E*F(37,16)*qb*F(27,2)*(qb/a)**6*mom
    print('cross coefficient <8:',float(cross));print('high at12.5:',float(high_polynomial(F(25,2))))
