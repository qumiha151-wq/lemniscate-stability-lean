from fractions import Fraction as F
from math import comb
qlo=F(4321,100000);qhi=F(2161,50000)
rlo=F(7177,10000);rhi=F(3589,5000)
qb=F(11,250);H=8*rhi/(1-qb*qb);C=105*rhi*H
def moment(z,p):
    # Eulerian polynomials, p<=6, obtained by differentiating geometric series.
    coeff=[F(1)]
    for k in range(p):
        out=[F(0)]*(len(coeff)+1)
        for i,x in enumerate(coeff):
            if i:out[i]+=i*x
            out[i+1]+=(k+1-i)*x
        coeff=out
    return sum(x*z**i for i,x in enumerate(coeff))/(1-z)**(p+1)
def tail(z,L,p):return z**L*sum(F(comb(p,k))*L**(p-k)*moment(z,k)for k in range(p+1))
def times(a,b):
    v=[x*y for x in a for y in b];return min(v),max(v)
def plus(a,b):return a[0]+b[0],a[1]+b[1]
def sc(a,c):return times(a,(c,c))
def h(n):
    n=abs(n)
    if n%2:return(F(0),F(0))
    if n==0:return hzero
    j=n//2
    return 8*rlo*j*qlo**j/(1-qlo**(2*j)),8*rhi*j*qhi**j/(1-qhi**(2*j))
hzero=(1-sum(2*h(2*j)[1]for j in range(1,5))-16*rhi/(1-qhi*qhi)*tail(qhi,5,1),1-sum(2*h(2*j)[0]for j in range(1,5)))
def s(n,m,sine=False):
    if not n and not m:return -F(42),-F(42)
    if not n*m:return sc(times(times((rlo,rhi),h(n+m)),(F(1414,1000),F(1415,1000))),-F(15,4)*(n+m)**2)
    sign=-1 if sine else 1
    v=times((rlo,rhi),plus(sc(h(n-m),45*n*m-F(15,4)*(n-m)**2),sc(h(n+m),sign*(-45*n*m-F(15,4)*(n+m)**2))))
    if n==m:v=plus(v,(-4*rhi*rhi*n**4-42,-4*rlo*rlo*n**4-42))
    return v
def ab(a):return max(abs(x)for x in a)
def weights(j,even):
    first=[F(1,9),F(1),F(11,50),F(29,1000)]if even else[F(1),F(1,2),F(11,125),F(1,100)]
    return first[j]if j<4 else first[3]*F(1,10)**(j-3)
def row(j,even,sine=False,cutoff=20):
    n=2*j+(not even);d=weights(j,even)
    v=s(n,n,sine)[1]
    v+=sum(ab(s(n,2*k+(not even),sine))*weights(k,even)/d for k in range(cutoff)if k!=j)
    zz=qb/10;LL=cutoff-j
    rem=C*weights(3,even)*F(1,10)**(j-3)/d*(n*n*tail(zz,LL,1)+2*n*tail(zz,LL,2)+tail(zz,LL,3))
    return v+rem
def poly(n,a=F(1,10)):
    return -4*rlo*rlo*n**4+45*rhi*n*n+C*(n*n*(moment(qb/a,1)+moment(qb*a,1))+2*n*moment(qb*a,2)+moment(qb*a,3))
if __name__=='__main__':
    print('h0',*(float(x)for x in hzero))
    for j in range(9):print(j,*[round(float(row(j,even,sine)),6)for even,sine in [(True,False),(False,False),(False,True)]])
    print('tail18',float(poly(18)))
    for j in [2,3,4]:
        n=2*j;v=s(n,n,True)[1]+sum(ab(s(n,2*k,True))for k in range(2,20)if j!=k)
        v+=C*(n*n*tail(qb,20-j,1)+2*n*tail(qb,20-j,2)+tail(qb,20-j,3))
        print('sine tail row',n,float(v))
    print('unit tail10',float(poly(10,F(1))))
    coupling=sum(ab(s(2,2*j,True))**2 for j in range(2,20))+C*C*sum(F(comb(4,k))*2**(4-k)*tail(qb*qb,19,k+2)for k in range(5))
    print('coupling square',float(coupling),'rho square',float(sum((F(j)*h(2*j)[1]/h(2)[0])**2 for j in range(2,20))+tail(qb*qb,20,4)/(qb*qb*(1-qb*qb)**2)))
