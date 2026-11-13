"""Untrusted exact-integer reference evaluator used only to propose Lean data."""
from fractions import Fraction as Q
S=10**60
ZERO=(0,0)
def ofq(x):return (x.numerator*S//x.denominator,1)
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[0],a[1])
def scale(n,a):return(n*a[0],abs(n)*a[1])
def ceildiv(a,n):return -((-a)//n)
def mul(a,b):return(a[0]*b[0]//S,ceildiv(abs(a[0])*b[1]+abs(b[0])*a[1]+a[1]*b[1],S)+1)
def div(a,n):return(a[0]//n,ceildiv(a[1],n)+1)
def conv(a,b,n):
    z=ZERO
    for j in range(n+1):z=add(z,mul(a[j],b[n-j]))
    return z
def state_coefficients(init,N):
    c=[list(init)];sq=[]
    for n in range(N):
        cc=lambda i:[row[i] for row in c]
        sq.append(conv(cc(0),cc(0),n))
        rhs=[scale(8,c[n][1]),
             add(neg(div(conv(sq,cc(0),n),16)),add(neg(div(c[n][2],8)),neg(div(conv(cc(4),cc(3),n),8)))),
             neg(conv(cc(0),cc(3),n)),
             add(ofq(Q(1)) if n==0 else ZERO,conv(cc(0),cc(2),n)),
             ZERO,c[n][0]]
        c.append([div(z,n+1) for z in rhs])
    return c,sq
def endpoint(c,t):
    out=[]
    for i in range(len(c[0])):
        z=ZERO
        for row in reversed(c):z=add(row[i],mul(t,z))
        out.append(z)
    return out
def variation_coefficients(c,q,column,N):
    w=[[ofq(Q(int(i==column))) for i in range(6)]]
    cc=lambda i:[row[i] for row in c]
    for n in range(N):
        ww=lambda i:[row[i] for row in w]
        rhs=[scale(8,w[n][1]),
             add(neg(div(scale(3,conv(q,ww(0),n)),16)),
               add(neg(div(w[n][2],8)),
                 add(neg(div(conv(cc(4),ww(3),n),8)),neg(div(conv(cc(3),ww(4),n),8))))),
             add(neg(conv(cc(0),ww(3),n)),neg(conv(cc(3),ww(0),n))),
             add(conv(cc(0),ww(2),n),conv(cc(2),ww(0),n)),
             ZERO,w[n][0]]
        w.append([div(z,n+1) for z in rhs])
    return w
def ball(v):return f'⟨{v[0]},{v[1]}⟩'
def vec(v):return '⟨#['+','.join(map(ball,v))+'],rfl⟩'
