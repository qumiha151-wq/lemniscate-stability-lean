from fractions import Fraction as Q

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def scale(a,c): return tuple(x*c for x in a)
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def rot(a): return (-a[1],a[0])
def solve(M,v):
    a,b=M[0]
    c,d=M[1]
    return ((d*v[0]-b*v[1])/(a*d-b*c),(a*v[1]-c*v[0])/(a*d-b*c))

def evaluate(t1,t2):
    p,q=(2*t/(1-t*t) for t in (t1,t2))
    l1,l2=((1+t*t)/(1-t*t) for t in (t1,t2))
    v=[(Q(0),Q(0)),(Q(1),-p),(Q(2),q-p),(Q(2),Q(0))]
    ell=[l1,l2,p-q,Q(2)]
    edges=[]
    for i,L in enumerate(ell):
        x,w=v[i],v[(i+1)%4]
        T=scale(sub(w,x),1/L)
        assert dot(T,T)==1
        edges.append((L,scale(add(w,x),Q(1,2)),T,rot(T)))
    def center(dirs):
        M=[[sum(e[0]*e[dirs][i]*e[dirs][j] for e in edges) for j in range(2)] for i in range(2)]
        b=[sum(e[0]*e[dirs][j]*dot(e[1],e[dirs]) for e in edges) for j in range(2)]
        return solve(M,b)
    cn,ct=center(3),center(2)
    cross=Q(0)
    tang=Q(0)
    for L,m,T,N in edges:
        pp,qq=dot(sub(m,cn),N),dot(sub(m,ct),T)
        cross+=L*pp*qq
        tang+=L*qq**2+L**3/12
    ratio=-cross/tang
    delta=sub(ct,cn)
    O=add(cn,scale(add(scale(rot(delta),ratio),scale(delta,ratio**2)),1/(1+ratio**2)))
    def height(z): return z[1]+p-q*(z[0]-1)
    assert min(map(height,v))==0
    return dict(P=p,Q=q,normal_center=cn,tangent_center=ct,pitch=ratio,full_center=O,
                normal_height=height(cn),full_height=height(O))

if __name__=='__main__':
    r=evaluate(Q(1,1001),Q(1,1201))
    assert -Q(72,100000)<r['normal_height']<-Q(71,100000)
    assert Q(25,100000)<r['full_center'][1]<Q(26,100000)
    assert -Q(136,100000)<r['pitch']<-Q(135,100000)
    for k,v in r.items(): print(k,*map(float,v) if isinstance(v,tuple) else [float(v)])
