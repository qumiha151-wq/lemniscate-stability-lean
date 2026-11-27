"""Enclose all distinct-parameter coincidences of the validated Fourier orbit."""
from certificate import here,D,json,sys,Fraction
from flint import arb,acb,ctx
from collections import defaultdict
from math import floor,ceil
from pathlib import Path

def count(path,M):
    ctx.prec=115
    d=json.loads(path.read_bytes())
    def spectrum(n):
        return [acb(arb(a)/D,arb(b)/D) for a,b in d["rows"][n]]
    def values(c):
        spec=c+[acb(0)]*(M-2*len(c)+1)+[v.conjugate() for v in c[:0:-1]]
        return [z.real*M for z in acb.dft(spec,inverse=True)]
    coeff=spectrum("k")
    lam=arb(d["length_scale"])/D
    pc=[acb(0)]+[lam*coef/acb(0,k) for k,coef in enumerate(coeff[1:],1)]
    angles=values(pc);base=angles[0];av=lam*coeff[0].real
    pg,qg=values(spectrum("p")),values(spectrum("q"))
    e=arb(0,"1e-19");T=[];X=[]; step=arb(61)/M
    for i in range(M):
        j=i if i<=M//2 else i-M
        theta=angles[i]-base+av*(2*arb.pi()*j/M)+arb(0,"1e-16")
        tangent=acb(theta.cos(),theta.sin())
        T.append(tangent);X.append(tangent*acb(qg[i]+e,pg[i]+e))
    bins=defaultdict(list)
    pitch=128
    def ix(x):
        # Outward-rounded bin limits; each stored square contains a full curve segment.
        v=x*pitch
        return range(int(v.lower().floor().unique_fmpz()),int(v.upper().floor().unique_fmpz())+1)
    pairs=set()
    for i,z in enumerate(X):
        box=arb(0,step)
        for u in ix(z.real+box):
            for v in ix(z.imag+box):
                for j in bins[u,v]:
                    if (min(i-j,M-i+j)+1)*610 < M:continue
                    if abs(X[j].real-z.real)>2*step or abs(X[j].imag-z.imag)>2*step:continue
                    pairs.add((j,i))
                bins[u,v].append(i)
    # Identify candidate regions on the grid torus; when a true root is near
    # the parameter cut keep lifts in a single local square and wrap indices.
    def canonical(i,j):
        a,b=i%M,j%M
        return (a,b) if a<b else (b,a)
    pending=set(pairs);clusters=[]
    while pending:
        v=pending.pop();todo=[v];cluster=[v]
        while todo:
            i,j=todo.pop()
            for di in (-1,0,1):
                for dj in (-1,0,1):
                    a=(i+di,j+dj);key=canonical(*a)
                    if key in pending:
                        pending.remove(key);todo.append(a);cluster.append(a)
        clusters.append(cluster)
    roots=[]; failures=[]
    for cluster in clusters:
        i,j=[round((min(p[k] for p in cluster)+max(p[k] for p in cluster)+1)/2) for k in (0,1)]
        R=max(max(abs(a-i),abs(a+1-i),abs(b-j),abs(b+1-j)) for a,b in cluster)*step
        # First use a constant inverse of the two tangent directions. The
        # affine Newton predictor defines the centre of a much tighter box.
        t,u=T[i%M],T[j%M]
        det=u.real*t.imag-t.real*u.imag
        if det.contains(0):failures.append(("parallel",i,j,len(cluster)));continue
        A=[[-u.imag/det,u.real/det],[-t.imag/det,t.real/det]]
        f=X[i%M]-X[j%M]
        pred=[-(a*f.real+b*f.imag) for a,b in A]
        # Enclose the derivative on the box with physical offsets <= R using
        # |T'|<=9, with the signs of both inverse columns retained.
        invbound=(abs(A[0][0])+abs(A[0][1])).max(abs(A[1][0])+abs(A[1][1])).upper()
        radius=float(R.upper())
        # invbound is an outward-rounded Arb evaluation of the inverse row norm.
        contraction=18*invbound*R
        if contraction>=1 or not all(abs(v)+contraction*R<R for v in pred):
            failures.append(("unresolved",i,j,len(cluster),float(contraction),radius));continue
        roots.append([i,j,len(cluster),radius,float(abs(det).lower())])
    separated_labels = []
    for i,j,_,radius,_ in roots:
        for k in (i,j):
            for l,other in separated_labels:
                difference=abs((k-l)%M)
                assert 60*min(difference,M-difference)/M > radius+other
            separated_labels.append((k,radius))
    return dict(mesh=M,eligible_pairs=len(pairs),clusters=len(clusters),roots=sorted(roots),failures=failures)

