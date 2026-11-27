"""A strictly separated outer radial cap with two monotone polar-angle branches."""
from certificate import D,json
from flint import arb,acb,ctx

def cap_check(path,shape):
    ctx.prec=128
    packet=json.loads(path.read_bytes())
    M=65536
    def sample(key):
        c=[acb(arb(a)/D,arb(b)/D) for a,b in packet["rows"][key]]
        full=c+[acb(0)]*(M-2*len(c)+1)+[v.conjugate() for v in c[:0:-1]]
        return [a.real*M+arb(0,"1e-19") for a in acb.dft(full,inverse=True)]
    p,q=sample("p"),sample("q")
    ds=arb(61)/M
    level=arb(101)/2
    eligible=[]
    for i,(a,b) in enumerate(zip(p,q)):
        r=(a*a+b*b).sqrt()+arb(0,ds)
        if not r*r<level:
            eligible.append(i)
            assert a-90*ds>arb(11)/2 and r*r<52,(i,a,r)
            assert 48950<i<49500
        if 49030<=i<49420:assert r*r>level,(i,r)
    critical=shape["crossing_cells"]["q"]
    upper=[i for i in critical if i in eligible]
    assert len(upper)==1
    j=upper[0]
    assert q[j]>0 and q[j+1]<0
    # All inequalities below are strict, so neighboring branches keep them.
    assert (arb(5)/52)*(arb(60)*390/M)>2*arb.pi()/200
    assert arb(61)*550/M/7<arb.pi()/2
    return dict(mesh=M,cap_level_squared="101/2",unique_critical_cell=j,
                candidate_cell_range=[min(eligible),max(eligible)],
                inner_label_block=[49030,49420],pitch_order_lower_denominator=200)
