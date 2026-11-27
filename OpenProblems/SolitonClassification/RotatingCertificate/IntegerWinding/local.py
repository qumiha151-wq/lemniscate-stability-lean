"""Check transverse hyperbolicity of the true integer-holonomy support orbit."""
import json
from trajectory import here, digest, arb, ctx
from flint import arb_mat

def main():
    ctx.dps=85
    root=json.loads((here/"certificate.json").read_bytes())
    for name,sha in root["files"].items():
        assert digest(here/name)==sha
    displacement=arb(root["eta"])/(1-arb(root["lip"]))
    K=I=arb(20000)
    L=arb(18);H=arb(4);T=arb(32)
    derivativeChange=(T*(4*K)*(4*I)*H*(4*K)**2+L*(4*K))*displacement
    sides=[]
    reports=[]
    for name in ("plus.json","minus.json"):
        rep=json.loads((here/name).read_bytes())
        jump=I*arb(rep["mjump"])
        centerError=K*(T*I*H*K*K*arb("1e-42")+jump).expm1()
        enlargement=derivativeChange+centerError
        assert enlargement<arb("1e-8")
        sides.append(arb_mat([[arb(v)+arb(0,enlargement) for v in row[:4]] for row in rep["matrix"][:4]]))
        reports.append(enlargement.str(55))
    M,N=sides
    samples=["-1000","-700","-.001","-.0001","3","5"]
    signs={}
    for x in samples:
        value=(M-arb(x)*N).det()
        assert abs(value)>0,(x,value)
        signs[x]={"sign":1 if value>0 else -1,"determinant":value.str(55)}
    for p,q in zip(samples[::2],samples[1::2]):
        assert signs[p]["sign"]==-signs[q]["sign"]
    result=dict(status="All three disjoint transverse Floquet intervals passed",
                 compare="det(M_plus-lambda*M_minus)",inputs=root["files"],root_sha256=digest(here/"certificate.json"),
                 maximum_root_displacement=displacement.str(55),inflations=reports,signs=signs,
                 exact_neutral_multiplier=1)
    (here/"hyperbolic.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result["signs"],indent=2))

if __name__=="__main__":
    main()
