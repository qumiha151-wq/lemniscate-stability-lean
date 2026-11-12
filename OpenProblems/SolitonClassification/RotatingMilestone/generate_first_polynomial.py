"""Produce an untrusted recorded output for an actual order-60 execution.

The emitted Lean equality re-executes fixedTaylorEndpoint in the kernel.
Only the polynomial is claimed enclosed. No ODE truncation is assumed.
"""
from pathlib import Path
from fractions import Fraction as Q
import json
HERE=Path(__file__).resolve().parent
src=HERE.parent/'next_research'/'classification_odd_branch_interval'/'shooting_certificate.json'
cap=json.loads(src.read_text())
x=list(map(Q,cap['center_exact_decimal']))
e=list(map(Q,cap['phase_exact_decimal']))
S=10**60
def ofq(x):return (x.numerator*S//x.denominator,1)
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[0],a[1])
def scale(n,a):return(n*a[0],abs(n)*a[1])
def ceildiv(a,n):return -((-a)//n)
def mul(a,b):return(a[0]*b[0]//S,ceildiv(abs(a[0])*b[1]+abs(b[0])*a[1]+a[1]*b[1],S)+1)
def div(a,n):return(a[0]//n,ceildiv(a[1],n)+1)
def conv(a,b,n):
    z=(0,0)
    for j in range(n+1):z=add(z,mul(a[j],b[n-j]))
    return z
init=[x[0],x[3]*e[0]/8,x[1],x[3]*e[1],x[4],Q(0)]
c=[list(map(ofq,init))]
sq=[]
for n in range(60):
    cc=lambda i:[row[i] for row in c]
    sq.append(conv(cc(0),cc(0),n))
    rhs=[scale(8,c[n][1]),
         add(neg(div(conv(sq,cc(0),n),16)),add(neg(div(c[n][2],8)),neg(div(conv(cc(4),cc(3),n),8)))),
         neg(conv(cc(0),cc(3),n)),
         add(ofq(Q(1)) if n==0 else (0,0),conv(cc(0),cc(2),n)),
         (0,0),c[n][0]]
    c.append([div(z,n+1) for z in rhs])
t=ofq(x[2]/4000)
endpoint=[]
for i in range(6):
    z=(0,0)
    for n in reversed(range(61)):z=add(c[n][i],mul(t,z))
    endpoint.append(z)
literal=','.join(f'⟨{a},{b}⟩' for a,b in endpoint)
text='''import SolitonClassification.Rotating.CandidateInitial
import SolitonClassification.Rotating.FixedTaylor

/-! Kernel re-execution of this candidate's actual order-60 polynomial.
This is not an ODE endpoint or periodic root certificate. -/
namespace SolitonClassification.Rotating.Candidate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def recordedFirstPolynomial : Vector FixedBall 6 := Vector.ofFn ![ENDPOINT]

theorem first_polynomial60_computed :
    fixedTaylorEndpoint mesh step initialBalls 60=recordedFirstPolynomial := by
  decide +kernel

theorem first_polynomial60_enclosed (i : Fin 6) :
    (recordedFirstPolynomial[i.val]).Contains mesh
      ((taylorPolynomial initial 60 i).eval (step:ℝ)) := by
  rw [←first_polynomial60_computed]
  exact fixedTaylorEndpoint_contains mesh_pos step initial_enclosed 60 i

end SolitonClassification.Rotating.Candidate

#print axioms SolitonClassification.Rotating.Candidate.first_polynomial60_enclosed

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Rotating actual order-60 polynomial audit passed; standard axioms only."
'''.replace('ENDPOINT',literal)
(HERE/'SolitonClassification'/'Rotating'/'FirstPolynomial60.lean').write_text(text,encoding='utf-8')
(HERE/'first_polynomial60_record.json').write_text(json.dumps({
    'mesh':S,'order':60,'endpoint':endpoint,
    'display_midpoints':[float(Q(z[0],S)) for z in endpoint],
    'display_radii':[float(Q(z[1],S)) for z in endpoint],
    'status':'Untrusted record; exact re-execution equality must be checked by Lean.'},indent=2)+'\n')
print(json.dumps({'midpoints':[float(Q(z[0],S)) for z in endpoint],
                  'radii':[float(Q(z[1],S)) for z in endpoint]}))
