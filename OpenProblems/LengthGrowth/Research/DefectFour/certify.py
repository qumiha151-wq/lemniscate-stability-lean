"""Generate outward rational bounds for the sixty-four intervals of z^(-1/2)."""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json

root=Path(__file__).resolve().parent
def sqrt_up(q):
    den=10**6
    m=isqrt(q.numerator*den**2//q.denominator)
    if Q(m,den)**2<q:m+=1
    assert Q(m,den)**2>=q
    return Q(m,den)
def bounds(i):
    l=Q(501,1000)*i/64
    u=Q(501,1000)*(i+1)/64
    c2=Q(227,500)
    c4=Q(81,500)
    v=(min(c2,c4/l) if l else c2)+Q(17,500)*u
    h=sqrt_up(v*v-Q(7,44)*l*l)
    B=Q(4,5)*v
    A=Q(6,5)*u*h+B*B/2
    q=min(2,10*u*u-8*l**4)
    f=-4*(1-A)**2+q+16*u**3*B-Q(489,100)*(l*B)**2
    assert A<Q(27,100) and f< -Q(1,40)
    return l,u,v,h,B,A,q,f
rows=[bounds(i) for i in range(64)]
print('upper force square bound',float(max(r[-1] for r in rows)),'upper square correction',float(max(r[5] for r in rows)))
(root/'intervals.json').write_text(json.dumps([[str(v) for v in r] for r in rows],indent=2)+'\n',encoding='utf8')
def rat(q):
    q=Q(q)
    return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
# Only v and the rational upper square root are supplied. All remaining
# endpoints, defect expressions and checks are evaluated by the Lean kernel.
lines=['import LengthGrowth.ActualFlow.StressAnnularTransfer',
 'namespace LengthGrowth.DefectFour','open Set','noncomputable section',
 'def leftQ (i : ℕ) : ℚ := 501*i/64000',
 'def rightQ (i : ℕ) : ℚ := 501*(i+1)/64000',
 'def upperV : ℕ → ℚ','  | 0 => '+rat(rows[0][2])]
lines.extend(f'  | {i} => {rat(r[2])}' for i,r in enumerate(rows) if i)
lines+=['  | _ => 0','def upperH : ℕ → ℚ']
lines.extend(f'  | {i} => {rat(r[3])}' for i,r in enumerate(rows))
lines+=['  | _ => 0',
 'def capQ (i : ℕ) : ℚ := (4/5)*upperV i',
 'def corrQ (i : ℕ) : ℚ := (6/5)*rightQ i*upperH i+(capQ i)^2/2',
 'def linQ (i : ℕ) : ℚ := min 2 (10*(rightQ i)^2-8*(leftQ i)^4)',
 'def binOK (i : ℕ) : Prop :=', 
 '  0≤upperV i ∧ 0≤upperH i ∧',
 '    (227/500+(17/500)*rightQ i≤upperV i ∨',
 '      (0<leftQ i ∧ (81/500)/leftQ i+(17/500)*rightQ i≤upperV i)) ∧',
 '    (upperV i)^2-(7/44)*(leftQ i)^2≤(upperH i)^2 ∧',
 '    0≤corrQ i ∧ corrQ i≤27/100 ∧',
 '    -4*(1-corrQ i)^2+linQ i+16*(rightQ i)^3*capQ i-',
 '      (489/100)*(leftQ i*capQ i)^2 ≤ -(1/40)',
 'instance (i : ℕ) : Decidable (binOK i) := by unfold binOK; infer_instance',
 'theorem verified_bins : ∀i : Fin 64, binOK i.val := by decide +kernel',
 'end','end LengthGrowth.DefectFour',
 '#print axioms LengthGrowth.DefectFour.verified_bins']
(root/'DefectFourBins.lean').write_text('\n'.join(lines)+'\n',encoding='utf8')
