import SolitonClassification.SolitonDilation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Stress and the two averaging correctors for the frozen arclength ODE. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace ClosedSimilarity.FrozenStress

/-- Here the normal and tangent supports are those of a fixed unit vector. -/
structure Orbit where
  k : ℝ → ℝ
  v : ℝ → ℝ
  p : ℝ → ℝ
  q : ℝ → ℝ
  dk (s : ℝ) : HasDerivAt k (v s) s
  dv (s : ℝ) : HasDerivAt v (-(k s)^3/2-p s) s
  dp (s : ℝ) : HasDerivAt p (-k s*q s) s
  dq (s : ℝ) : HasDerivAt q (k s*p s) s
  unit (s : ℝ) : (p s)^2+(q s)^2=1

namespace Orbit
variable (z : Orbit)
def radial (s : ℝ) := z.k s^2/2*z.q s+z.v s*z.p s
def transverse (s : ℝ) := z.k s^2/2*z.p s-z.v s*z.q s
def amplitude (s : ℝ) := Real.sqrt ((z.k s^2/2)^2+z.v s^2)

theorem radial_hasDerivAt (s : ℝ) : HasDerivAt z.radial (-(z.p s)^2) s := by
  convert! ((((z.dk s).pow 2).div_const 2).mul (z.dq s) |>.add ((z.dv s).mul (z.dp s))) using 1
  simp only [Pi.pow_apply]
  ring

theorem transverse_hasDerivAt (s : ℝ) : HasDerivAt z.transverse (z.p s*z.q s) s := by
  convert! ((((z.dk s).pow 2).div_const 2).mul (z.dp s) |>.sub ((z.dv s).mul (z.dq s))) using 1
  simp only [Pi.pow_apply]
  ring

theorem amplitude_sq (s : ℝ) : z.amplitude s^2=(z.k s^2/2)^2+z.v s^2 :=
  Real.sq_sqrt (by positivity)

theorem stress_unit (s : ℝ) : z.radial s ^ 2 + z.transverse s ^ 2 = z.amplitude s ^ 2 := by
  rw [z.amplitude_sq]
  unfold radial transverse
  linear_combination ((z.k s^2/2)^2+z.v s^2) * z.unit s

theorem amplitude_hasDerivAt (s : ℝ) (ha : 0<z.amplitude s) :
    HasDerivAt z.amplitude (-z.p s*z.v s/z.amplitude s) s := by
  have de : HasDerivAt (fun x => (z.k x^2/2)^2+z.v x^2) (-2*z.v s*z.p s) s := by
    convert! ((((z.dk s).pow 2).div_const 2).pow 2 |>.add ((z.dv s).pow 2)) using 1
    simp only [Pi.pow_apply]
    ring
  have nn : 0<(z.k s^2/2)^2+z.v s^2 := by rw [← z.amplitude_sq]; positivity
  convert! de.sqrt nn.ne' using 1
  change _= -2*z.v s*z.p s/(2*z.amplitude s)
  field_simp [ha.ne']
end Orbit

def psi (U w a b : ℝ) := U^3*(a^2-b^2/2)/6 - U*w*a*b/2
def chi (U w a b : ℝ) := U*w*(a^2-b^2)/3+U^3*a*b/3
def remJ (U w a b p : ℝ) :=
  p*U*(-(U^2/2)*w*(a^2/3+b^2/12)+((U^2/2)^2/2+3*w^2/4)*a*b)

/-- Normalized oscillator rates at one nonzero stress. The phase may be chosen
locally, since its value need not be lifted to define any of these coordinates. -/
structure Rates (s : ℝ) (r U w a b : ℝ → ℝ) where
  pos : 0<r s
  oscillator : (U s^2/2)^2+w s^2=1
  unit : a s^2+b s^2=1
  dr : HasDerivAt r (-(w s*a s+U s^2/2*b s)*w s/(2*r s)) s
  dU : HasDerivAt U (w s*(r s+U s*(w s*a s+U s^2/2*b s)/(2*r s^2))) s
  dw : HasDerivAt w (-U s^3/2*(r s+U s*(w s*a s+U s^2/2*b s)/(2*r s^2))) s
  da : HasDerivAt a (-(w s*a s+U s^2/2*b s)*(U s^2/2)*b s/r s^2) s
  db : HasDerivAt b ((w s*a s+U s^2/2*b s)*(U s^2/2)*a s/r s^2) s

variable {s : ℝ} {r U w a b : ℝ → ℝ} (d : Rates s r U w a b)

def correctedImpact (r U w a b : ℝ → ℝ) (s : ℝ) :=
  r s*b s - psi (U s) (w s) (a s) (b s)/r s^2

def correctedOutgoing (r U w a b : ℝ → ℝ) (s : ℝ) :=
  -(r s^2*a s)-chi (U s) (w s) (a s) (b s)/r s

include d
theorem correctedImpact_hasDerivAt : HasDerivAt (correctedImpact r U w a b)
    (remJ (U s) (w s) (a s) (b s) (w s*a s+U s^2/2*b s)/r s^4) s := by
  have ps := (((d.dU.pow 3).mul ((d.da.pow 2).sub ((d.db.pow 2).div_const 2))).div_const 6).sub
    ((((d.dU.mul d.dw).mul d.da).mul d.db).div_const 2)
  convert! (d.dr.mul d.db).sub (ps.div (d.dr.pow 2) (pow_ne_zero _ d.pos.ne')) using 1
  unfold remJ
  simp only [Pi.pow_apply,Pi.mul_apply,Pi.sub_apply]
  field_simp [d.pos.ne']
  ring

def remH (U w a b p : ℝ) :=
  -((p^2-(1+a^2)/3)*U*p/2)
  +p*(U^2/2)*(4*U*w*a*b/3+U^3*(b^2-a^2)/3)
  -chi U w a b*p*w/2

theorem correctedOutgoing_hasDerivAt : HasDerivAt (correctedOutgoing r U w a b)
    ((1+a s^2)/3+remH (U s) (w s) (a s) (b s) (w s*a s+U s^2/2*b s)/r s^3) s := by
  have ch := (((d.dU.mul d.dw).mul ((d.da.pow 2).sub (d.db.pow 2))).div_const 3).add
    ((((d.dU.pow 3).mul d.da).mul d.db).div_const 3)
  convert! (((d.dr.pow 2).mul d.da).neg).sub (ch.div d.dr d.pos.ne') using 1
  have phase : (1+a s^2)/3 = (w s*a s+U s^2/2*b s)^2-
      ((w s^2-U s^4/2)*(a s^2-b s^2)/3+U s^2*w s*a s*b s) := by
    linear_combination -((2*a s^2+b s^2)/3)*d.oscillator - d.unit/3
  unfold remH chi
  rw [phase]
  simp only [Pi.pow_apply,Pi.mul_apply,Pi.sub_apply,Pi.add_apply]
  field_simp [d.pos.ne']
  ring

end ClosedSimilarity.FrozenStress
