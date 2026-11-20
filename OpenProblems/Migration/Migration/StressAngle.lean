import Migration.ForceIdentities
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.StressAngle

def weight (η k v : ℝ) : ℝ := (k^2/2+η)/((k^2/2+η)^2+v^2)

private theorem denom {η : ℝ} (hη : 0<η) (k v : ℝ) : 0<(k^2/2+η)^2+v^2 := by positivity

private theorem angleD {η : ℝ} (hη : 0<η) {k v : ℝ→ℝ} {s F : ℝ}
    (hk : HasDerivAt k (v s) s) (hv : HasDerivAt v (F-k s^3/2) s) :
    HasDerivAt (fun z => Real.arctan (v z/(k z^2/2+η)))
      (weight η (k s) (v s)*(F+η*k s)-k s) s := by
  let u:=k s^2/2+η
  have hu : 0<u := by dsimp [u]; positivity
  have hd : 0 < u^2 + v s^2 := by positivity
  have ha : HasDerivAt (fun z => k z^2/2+η) (k s*v s) s := by
    apply ((((hk.pow 2).div_const 2).add_const η)).congr_deriv
    ring
  apply ((hv.div ha hu.ne').arctan).congr_deriv
  change 1 / (1+(v s/u)^2)*(((F-k s^3/2)*u-v s*(k s*v s))/u^2) = _
  rw [show 1+(v s/u)^2=(u^2+v s^2)/u^2 by field_simp [hu.ne']]
  change _ = u/(u^2+v s^2)*(F+η*k s)-k s
  field_simp [hu.ne',hd.ne']
  dsimp [u]
  ring

/-- The regularized stress angle gives a weighted integral formula for the
signed turning of any smooth periodic unit-speed coordinate curve. -/
theorem weighted_force_integral {x y : ℝ→ℝ} {L η : ℝ} (hη : 0<η)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) (px : Function.Periodic x L) (py : Function.Periodic y L) :
    (∫ s in 0..L, weight η (signedCurvature x y s) (deriv (signedCurvature x y) s)*
      (elasticForce x y s+η*signedCurvature x y s))=∫ s in 0..L, signedCurvature x y s := by
  let k:=signedCurvature x y
  let v:=deriv k
  let F:=elasticForce x y
  have sk : ContDiff ℝ ∞ k:=signedCurvature_smooth hx hy
  have sv : ContDiff ℝ ∞ v:=(contDiff_infty_iff_deriv.mp sk).2
  have ck:=sk.continuous
  have cv:=sv.continuous
  have cF : Continuous F:=(elasticForce_smooth hx hy).continuous
  have cw : Continuous (fun s => weight η (k s) (v s)*(F s+η*k s)) := by
    dsimp only [weight]
    have ca := ((ck.pow 2).div_const 2).add_const η
    have cd := (ca.pow 2).add (cv.pow 2)
    exact (ca.div cd (fun s => (denom hη (k s) (v s)).ne')).mul (cF.add (ck.const_mul η))
  have hd (s : ℝ) : HasDerivAt (fun z => Real.arctan (v z/(k z^2/2+η)))
      (weight η (k s) (v s)*(F s+η*k s)-k s) s := by
    apply angleD hη ((sk.differentiable (by simp) s).hasDerivAt)
    apply ((sv.differentiable (by simp) s).hasDerivAt).congr_deriv
    dsimp [F,elasticForce,v,k]
    ring
  have kp : Function.Periodic k L:=signedCurvature_periodic px py
  have vp : Function.Periodic v L:=periodic_actual_deriv kp
  have ke : k L=k 0 := by simpa using kp 0
  have ve : v L=v 0 := by simpa using vp 0
  have eq:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=L)
    (fun s _ => hd s) ((cw.sub ck).intervalIntegrable 0 L)
  rw [intervalIntegral.integral_sub (cw.intervalIntegrable 0 L) (ck.intervalIntegrable 0 L),ke,ve,sub_self] at eq
  exact sub_eq_zero.mp eq

end MigrationGeometry.StressAngle
#print axioms MigrationGeometry.StressAngle.weighted_force_integral
