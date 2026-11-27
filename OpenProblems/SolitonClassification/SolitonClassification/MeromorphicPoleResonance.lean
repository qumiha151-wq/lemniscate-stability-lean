import SolitonClassification.MeromorphicPoleCoefficients

noncomputable section
open Complex Polynomial Filter Set
open scoped Polynomial Topology
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
namespace ClosedSimilarity.MeromorphicCurvature

structure Resonance (a b c d e f g h:ℂ) : Prop where
  e1 : 48*c*d+36*c^3*d+6*c^5*d=0
  e2 : 60*c*e+33*c^2*d^2+30*c^3*e+6*c^5*e+15*c^4*d^2=0
  e3 : 72*c*f+34*c^3*f+54*c^2*d*e+10*c*d^3+6*c^5*f+30*c^4*d*e+20*c^3*d^3=0
  e4 : 96*c*g+48*c^3*g+72*c^2*d*f+24*c^2*e^2+24*c*d^2*e+6*c^5*g+30*c^4*d*f+15*c^4*e^2+60*c^3*d^2*e+15*c^2*d^4-2*a*c^2+2*b*c=0
  e5 : 192*c*h+72*c^3*h+120*c^2*d*g+72*c^2*e*f+48*c*d^2*f+24*c*d*e^2+6*c^5*h+30*c^4*d*g+30*c^4*e*f+60*c^3*d^2*f+60*c^3*d*e^2+60*c^2*d^3*e+6*c*d^5-4*a*c*d=0

theorem resonance_of_divides {P:ℂ[X]} {a b:ℂ} (z:X^6∣polyR a b P) :
    Resonance a b (P.coeff 0) (P.coeff 1) (P.coeff 2) (P.coeff 3) (P.coeff 4) (P.coeff 5) := by
  have h:=X_pow_dvd_iff.mp z
  exact ⟨(residual_coeff1 a b P).symm.trans (h 1 (by decide)),
    (residual_coeff2 a b P).symm.trans (h 2 (by decide)),
    (residual_coeff3 a b P).symm.trans (h 3 (by decide)),
    (residual_coeff4 a b P).symm.trans (h 4 (by decide)),
    (residual_coeff5 a b P).symm.trans (h 5 (by decide))⟩

private theorem impossible_four {a b:ℝ} {c d e f g h:ℂ}
    (ap:0<a) (nc:c≠0) (hc:c^2= -4) (eq:Resonance a b c d e f g h) : False := by
  have r2 : 36*c*e+108*d^2=0 := by
    linear_combination eq.e2-(-27*d^2+6*c*e+6*c^3*e+15*c^2*d^2)*hc
  have r3 : 32*c*f+264*d*e-70*c*d^3=0 := by
    linear_combination eq.e3-(10*c*f-66*d*e+6*c^3*f+30*c^2*d*e+20*c*d^3)*hc
  have r4 : 192*d*f+144*e^2-216*c*d^2*e-60*d^4+8*(a:ℂ)+2*(b:ℂ)*c=0 := by
    linear_combination eq.e4-(24*c*g-48*d*f-36*e^2+6*c^3*g+30*c^2*d*f+15*c^2*e^2+60*c*d^2*e+15*d^4-2*a)*hc
  have r5 : 192*e*f-192*c*d^2*f-216*c*d*e^2-240*d^3*e+6*c*d^5-4*(a:ℂ)*c*d=0 := by
    linear_combination eq.e5-(48*c*h-48*e*f+6*c^3*h+30*c^2*d*g+30*c^2*e*f+60*c*d^2*f+60*c*d*e^2+60*d^3*e)*hc
  have ce : c*e= -3*d^2 := by linear_combination r2/36
  have er : e=3*c*d^2/4 := by linear_combination (-c/4)*ce+(e/4)*hc
  rw [er] at r3 r4 r5
  have cf : c*(f+4*d^3)=0 := by linear_combination r3/32
  have fr : f= -4*d^3 := by linear_combination (mul_eq_zero.mp cf).resolve_left nc
  rw [fr] at r4 r5
  have four : -504*d^4+8*(a:ℂ)+2*(b:ℂ)*c=0 := by linear_combination r4+81*d^4*hc
  have five : c*d*(504*d^4-4*(a:ℂ))=0 := by linear_combination r5+(243/2)*c*d^5*hc
  have ri : c^2=(2*I)^2 := by rw [mul_pow,I_sq,hc];norm_num
  have cr : c.re=0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ri with u|u <;> rw [u] <;> simp [Complex.mul_re]
  have fourOr : 8*(a:ℂ)+2*(b:ℂ)*c=0 ∨ 4*(a:ℂ)+2*(b:ℂ)*c=0 := by
    by_cases z:d=0
    · left;simpa [z] using four
    · right;linear_combination four+(mul_eq_zero.mp five).resolve_left (mul_ne_zero nc z)
  rcases fourOr with eq|eq <;>
    have v:=congrArg Complex.re eq <;>
    simp [Complex.mul_re,Complex.mul_im,cr] at v <;> linarith

theorem pole_coefficients {a b:ℝ} {c d e f g h:ℂ}
    (ap:0<a) (nc:c≠0) (roots:(c^2+4)*(c^2+9)=0) (eq:Resonance a b c d e f g h) :
    c^2= -9 ∧ d=0 ∧ e=0 ∧ f=0 := by
  rcases mul_eq_zero.mp roots with four|nine
  · exact (impossible_four ap nc (by linear_combination four) eq).elim
  have hc : c^2= -9 := by linear_combination nine
  have r1 : 210*c*d=0 := by
    linear_combination eq.e1-(-18*c*d+6*c^3*d)*hc
  have r2 : 276*c*e+918*d^2=0 := by
    linear_combination eq.e2-(-102*d^2-24*c*e+6*c^3*e+15*c^2*d^2)*hc
  have r3 : 252*c*f+1944*d*e-170*c*d^3=0 := by
    linear_combination eq.e3-(-20*c*f-216*d*e+6*c^3*f+30*c^2*d*e+20*c*d^3)*hc
  have dz : d=0 := by
    apply (mul_eq_zero.mp (show c*d=0 by linear_combination r1/210)).resolve_left nc
  rw [dz] at r2 r3
  have ez : e=0 := by
    apply (mul_eq_zero.mp (show c*e=0 by linear_combination r2/276)).resolve_left nc
  rw [ez] at r3
  have fz : f=0 := by
    apply (mul_eq_zero.mp (show c*f=0 by linear_combination r3/252)).resolve_left nc
  exact ⟨hc,dz,ez,fz⟩

end ClosedSimilarity.MeromorphicCurvature
#print axioms ClosedSimilarity.MeromorphicCurvature.pole_coefficients
