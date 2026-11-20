import SolitonClassification.ReflectedArc
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Radial variables for the actual centre shots, in physical arclength. -/
noncomputable section
namespace ClosedSimilarity.ReflectedArc.RadialLayer

def scale (z : ℝ → Support) (s : ℝ) : ℝ := ((z s 2)^2 + (z s 3)^2) ^ (1/6 : ℝ)
def K (z : ℝ → Support) (s : ℝ) := z s 0 / scale z s
def V (z : ℝ → Support) (s : ℝ) := z s 1 / (scale z s)^2
def C (z : ℝ → Support) (s : ℝ) := z s 3 / (scale z s)^3
def S (z : ℝ → Support) (s : ℝ) := -z s 2 / (scale z s)^3
def eps (z : ℝ → Support) (s : ℝ) := 1 / (scale z s)^4

theorem scale_six (z : ℝ → Support) (s : ℝ) :
    (scale z s)^6 = (z s 2)^2 + (z s 3)^2 := by
  rw [scale,← Real.rpow_natCast _ 6,← Real.rpow_mul (by positivity)]
  norm_num

/-- The field in physical arclength is the regular layer field multiplied by
    the positive clock rate |X|^(1/3). C and S are cosine and sine of the
    tangent angle relative to the radial direction. -/
theorem physical_rates {z : ℝ → Support} {s : ℝ}
    (hd : HasDerivAt z (supportField (z s)) s)
    (off : 0 < (z s 2)^2 + (z s 3)^2) :
    HasDerivAt (K z) (scale z s*(V z s-eps z s*K z s*C z s/3)) s ∧
    HasDerivAt (V z) (scale z s*(-(K z s)^3/2+S z s-2*eps z s*V z s*C z s/3)) s ∧
    HasDerivAt (C z) (scale z s*(-S z s*(K z s-eps z s*S z s))) s ∧
    HasDerivAt (S z) (scale z s*(C z s*(K z s-eps z s*S z s))) s ∧
    HasDerivAt (eps z) (scale z s*(-4*(eps z s)^2*C z s/3)) s := by
  have h := hasDerivAt_pi.mp hd
  have dk : HasDerivAt (fun t => z t 0) (z s 1) s := h 0
  have dv : HasDerivAt (fun t => z t 1) (-(z s 0)^3/2-z s 2) s := h 1
  have dp : HasDerivAt (fun t => z t 2) (-z s 0*z s 3) s := h 2
  have dq : HasDerivAt (fun t => z t 3) (1+z s 0*z s 2) s := h 3
  have dsq : HasDerivAt (fun t => (z t 2)^2+(z t 3)^2) (2*z s 3) s := by
    convert! ((dp.pow 2).add (dq.pow 2)) using 1
    ring
  have hp : 0 < scale z s := Real.rpow_pos_of_pos off _
  have six := scale_six z s
  have ds : DifferentiableAt ℝ (scale z) s :=
    (dsq.rpow_const (p := 1/6) (Or.inl off.ne')).differentiableAt
  have d6 := ds.hasDerivAt.pow 6
  have ident : (fun t => (scale z t)^6) = fun t => (z t 2)^2 + (z t 3)^2 :=
    funext (scale_six z)
  change HasDerivAt (fun t => (scale z t)^6) _ s at d6
  rw [ident] at d6
  have eq := d6.unique dsq
  have dr : HasDerivAt (scale z) (z s 3/(3*(scale z s)^5)) s := by
    have de : deriv (scale z) s = z s 3/(3*(scale z s)^5) := by
      apply (eq_div_iff (by positivity)).mpr
      norm_num at eq
      linarith
    exact de ▸ ds.hasDerivAt
  refine ⟨?_,?_,?_,?_,?_⟩
  · convert! dk.div dr hp.ne' using 1
    dsimp [K,V,eps,C]
    field_simp [hp.ne']
  · convert! dv.div (dr.pow 2) (pow_ne_zero _ hp.ne') using 1
    dsimp [K,V,C,S,eps]
    field_simp [hp.ne']; ring
  · convert! dq.div (dr.pow 3) (pow_ne_zero _ hp.ne') using 1
    dsimp [K,S,C,eps]
    field_simp [hp.ne']
    nlinarith only [six]
  · convert! dp.neg.div (dr.pow 3) (pow_ne_zero _ hp.ne') using 1
    dsimp [K,S,C,eps]
    field_simp [hp.ne']
  · convert! (hasDerivAt_const s (1:ℝ)).div (dr.pow 4) (pow_ne_zero _ hp.ne') using 1
    dsimp [eps,C]
    field_simp [hp.ne']; ring

theorem seam_iff {z : ℝ → Support} {s : ℝ} (off : 0 < (z s 2)^2 + (z s 3)^2) :
    (V z s = 0 ∧ C z s = 0) ↔ (z s 1 = 0 ∧ z s 3 = 0) := by
  have hp : 0 < scale z s := Real.rpow_pos_of_pos off _
  simp [V,C,hp.ne']

end ClosedSimilarity.ReflectedArc.RadialLayer
#print axioms ClosedSimilarity.ReflectedArc.RadialLayer.physical_rates
