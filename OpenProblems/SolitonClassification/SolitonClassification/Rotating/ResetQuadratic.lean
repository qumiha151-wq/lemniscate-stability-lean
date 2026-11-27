import SolitonClassification.Rotating.FlowBootstrapCoordinates
import SolitonClassification.Rotating.SignedResetShadow
namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
theorem bilinear_wide {a : State} (h0 : |a 0|≤9) (u v : State) :
    ‖bilinear a u v‖≤2*‖u‖*‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i <;> try { change ‖(0:ℝ)‖≤_; simp; positivity }
  · change |-3*a 0*u 0*v 0/16-u 4*v 3/8|≤_
    calc
      _ ≤ |-3*a 0*u 0*v 0/16|+|u 4*v 3/8| := abs_sub _ _
      _ = 3*|a 0| * |u 0| * |v 0|/16+|u 4| * |v 3|/8 := by
        simp only [abs_div,abs_mul]; norm_num
      _ ≤ 3*9*‖u‖*‖v‖/16+‖u‖*‖v‖/8 := by
        gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]
  · change |-u 0*v 3|≤_
    rw [abs_mul,abs_neg]
    calc
      _ ≤ ‖u‖*‖v‖ := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]
  · change |u 0*v 2|≤_
    rw [abs_mul]
    calc
      _ ≤ ‖u‖*‖v‖ := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]

theorem field_quadratic_wide {a x : State} (ha : |a 0|≤9)
    (hx : ‖x-a‖≤1) : ‖field x-field a-fderiv ℝ field a (x-a)‖≤3*‖x-a‖^2 := by
  have eq := field_expansion a (x-a)
  rw [add_sub_cancel] at eq
  have cancel : field x-field a-fderiv ℝ field a (x-a)=
      bilinear a (x-a) (x-a)+trilinear (x-a) (x-a) (x-a) := by
    rw [field_fderiv_apply,eq]; abel
  rw [cancel]
  apply (norm_add_le ..).trans
  have h1 := bilinear_wide ha (x-a) (x-a)
  have h2 := trilinear_bound (x-a) (x-a) (x-a)
  have h3 := mul_le_mul_of_nonneg_left hx (sq_nonneg ‖x-a‖)
  nlinarith only [h1,h2,h3,sq_nonneg ‖x-a‖]

def movingError (x Q : ℝ→State) (M : ℝ→FlowEnd) (t : ℝ) : State :=
  Ring.inverse (M t) (x t-Q t)

theorem moving_deriv {s t : ℝ} {S : Set ℝ} {x Q : ℝ→State} {M : ℝ→FlowEnd}
    {Z : FlowEnd} {r : State} (hu : IsUnit (M t))
    (hx : HasDerivWithinAt x (s • field (x t)) S t)
    (hQ : HasDerivWithinAt Q (s • field (Q t)+r) S t)
    (hM : HasDerivWithinAt M ((s • fderiv ℝ field (Q t))*M t+Z) S t) :
    HasDerivWithinAt (movingError x Q M)
      (bootstrapVelocity s (x t) (Q t) (M t) Z r) S t := by
  have hd := (referenceInverse_hasDerivWithinAt hM hu).clm_apply (hx.sub hQ)
  convert! hd using 1
  exact (bootstrap_derivative_algebra s (x t) (Q t) (M t) Z r hu).symm

theorem moving_velocity {s : ℝ} {x Q : State} {M Z : FlowEnd} {r : State}
    {E D A B I : ℝ} (hQ : |Q 0|≤9) (hD : ‖x-Q‖≤D) (h1 : D≤1)
    (hE : ‖Ring.inverse M (x-Q)‖≤E) (hZ : ‖Z‖≤B) (hr : ‖r‖≤A)
    (hI : ‖Ring.inverse M‖≤I) :
    ‖bootstrapVelocity s x Q M Z r‖≤I*(|s| *(3*D^2)+A+B*E) := by
  have hI0 := (norm_nonneg _).trans hI
  have hB0 := (norm_nonneg _).trans hZ
  have hpow := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hD)).mpr hD
  have hquad := (field_quadratic_wide hQ (hD.trans h1)).trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  have hs : ‖s • (field x-field Q-fderiv ℝ field Q (x-Q))‖≤|s| *(3*D^2) := by
    rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hquad (abs_nonneg _)
  have hze := (Z.le_opNorm _).trans (mul_le_mul hZ hE (norm_nonneg _) hB0)
  have hv := (norm_sub_le (s • (field x-field Q-fderiv ℝ field Q (x-Q))-r) _).trans
    (add_le_add ((norm_sub_le ..).trans (add_le_add hs hr)) hze)
  exact ((Ring.inverse M).le_opNorm _).trans (mul_le_mul hI hv (norm_nonneg _) hI0)

end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.moving_deriv
#print axioms SolitonClassification.Rotating.DyadicReset.moving_velocity
