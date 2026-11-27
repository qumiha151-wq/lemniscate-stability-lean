import LengthGrowth.ActualFlow.HighRecordExcursions

noncomputable section
namespace LengthGrowth.ActualFlow

/-- Differentiate the regularized stress current with respect to scale. The
two inputs u and v represent k^4/4 and k_s^2 on one spatial slice. -/
theorem scale_current_derivative {R : ℝ → ℝ} {a u v : ℝ}
    (pos : 0 < R a) (mass : R a ^ 2 = u + v + a^4)
    (rate : HasDerivAt R (2*a^3/R a) a) :
    HasDerivAt (fun b => b*(b^4-u)/R b^3)
      ((-u*(u+v)+(10*u+5*v)*a^4-a^8)/R a^5) a ∧
    HasDerivAt (fun b => -b/(2*R b^3)) ((5*a^4-u-v)/(2*R a^5)) a := by
  have hv : v=R a^2-u-a^4 := by linarith only [mass]
  constructor
  · convert ((hasDerivAt_id a).mul (((hasDerivAt_id a).pow 4).sub_const u)).div
        (rate.pow 3) (pow_ne_zero _ pos.ne') using 1 <;> first | rfl | skip
    simp only [id_eq,Pi.pow_apply,Pi.mul_apply,hv]
    field_simp [pos.ne']
    ring
  · convert (hasDerivAt_id a).neg.div ((rate.pow 3).const_mul 2)
        (mul_ne_zero (by norm_num) (pow_ne_zero _ pos.ne')) using 1 <;> first | rfl | skip
    simp only [id_eq,Pi.pow_apply,Pi.neg_apply,hv]
    field_simp [pos.ne']
    ring

private theorem mixed_current (k p f g R : ℝ) (pos : 0<R) :
    -k^2*g^2/(2*R^3)-2*k*p*f*g/R^3+3*k^2*p*f^2*g/(2*R^5) ≤
      4*p^2*f^2/R^3+9*k^2*p^2*f^4/(4*R^7) := by
  let A := k*g*R^2
  let B := -2*p*f*R^2
  let C := 3*k*p*f^2/2
  have q : -A^2/2+A*(B+C) ≤ B^2+C^2 := by
    nlinarith only [sq_nonneg (A-(B+C)),sq_nonneg (B-C)]
  apply (mul_le_mul_iff_of_pos_right (show 0 < 4*R^7 by positivity)).mp
  convert (mul_le_mul_of_nonneg_right q (by norm_num : (0:ℝ)≤4)) using 1 <;>
    dsimp only [A,B,C] <;> field_simp [pos.ne'] <;> ring

/-- A bound for the physical spatial flux density after periodic integration
by parts. The right hand side contains no derivatives of the force. -/
theorem scale_current_force_bound {k p f g r R a : ℝ}
    (hr : 0<r) (hR : r≤R) (hk : k^2≤2*r) (hp : p^2≤r^2) :
    a^2*((k^4/4-a^4)*f^2/R^3 - k^2*g^2/(2*R^3) -
      2*k*p*f*g/R^3 + 3*k^2*p*f^2*g/(2*R^5)) ≤
      (a^2*r^2/R^3)*(5*f^2 + (9/2)*f^4/r^3) := by
  have pos := hr.trans_le hR
  have hsq := mul_self_le_mul_self (sq_nonneg k) hk
  have quad : k^4/4-a^4 ≤ r^2 := by nlinarith only [hsq,sq_nonneg (a^2)]
  have lin := add_le_add (mul_le_mul_of_nonneg_right quad (sq_nonneg f))
    (mul_le_mul_of_nonneg_right hp (show 0≤4*f^2 by positivity))
  have low : (k^4/4-a^4)*f^2/R^3 + 4*p^2*f^2/R^3 ≤ 5*r^2*f^2/R^3 := by
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith only [lin]
  have kpp := mul_le_mul hk hp (sq_nonneg p) (by positivity)
  have r4 : r^4≤R^4 := pow_le_pow_left₀ hr.le hR 4
  have top : (k^2*p^2)*r ≤ 2*R^4 := calc
    _ ≤ ((2*r)*r^2)*r := mul_le_mul_of_nonneg_right kpp hr.le
    _ = 2*r^4 := by ring
    _ ≤ _ := by linarith only [r4]
  have high : 9*k^2*p^2*f^4/(4*R^7) ≤
      r^2/R^3*((9/2)*f^4/r^3) := by
    apply (mul_le_mul_iff_of_pos_right (show 0 < 4*R^7*r by positivity)).mp
    convert mul_le_mul_of_nonneg_right top (show 0≤9*f^4 by positivity) using 1 <;>
      field_simp [pos.ne',hr.ne']
    all_goals ring
  have mix := mixed_current k p f g R pos
  calc
    _ ≤ a^2*(5*r^2*f^2/R^3 + r^2/R^3*((9/2)*f^4/r^3)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
      ring_nf at low high mix ⊢
      linarith only [low, high, mix]
    _ = _ := by ring

/-- Two tails of the scale localizing weight. Here L=a^2 and
R=sqrt(r^2+L^2). Only the two metric lower bounds on R are needed. -/
theorem scale_weight_tails {L r R : ℝ} (hL : 0<L) (hr : 0<r)
    (lr : L≤R) (rr : r≤R) :
    L*r^2/R^3 ≤ (r/L)^2 ∧ L*r^2/R^3 ≤ L/r := by
  have pos := hr.trans_le rr
  constructor
  · have cube := pow_le_pow_left₀ hL.le lr 3
    apply (mul_le_mul_iff_of_pos_right (show 0<R^3*L^2 by positivity)).mp
    convert mul_le_mul_of_nonneg_right cube (sq_nonneg r) using 1 <;>
      field_simp [pos.ne',hL.ne']
  · have cube := pow_le_pow_left₀ hr.le rr 3
    apply (mul_le_mul_iff_of_pos_right (show 0<R^3*r by positivity)).mp
    convert mul_le_mul_of_nonneg_left cube hL.le using 1 <;>
      field_simp [pos.ne',hr.ne']

end LengthGrowth.ActualFlow
