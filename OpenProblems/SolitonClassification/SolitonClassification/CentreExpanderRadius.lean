import SolitonClassification.StrongCentreMarker
import SolitonClassification.CentreShotAlignment

noncomputable section
namespace ClosedSimilarity.ReflectedArc.ZeroTurnExpander
open GlobalSupport OuterStress Set
open scoped ContDiff

/-- Every coefficient-one expander with a high centre marker reaches a
    definite physical distance from its centre in one half slow-time unit. -/
theorem reaches_large_radius {L b : ℝ} (P : ZeroTurnExpander L b) (large : 32≤b) :
    let s := (1/2:ℝ)/Real.sqrt b⁻¹
    b/288^2 ≤ (P.X s)^2 + (P.Y s)^2 := by
  let t := (1/2:ℝ)
  let f := Real.sqrt b⁻¹
  let s := t/f
  let z := centreData b (by linarith : 0<b)
  have bp : 0<b := by linarith
  have dp := inv_pos.mpr bp
  have small : b⁻¹≤1/32 := by rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) large
  have init : z.K 0=0 ∧ z.V 0=1 ∧ z.p 0=0 ∧ z.q 0=0 := by
    simp [z,centreData,ofSupport,solution_zero,bp.ne']
  have align := z.centre_alignment dp small init.1 init.2.1 init.2.2.1 init.2.2.2
  have amp : 0<z.amplitude t := by
    have h := (z.centre_bounds dp init.1 init.2.1 init.2.2.1 init.2.2.2
      (show 0≤t by norm_num [t])).2
    dsimp [t] at h ⊢
    linarith
  have rad := z.radius_sq t amp
  have sq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/288) align 2
  have cart := congrFun P.cartesianSupport_eq_solution s
  have p : z.p t=f*(-P.X s*deriv P.Y s+P.Y s*deriv P.X s) := by
    change f*(solution 1 ![0,b,0,0] s 2)=_
    rw [←cart]
    rfl
  have q : z.q t=f*(P.X s*deriv P.X s+P.Y s*deriv P.Y s) := by
    change f*(solution 1 ![0,b,0,0] s 3)=_
    rw [←cart]
    rfl
  have frame : z.p t^2+z.q t^2=f^2*((P.X s)^2+(P.Y s)^2) := by
    rw [p,q,←mul_one ((P.X s)^2+(P.Y s)^2),←P.unit_speed s]
    ring
  have fsq : f^2=b⁻¹ := Real.sq_sqrt dp.le
  rw [frame,fsq] at rad
  change b/288^2≤(P.X s)^2+(P.Y s)^2
  have bd : (1/288:ℝ)^2 ≤ b⁻¹*((P.X s)^2+(P.Y s)^2) := by
    change (1/288:ℝ)^2 ≤ (z.along t)^2 at sq
    linarith only [sq,rad,sq_nonneg (z.across t)]
  have scaled := mul_le_mul_of_nonneg_left bd bp.le
  rwa [←mul_assoc,mul_inv_cancel₀ bp.ne',one_mul,div_pow,one_pow,←div_eq_mul_one_div] at scaled

private theorem coordinate_bound {g : ℝ→ℝ} {d : ℝ} (dp : 0<d) (per : Function.Periodic g d)
    (smooth : ContDiff ℝ ∞ g) (start : g 0=0) (speed : ∀ s, |deriv g s|≤1)
    (s : ℝ) : |g s|≤d := by
  let u := toIcoMod dp 0 s
  have range : u ∈ Icc (0:ℝ) d := Ico_subset_Icc_self (toIcoMod_mem_Ico' dp s)
  have same : g u=g s := by
    unfold u
    rw [←self_sub_toIcoDiv_zsmul dp 0 s]
    exact per.sub_zsmul_eq _
  have val := (convex_Icc (0:ℝ) d).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => smooth.differentiable (by simp) x)
    (fun x _ => by simpa only [Real.norm_eq_abs] using speed x)
    (left_mem_Icc.mpr dp.le) range
  simpa only [Real.norm_eq_abs,start,sub_zero,one_mul,abs_of_nonneg range.1,same] using val.trans
    (show 1*‖u-0‖≤d by simpa [abs_of_nonneg range.1] using range.2)

/-- The estimate holds for any positive period of the position, including
    the least period when a longer traversal was originally specified. -/
theorem lower_bound_for_each_period {L b d : ℝ} (P : ZeroTurnExpander L b) (large : 32≤b)
    (dp : 0<d) (px : Function.Periodic P.X d) (py : Function.Periodic P.Y d) :
    Real.sqrt b/576 < d := by
  let s := (1/2:ℝ)/Real.sqrt b⁻¹
  have vx (u : ℝ) : |deriv P.X u|≤1 := by
    apply le_of_sq_le_sq _ zero_le_one
    rw [sq_abs]
    nlinarith only [P.unit_speed u,sq_nonneg (deriv P.Y u)]
  have vy (u : ℝ) : |deriv P.Y u|≤1 := by
    apply le_of_sq_le_sq _ zero_le_one
    rw [sq_abs]
    nlinarith only [P.unit_speed u,sq_nonneg (deriv P.X u)]
  have x := pow_le_pow_left₀ (abs_nonneg _) (coordinate_bound dp px P.X_smooth P.center_crossing.1 vx s) 2
  have y := pow_le_pow_left₀ (abs_nonneg _) (coordinate_bound dp py P.Y_smooth P.center_crossing.2.1 vy s) 2
  rw [sq_abs] at x y
  have dist : b/288^2 ≤ P.X s^2+P.Y s^2 := P.reaches_large_radius large
  have pos : 0<b := by linarith
  by_contra! small
  have ord : 576*d ≤ Real.sqrt b := by linarith
  have sq := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ)≤576) dp.le) ord 2
  rw [Real.sq_sqrt pos.le] at sq
  nlinarith only [x,y,dist,sq,mul_self_pos.mpr dp.ne']

end ClosedSimilarity.ReflectedArc.ZeroTurnExpander
#print axioms ClosedSimilarity.ReflectedArc.ZeroTurnExpander.reaches_large_radius
#print axioms ClosedSimilarity.ReflectedArc.ZeroTurnExpander.lower_bound_for_each_period
