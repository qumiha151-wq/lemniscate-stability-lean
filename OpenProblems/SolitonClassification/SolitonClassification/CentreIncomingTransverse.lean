import SolitonClassification.CentreTransversality
import SolitonClassification.OuterIncomingCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace ClosedSimilarity.GlobalSupport.MovingSeam

/-- At an incoming level crossing the corrected height and positive radial
    alignment place the normalized amplitude in a compact annulus. -/
theorem annulus_at_level {x : Phase} {H m : ℝ} (reg : regular x)
    (far : 1 ≤ innerRoot x) (mp : 0<m) (alignment : m≤along x) (hit : -height x=H) :
    H-1≤(innerRoot x)^2 ∧ (innerRoot x)^2≤(H+1)/m := by
  have err := abs_le.mp (height_error reg far)
  rw [hit] at err
  have cap : along x≤1 := by nlinarith [(unit_chart x reg).2,sq_nonneg (across x),sq_nonneg (along x-1)]
  constructor
  · linarith [mul_le_mul_of_nonneg_left cap (sq_nonneg (innerRoot x)),err.2]
  · exact (le_div_iff₀ mp).mpr (by linarith [mul_le_mul_of_nonneg_left alignment (sq_nonneg (innerRoot x)),err.1])

theorem positive_rate_at_level (H m : ℝ) (high : 17≤H) (mp : 0<m) :
    ∃ η>0, ∀ x, regular x → 1 ≤ innerRoot x → m≤along x → -height x=H →
      1/(scale x)^4<η → scale x/8 < heightRate (1,x) := by
  obtain ⟨η,ep,bound⟩ := regular_physical_rate_band ((H+1)/m)
  refine ⟨η,ep,?_⟩
  intro x reg far align hit eps
  obtain ⟨lo,hi⟩ := annulus_at_level reg far mp align hit
  exact bound x reg (by change 12≤(innerRoot x)^2; linarith) hi eps

/-- One marker threshold controls every actual hit of this level, without
    requiring a continuously selected endpoint for the shooting interval. -/
theorem large_marker_rate_at_level (H m : ℝ) (high : 17≤H) (mp : 0<m) :
    ∃B>0, ∀ b≥B, ∀ x, regular x → 1 ≤ innerRoot x → m≤along x → -height x=H →
      (1/scale x^4)^3 ≤ 1200^4*(b⁻¹)^2 →
      4 ≤ innerRoot x ∧ scale x/8 < heightRate (1,x) := by
  obtain ⟨η,ep,bound⟩ := positive_rate_at_level H m high mp
  have lim : Tendsto (fun b : ℝ => 1200^4*(b⁻¹)^2) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.pow 2).const_mul ((1200:ℝ)^4)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (lim.eventually (eventually_lt_nhds (pow_pos ep 3)))
  refine ⟨max 1 N,lt_of_lt_of_le zero_lt_one (le_max_left ..),?_⟩
  intro b hb x reg far align hit eps
  have e := eps.trans_lt (hN _ ((le_max_right ..).trans hb))
  have less : 1/(scale x)^4<η := by
    by_contra! h
    exact e.not_ge (pow_le_pow_left₀ ep.le h 3)
  have lo := (annulus_at_level reg far mp align hit).1
  refine ⟨le_of_sq_le_sq (by linarith) (by linarith),bound _ reg far align hit less⟩

/-- The normalized slow-time derivative has the same strict sign, with all
    clocks restored. Applies directly to the curve called centreAt. -/
theorem centre_has_slow_rate {b u : ℝ} (bp : 0<b)
    (reg : regular (solution 1 ![0,b,0,0] (u/Real.sqrt b⁻¹)))
    (rate : 0<heightRate (1,solution 1 ![0,b,0,0] (u/Real.sqrt b⁻¹))) :
    ∃ d<0, HasDerivAt (fun v => -height (solution 1 ![0,b,0,0] (v/Real.sqrt b⁻¹))) d u := by
  have hd := rate_eq 1 (![0,b,0,0] : Phase) (u/Real.sqrt b⁻¹) reg
  have dt : HasDerivAt (fun v : ℝ => v/Real.sqrt b⁻¹) (1/Real.sqrt b⁻¹) u :=
    (hasDerivAt_id u).div_const _
  have D := (hd.comp u dt).neg
  exact ⟨_,neg_neg_of_pos (mul_pos rate (one_div_pos.mpr (Real.sqrt_pos.mpr (inv_pos.mpr bp)))),
    by simpa only [Pi.neg_def,Function.comp_def] using D⟩

theorem centre_rate_in_slow_time {b u : ℝ} (bp : 0<b)
    (reg : regular (solution 1 ![0,b,0,0] (u/Real.sqrt b⁻¹)))
    (rate : 0<heightRate (1,solution 1 ![0,b,0,0] (u/Real.sqrt b⁻¹))) :
    deriv (fun v => -height (solution 1 ![0,b,0,0] (v/Real.sqrt b⁻¹))) u<0 := by
  obtain ⟨_,lo,de⟩ := centre_has_slow_rate bp reg rate
  exact de.deriv.trans_lt lo

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.large_marker_rate_at_level
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.centre_rate_in_slow_time
