import SolitonClassification.SolitonDilation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! If the force is a continuous single-valued function of curvature on a
noncircular closed similarity profile, the angular coefficient vanishes. -/
noncomputable section
namespace ClosedSimilarity.PeriodicSupportProfile
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
private def posPrimitive (x : ℝ) := ∫ u in 0..x, max u 0

private theorem pp_deriv (x : ℝ) : HasDerivAt posPrimitive (max x 0) x := by
  have c : Continuous (fun u : ℝ => max u 0) := continuous_id.max continuous_const
  exact intervalIntegral.integral_hasDerivAt_right (c.intervalIntegrable _ _)
    c.aestronglyMeasurable.stronglyMeasurableAtFilter c.continuousAt

private theorem pp_smooth : ContDiff ℝ 1 posPrimitive := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (pp_deriv x).differentiableAt,?_⟩
  rw [show deriv posPrimitive=(fun x : ℝ => max x 0) from funext fun x => (pp_deriv x).deriv]
  exact continuous_id.max continuous_const

private theorem pp_zero {x : ℝ} (hx : x≤0) : posPrimitive x=0 := by
  have h : (∫ u in 0..x, max u 0)=∫ _ in 0..x,(0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_ge hx] at ht
    exact max_eq_right ht.2
  simpa [posPrimitive] using h

private theorem pp_pos {x : ℝ} (hx : 0<x) : 0<posPrimitive x := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f:=fun _ : ℝ => (0:ℝ)) (g:=fun u : ℝ => max u 0) hx
    continuous_const.continuousOn (continuous_id.max continuous_const).continuousOn
    (fun _ _ => le_max_right _ _) ⟨x,⟨hx.le,le_rfl⟩,by simpa [hx.le] using hx⟩
  simpa [posPrimitive] using h

variable {a b L : ℝ} (z : PeriodicSupportProfile a b L)

private def balance (s : ℝ) := a*z.q s-b*z.p s

private theorem force_slope (s : ℝ) : HasDerivAt z.force (z.k s*z.balance s-b) s := by
  convert! ((z.dp s).const_mul (-a)).sub ((z.dq s).const_mul b) using 1
  unfold balance
  ring

private theorem weighted_force (w G : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hG : Continuous G) (rel : ∀ t, z.force t=G (z.k t)) (s : ℝ) :
    (∫ t in s..s+L, w (z.k t)*(z.k t*z.balance t-b))=0 := by
  have cf : Continuous (fun x => deriv w x*G x) :=
    hw.continuous_deriv_one.mul hG
  let J := fun x => ∫ u in 0..x, deriv w u*G u
  let V := fun t => w (z.k t)*z.force t-J (z.k t)
  have dV (t : ℝ) : HasDerivAt V (w (z.k t)*(z.k t*z.balance t-b)) t := by
    have dj : HasDerivAt J (deriv w (z.k t)*G (z.k t)) (z.k t) :=
      intervalIntegral.integral_hasDerivAt_right (cf.intervalIntegrable _ _)
        cf.aestronglyMeasurable.stronglyMeasurableAtFilter cf.continuousAt
    have dw := ((hw.differentiable (by simp) (z.k t)).hasDerivAt.comp t (z.dk t))
    convert! (dw.mul (z.force_slope t)).sub (dj.comp t (z.dk t)) using 1
    rw [rel]
    simp only [Function.comp_apply]
    ring
  have cb : Continuous z.balance := (z.continuous_q.const_mul a).sub (z.continuous_p.const_mul b)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => dV t)
    (((hw.continuous.comp z.continuous_k).mul
      ((z.continuous_k.mul cb).sub continuous_const)).intervalIntegrable _ _)]
  simp only [V,rel,z.periodic_k s,sub_self]

theorem angular_rate_zero_of_continuous_force_law (hL : 0<L)
    (hn : ¬∃ c : ℝ, ∀ s, z.k s=c) {G : ℝ → ℝ} (hG : Continuous G)
    (rel : ∀ t, z.force t=G (z.k t)) : b=0 := by
  by_contra hb
  obtain ⟨⟨x,hx⟩,y,hy⟩ := z.both_curvature_excursions_of_period hL hn
  have hr := z.curvatureRMS_pos (z.dilation_pos hL) hL
  obtain ⟨s,hs⟩ := intermediate_value_univ x y z.continuous_k
    (show (0:ℝ)∈Icc (z.k x) (z.k y) from ⟨by linarith,by linarith⟩)
  have cb : Continuous z.balance := (z.continuous_q.const_mul a).sub (z.continuous_p.const_mul b)
  obtain ⟨m,_,hm⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (show s≤s+L by linarith)) cb.abs.continuousOn
  let δ := |b|/(|z.balance m|+1)
  have hδ : 0<δ := div_pos (abs_pos.mpr hb) (by positivity)
  let w := fun x : ℝ => posPrimitive (δ^2-x^2)
  have cw : ContDiff ℝ 1 w := pp_smooth.comp (contDiff_const.sub (contDiff_id.pow 2))
  let g := fun t => w (z.k t)*b*(b-z.k t*z.balance t)
  have cg : Continuous g := ((cw.continuous.comp z.continuous_k).mul continuous_const).mul
    (continuous_const.sub (z.continuous_k.mul cb))
  have pos (t : ℝ) (ht : t∈Icc s (s+L)) : 0≤g t := by
    by_cases h : |z.k t|<δ
    · have st : |z.k t*z.balance t| < |b| := by
        rw [abs_mul]
        have h₀ : |z.k t| * (|z.balance m|+1)< |b| :=
          (lt_div_iff₀ (by positivity)).mp h
        have h₁ := mul_le_mul_of_nonneg_left (hm ht) (abs_nonneg (z.k t))
        nlinarith [abs_nonneg (z.k t)]
      have prod : 0≤b*(b-z.k t*z.balance t) := by
        rcases lt_or_gt_of_ne hb with hneg|hpos
        · rw [abs_of_neg hneg] at st
          exact mul_nonneg_of_nonpos_of_nonpos hneg.le (by linarith [(abs_lt.mp st).1])
        · rw [abs_of_pos hpos] at st
          exact mul_nonneg hpos.le (by linarith [(abs_lt.mp st).2])
      have wp : 0<w (z.k t) := pp_pos (by nlinarith [sq_abs (z.k t),sq_nonneg (δ-|z.k t|),sq_lt_sq' (abs_lt.mp h).1 (abs_lt.mp h).2])
      dsimp only [g]
      rw [mul_assoc]
      exact mul_nonneg wp.le prod
    · have hz : w (z.k t)=0 := pp_zero (by
        have hh := le_of_not_gt h
        nlinarith [sq_abs (z.k t),mul_nonneg (sub_nonneg.mpr hh) (add_nonneg hδ.le (abs_nonneg (z.k t)))])
      simp [g,hz]
  have at0 : 0<w 0 := pp_pos (by simpa using sq_pos_of_pos hδ)
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f:=fun _ => (0:ℝ)) (g:=g) (show s<s+L by linarith)
    continuous_const.continuousOn cg.continuousOn (fun t h => pos t ⟨h.1.le,h.2⟩)
    ⟨s,⟨le_rfl,by linarith⟩,by simpa [g,hs,mul_assoc] using mul_pos at0 (mul_self_pos.mpr hb)⟩
  have eq : g=(fun t => (-b)*(w (z.k t)*(z.k t*z.balance t-b))) := by
    funext t
    dsimp [g]
    ring
  rw [intervalIntegral.integral_zero,eq,intervalIntegral.integral_const_mul,
    z.weighted_force _ _ cw hG rel,mul_zero] at hi
  exact (lt_irrefl _ hi)

end ClosedSimilarity.PeriodicSupportProfile
