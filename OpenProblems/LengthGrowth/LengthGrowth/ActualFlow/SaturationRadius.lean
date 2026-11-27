import LengthGrowth.ActualFlow.PhysicalSaturationGap
import LengthGrowth.ActualFlow.RadiusGrowth
import LengthGrowth.ActualFlow.SharpCircle

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

theorem optimalSimilarityMoment_le_circumradius :
    c.optimalSimilarityMoment ≤ c.period*c.circumradius^2 := by
  have cc : Continuous c.curve := continuous_iff_continuousAt.mpr fun s => (c.curve_deriv s).continuousAt
  obtain ⟨v,_,mx⟩ := isCompact_Icc.exists_isMaxOn ⟨0,le_rfl,c.period_pos.le⟩ cc.norm.continuousOn
  have ne : c.enclosingRadii.Nonempty := ⟨‖c.curve v‖,0,fun s hs => by simpa using mx hs⟩
  have bd : BddBelow c.enclosingRadii := ⟨0,fun r ⟨z,hz⟩ =>
    (norm_nonneg _).trans (hz 0 ⟨le_rfl,c.period_pos.le⟩)⟩
  have closed : IsClosed {r : ℝ | c.optimalSimilarityMoment≤c.period*r^2} :=
    isClosed_le continuous_const (continuous_const.mul (continuous_id.pow 2))
  have sub : c.enclosingRadii ⊆ {r : ℝ | c.optimalSimilarityMoment≤c.period*r^2} := by
    rintro r ⟨z,cover⟩
    have low : c.optimalSimilarityMoment ≤ ∫s in 0..c.period,c.similaritySupport z 0 s^2 := by
      apply csInf_le
      · refine ⟨0,?_⟩
        rintro _ ⟨w,b,rfl⟩
        exact intervalIntegral.integral_nonneg_of_forall c.period_pos.le (fun x => sq_nonneg _)
      · exact ⟨z,0,rfl⟩
    apply low.trans
    calc
      _ ≤ ∫s in 0..c.period,r^2 := by
        apply intervalIntegral.integral_mono_on c.period_pos.le
          (((c.similaritySupport_continuous z 0).pow 2).intervalIntegrable _ _) intervalIntegrable_const
        intro s hs
        have point := abs_real_inner_le_norm (c.normal s) (c.curve s-z)
        rw [c.normal_unit,one_mul] at point
        simpa [similaritySupport] using pow_le_pow_left₀ (abs_nonneg _) (point.trans (cover s hs)) 2
      _ = c.period*r^2 := by simp [smul_eq_mul]
  exact (closed.closure_subset_iff.mpr sub) (csInf_mem_closure ne bd)
end LengthGrowth.ClosedFrenetCurve

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

theorem productGrowthFraction_circumradius (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t) :
    c.length t/(4*c.energy t) ≤ (1/2-c.productGrowthFraction t)*c.circumradius t^2 := by
  let p := (c.regularPositionAt ht.le).closedFrenetCurve
  have hL : p.period=c.length t := rfl
  have hR : p.circumradius=c.circumradius t := by simp only [circumradius,dif_pos ht.le,p]
  have m := p.optimalSimilarityMoment_le_circumradius
  rw [hL,hR] at m
  have e := c.energy_pos ht.le
  have l : 0<c.length t := p.period_pos
  have gap := c.productGrowthFraction_le_pi_gap hf ht
  have g : 0≤1/2-c.productGrowthFraction t := by
    have n : 0≤Real.pi^2/c.normalizedProduct t :=
      div_nonneg (sq_nonneg _) (mul_nonneg e.le l.le)
    linarith
  have h := (c.productGrowthFraction_optimal_moment hf ht).trans (mul_le_mul_of_nonneg_left m g)
  apply (mul_le_mul_iff_left₀ l).mp
  convert h using 1 <;> ring

theorem productGrowthFraction_nonpos_of_radius (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t)
    (concentrated : 2*c.energy t*c.circumradius t^2 ≤ c.length t) :
    c.productGrowthFraction t ≤ 0 := by
  have geom := c.productGrowthFraction_circumradius hf ht
  have e := c.energy_pos ht.le
  have control := c.circumradius_slice_controls ht.le
  have rp : c.circumradius t ≠ 0 := by
    intro h
    rw [h,mul_zero] at control
    linarith only [control.2]
  have h := (div_le_iff₀ (show 0<4*c.energy t by positivity)).mp geom
  by_contra! positive
  nlinarith only [h,concentrated,mul_pos positive (mul_pos e (sq_pos_of_ne_zero rp))]

theorem radius_lower_of_productGrowthFraction (hf : c.IsNormalFEF) {t a : ℝ} (ht : 0<t)
    (ha : a<1/2) (rate : a≤c.productGrowthFraction t) :
    c.length t/(2*c.energy t*(1-2*a)) ≤ c.circumradius t^2 := by
  have h := c.productGrowthFraction_circumradius hf ht
  have e := c.energy_pos ht.le
  have d : 0<1-2*a := by linarith
  apply (div_le_iff₀ (by positivity)).mpr
  have b := (div_le_iff₀ (show 0<4*c.energy t by positivity)).mp h
  have m := mul_le_mul_of_nonneg_right rate (mul_nonneg e.le (sq_nonneg (c.circumradius t)))
  nlinarith only [b,m]
end LengthGrowth.ActualFlow.ForwardImmersion

namespace LengthGrowth.ActualFlow.SharpCircle
theorem productGrowthFraction_pi_gap_equality (r : ℝ) (hr : 0<r) {t : ℝ} (ht : 0<t) :
    (flow r hr).productGrowthFraction t = 1/2-Real.pi^2/(flow r hr).normalizedProduct t := by
  have product {x : ℝ} (hx : 0≤x) : (flow r hr).normalizedProduct x=2*Real.pi^2 :=
    (static_equalities r hr hx).1
  have eq : (flow r hr).normalizedProduct =ᶠ[nhds t] (fun _ => 2*Real.pi^2) := by
    filter_upwards [lt_mem_nhds ht] with x hx
    exact product hx.le
  have hd : deriv (flow r hr).normalizedProduct t=0 := by
    rw [Filter.EventuallyEq.deriv_eq eq,deriv_const]
  rw [ForwardImmersion.productGrowthFraction,hd,product ht.le,mul_zero,zero_div]
  field_simp [Real.pi_ne_zero]
  ring
end LengthGrowth.ActualFlow.SharpCircle

#print axioms LengthGrowth.ActualFlow.ForwardImmersion.productGrowthFraction_circumradius
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.productGrowthFraction_nonpos_of_radius
#print axioms LengthGrowth.ActualFlow.SharpCircle.productGrowthFraction_pi_gap_equality
