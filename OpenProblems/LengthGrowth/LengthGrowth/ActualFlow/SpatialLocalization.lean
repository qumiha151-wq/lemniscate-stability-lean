import LengthGrowth.ActualFlow.LocalizationEnvelope
import LengthGrowth.ActualFlow.LocalizationOptimization

noncomputable section
open Set Filter
open scoped Topology
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- The maximum distance of one complete time slice from a fixed origin. -/
def fixedOriginRadius (O : ℂ) (t : ℝ) : ℝ :=
  sSup ((fun u => ‖c.position t u-O‖) '' Icc 0 c.period)

theorem fixedOriginRadius_attained (O : ℂ) {t : ℝ} (ht : 0≤t) :
    ∃u∈Icc 0 c.period, c.fixedOriginRadius O t=‖c.position t u-O‖ := by
  have hc : Continuous (fun u => ‖c.position t u-O‖) :=
    ((c.position_slice_smooth ht).continuous.sub continuous_const).norm
  obtain ⟨u,hu,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr c.period_pos.le)
    (f:=fun u => ‖c.position t u-O‖) hc.continuousOn
  refine ⟨u,hu,?_⟩
  apply IsGreatest.csSup_eq
  exact ⟨⟨u,hu,rfl⟩,fun y ⟨v,hv,eq⟩ => eq ▸ hmax hv⟩

/-- Unconditional endpoint localization of the entire actual image. The sole
dynamical hypothesis is the position-defined normal elastic-flow equation. -/
theorem fixedOriginRadius_localization (hf : c.IsNormalFEF) (O : ℂ) :
    Tendsto (fun t => c.fixedOriginRadius O t/(t^(1/3:ℝ)*Real.sqrt (Real.log (2+t))))
      atTop (𝓝 0) := by
  obtain ⟨C,ce⟩ := c.localization_position_envelope hf
  apply localization_optimization (C:=C+‖O‖) (c.localizationClock_subquadratic hf)
  · intro t ht
    obtain ⟨u,_,h⟩ := c.fixedOriginRadius_attained O (show 0≤t by linarith)
    rw [h]
    exact norm_nonneg _
  · intro t ht a ap a1
    obtain ⟨u,_,h⟩ := c.fixedOriginRadius_attained O (show 0≤t by linarith)
    rw [h]
    have norm := norm_sub_le (c.position t u) O
    linarith only [mul_le_mul_of_nonneg_left norm ap.le,ce t ht a ap a1 u,
      mul_le_mul_of_nonneg_right a1 (norm_nonneg O)]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.fixedOriginRadius_localization
