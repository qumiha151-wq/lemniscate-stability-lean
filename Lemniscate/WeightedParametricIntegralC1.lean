import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic

/-! One derivative suffices for the scalar adjoint phase. A compact
spatial domain and an integrable fixed weight give both differentiation
under the integral and continuity of the actual derivative. -/
noncomputable section
namespace Lemniscate
open MeasureTheory Filter Set
open scoped Topology ContDiff

private theorem integrable_weighted_compact_row
    {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (μ : Measure X) (w : X → ℂ) (hw : Integrable w μ)
    (g : X → E) (hg : Continuous g) :
    Integrable (fun x => w x • g x) μ := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  exact hw.smul_bdd C hg.aestronglyMeasurable_of_compactSpace
    (Eventually.of_forall fun x => hC x (mem_univ x))

/-- A jointly continuous family with jointly continuous actual parameter
derivative has a C1 weighted integral on the open parameter domain.
The derivative is the actual integral of the weighted derivative. -/
theorem weighted_parametric_integral_c1
    {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (w : X → ℂ) (hw : Integrable w μ)
    (U : Set P) (hU : IsOpen U)
    (H : P × X → ℂ) (D : P × X → P →L[ℝ] ℂ)
    (hH : ContinuousOn H (U ×ˢ (univ : Set X)))
    (hD : ContinuousOn D (U ×ˢ (univ : Set X)))
    (hd : ∀ p ∈ U, ∀ x : X, HasFDerivAt (fun q : P => H (q,x)) (D (p,x)) p) :
    ContDiffOn ℝ 1 (fun p : P => ∫ x, w x*H (p,x) ∂μ) U ∧
      ∀ p ∈ U, HasFDerivAt (fun q : P => ∫ x, w x*H (q,x) ∂μ)
        (∫ x, w x • D (p,x) ∂μ) p := by
  have hHrow (p : P) (hp : p ∈ U) : Continuous (fun x : X => H (p,x)) :=
    hH.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hp,mem_univ x⟩)
  have hDrow (p : P) (hp : p ∈ U) : Continuous (fun x : X => D (p,x)) :=
    hD.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hp,mem_univ x⟩)
  have hHintegrable (p : P) (hp : p ∈ U) :
      Integrable (fun x => w x*H (p,x)) μ := by
    simpa only [smul_eq_mul] using
      integrable_weighted_compact_row μ w hw (fun x => H (p,x)) (hHrow p hp)
  have hDintegrable (p : P) (hp : p ∈ U) :
      Integrable (fun x => w x • D (p,x)) μ :=
    integrable_weighted_compact_row μ w hw (fun x => D (p,x)) (hDrow p hp)
  have hDcontinuous : ContinuousOn (fun p : P => ∫ x, w x • D (p,x) ∂μ) U := by
    simpa only [ContinuousLinearMap.lsmul_apply] using
      (continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
        (ContinuousLinearMap.lsmul ℝ ℂ :
          ℂ →L[ℝ] (P →L[ℝ] ℂ) →L[ℝ] (P →L[ℝ] ℂ))
        (μ := μ) (f := fun p x => D (p,x)) (s := U) (g := w)
        isCompact_univ (by simpa only [Function.uncurry] using! hD)
        (fun p x hp hx => (hx (mem_univ x)).elim) (by simpa using hw))
  have hderivative (p : P) (hp : p ∈ U) :
      HasFDerivAt (fun q : P => ∫ x, w x*H (q,x) ∂μ)
        (∫ x, w x • D (p,x) ∂μ) p := by
    obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hDrow p hp).continuousOn
    obtain ⟨A,hA,hclose⟩ := isCompact_univ.mem_uniformity_of_prod
      (f := fun q x => D (q,x))
      (by simpa only [Function.uncurry] using! hD) hp
      (Metric.dist_mem_uniformity (by norm_num : (0:ℝ) < 1))
    rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hp)] at hA
    have hS : U ∩ A ∈ 𝓝 p := inter_mem (hU.mem_nhds hp) hA
    have hlocal (q : P) (hq : q ∈ A) (x : X) : ‖D (q,x)‖ ≤ C+1 := by
      have hh := norm_le_norm_sub_add (D (q,x)) (D (p,x))
      have hbase := hC x (mem_univ x)
      have hc : ‖D (q,x)-D (p,x)‖ < 1 := by
        simpa only [dist_eq_norm] using! hclose q hq x (mem_univ x)
      linarith only [hh,hbase,hc]
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun q x => w x*H (q,x)) (F' := fun q x => w x • D (q,x))
      (s := U ∩ A) (bound := fun x => ‖w x‖*(C+1)) hS
    · filter_upwards [hU.mem_nhds hp] with q hq
      exact (hHintegrable q hq).aestronglyMeasurable
    · exact hHintegrable p hp
    · exact (hDintegrable p hp).aestronglyMeasurable
    · apply Eventually.of_forall
      intro x q hq
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hlocal q hq.2 x) (norm_nonneg (w x))
    · exact hw.norm.mul_const (C+1)
    · apply Eventually.of_forall
      intro x q hq
      exact (hd q hq.1 x).const_mul (w x)
  refine ⟨?_,hderivative⟩
  have hc : ContDiffOn ℝ ((0:ℕ∞ω)+1) (fun p : P => ∫ x, w x*H (p,x) ∂μ) U :=
    (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (𝕜 := ℝ) (n := (0:ℕ∞ω)) hU.uniqueDiffOn).mpr
      ⟨by simp,fun p => ∫ x, w x • D (p,x) ∂μ,
        contDiffOn_zero.mpr hDcontinuous,fun p hp => (hderivative p hp).hasFDerivWithinAt⟩
  simpa only [zero_add] using hc

end Lemniscate
