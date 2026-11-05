import Lemniscate.WeightedParametricIntegralC1
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The scalar phase of a normal graph needs only one parameter derivative.
The angular height derivative is supplied by the geometric phase variation. -/
noncomputable section
namespace Lemniscate
open MeasureTheory Filter Set
open scoped Topology ContDiff

/-- The real weighted phase is C1, and its actual angular derivative is
minus the weighted geometric rotation field. The pointwise angular
height derivative is an input, rather than a derivative of the phase. -/
theorem normal_graph_phase_integral
    {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (w : X → ℂ) (hw : Integrable w μ)
    (U : Set (P × ℝ)) (hU : IsOpen U)
    (H G : (P × ℝ) × X → ℂ)
    (D : (P × ℝ) × X → (P × ℝ) →L[ℝ] ℂ)
    (hH : ContinuousOn H (U ×ˢ (univ : Set X)))
    (hD : ContinuousOn D (U ×ˢ (univ : Set X)))
    (hd : ∀ q ∈ U, ∀ x : X,
      HasFDerivAt (fun z : P × ℝ => H (z,x)) (D (q,x)) q)
    (hangle : ∀ q ∈ U, ∀ x : X,
      HasDerivAt (fun θ => H ((q.1,θ),x)) (-G (q,x)) q.2) :
    ContDiffOn ℝ 1 (fun q : P × ℝ => (∫ x, w x*H (q,x) ∂μ).re) U ∧
      ∀ p θ, (p,θ) ∈ U →
        HasDerivAt (fun a => (∫ x, w x*H ((p,a),x) ∂μ).re)
          (-(∫ x, w x*G ((p,θ),x) ∂μ).re) θ := by
  obtain ⟨hC,hIntegral⟩ := weighted_parametric_integral_c1 μ w hw U hU H D hH hD hd
  refine ⟨?_,?_⟩
  · have hRe : ContDiff ℝ 1 (fun z : ℂ => z.re) := Complex.reCLM.contDiff
    simpa only [Function.comp_def] using hRe.comp_contDiffOn hC
  · intro p θ hq
    have hparam : HasDerivAt (fun a : ℝ => (p,a)) ((0:P),1) θ :=
      (hasDerivAt_const θ p).prodMk (hasDerivAt_id θ)
    have hpoint (x : X) : D ((p,θ),x) ((0:P),1) = -G ((p,θ),x) :=
      ((hd (p,θ) hq x).comp_hasDerivAt θ hparam).unique (hangle (p,θ) hq x)
    have hrow : Continuous (fun x : X => D ((p,θ),x)) :=
      hD.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x => ⟨hq,mem_univ x⟩)
    obtain ⟨C,hCbound⟩ := isCompact_univ.exists_bound_of_continuousOn hrow.continuousOn
    have hint : Integrable (fun x => w x • D ((p,θ),x)) μ :=
      hw.smul_bdd C hrow.aestronglyMeasurable_of_compactSpace
        (Eventually.of_forall fun x => hCbound x (mem_univ x))
    have hvalue : (∫ x, w x • D ((p,θ),x) ∂μ) ((0:P),1) =
        -(∫ x, w x*G ((p,θ),x) ∂μ) := by
      rw [ContinuousLinearMap.integral_apply hint]
      calc
        _ = ∫ x, -(w x*G ((p,θ),x)) ∂μ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            simp only [smul_apply,hpoint x,smul_eq_mul,mul_neg]
        _ = _ := integral_neg _
    have hdir := (hIntegral (p,θ) hq).comp_hasDerivAt θ hparam
    have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ hdir
    simpa only [Function.comp_def,Complex.reCLM_apply,hvalue,Complex.neg_re] using hreal

end Lemniscate
