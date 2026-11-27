import SolitonClassification.CrossingStressResponse
import SolitonClassification.CrossingParity
import SolitonClassification.PhysicalSeamScale
import SolitonClassification.StrongCentreMarker

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ClosedSimilarity.CrossingResponse
open GlobalSupport

/-- The zero-parameter central shot agrees with any standard quartic
    oscillator started at curvature zero and unit slope. -/
theorem frozen_eq_oscillator (U w : ℝ → ℝ) (hU : U 0 = 0) (hw : w 0 = 1)
    (dU : ∀ t, HasDerivAt U (w t) t) (dw : ∀ t, HasDerivAt w (-(U t)^3/2) t) :
    K 0 = U ∧ V 0 = w := by
  let z := fun t : ℝ => (![U t,w t,0,0] : Phase)
  have dz (t : ℝ) : HasDerivAt z (rhs 0 (z t)) t := by
    apply hasDerivAt_pi.mpr
    intro i; fin_cases i
    · exact dU t
    · simpa [z,rhs] using dw t
    · simpa [z,rhs] using hasDerivAt_const t (0:ℝ)
    · simpa [z,rhs] using hasDerivAt_const t (0:ℝ)
  have same := (exists_unique_solution 0 (![0,1,0,0] : Phase)).unique
    (show solution 0 ![0,1,0,0] 0 = _ ∧ _ from ⟨solution_zero ..,solution_derivative 0 _⟩)
    (show z 0 = _ ∧ _ from ⟨by simp [z,hU,hw],dz⟩)
  exact ⟨funext (fun t => congrFun (congrFun same t) 0),
    funext (fun t => congrFun (congrFun same t) 1)⟩

/-- A closed physical expander marked by its centre slope has exactly the
    fast central support shot used in the response computation. -/
theorem physical_fast_support {L b : ℝ} (P : ReflectedArc.ZeroTurnExpander L b)
    (pos : 0 < b) (t : ℝ) :
    P.cartesianSupport (t / Real.sqrt b) =
      restore (Real.sqrt b) (shot ((b^2)⁻¹) t) := by
  have r := Real.sqrt_pos.mpr pos
  have sq := Real.sq_sqrt pos.le
  have scale : (Real.sqrt b)^4 * (b^2)⁻¹ = 1 := by
    rw [show (Real.sqrt b)^4 = ((Real.sqrt b)^2)^2 by ring, sq]
    exact mul_inv_cancel₀ (pow_ne_zero _ pos.ne')
  have initial : restore (Real.sqrt b) ![0,1,0,0] = ![0,b,0,0] := by
    funext i; fin_cases i <;> simp [restore,sq]
  have h := physical_support_conjugacy scale ![0,1,0,0] (t/Real.sqrt b)
  rw [initial, show Real.sqrt b*(t/Real.sqrt b) = t by field_simp] at h
  exact (congrFun P.cartesianSupport_eq_solution _).trans h

private theorem frozen_rate :
    horizontalRate 0 = CrossingParity.horizontalRate (K 0) (V 0) (Y 0) := by
  funext t
  unfold horizontalRate CrossingParity.horizontalRate
  rw [frozen_positionX,(frozen_tangent t).1,(frozen_tangent t).2]
  ring

/-- The actual centre-shot stress variation is determined at any limiting
    inflection time even when the moving endpoint is only continuous. -/
theorem actual_response_at_zero (r : ℝ → ℝ) (hr : ContinuousAt r 0)
    (root : K 0 (r 0) = 0) :
    HasDerivAt (fun e => stressX e (r e)) (-(∫ t in (0:ℝ)..r 0, K 0 t ^ 5) / 3) 0 := by
  obtain ⟨cw, dU, dG, zero⟩ := frozen_data
  have h := stressX_response r hr
  rw [frozen_rate, CrossingParity.integral_horizontalRate_of_zeros (K 0) (V 0) (Y 0) cw dU dG zero root] at h
  exact h

/-- The stress divided by the parameter has its limit simultaneously in
    time and in the nonzero parameter. No rate or chosen root map occurs. -/
theorem joint_response_quotient {a : ℝ} (root : K 0 a = 0) :
    Tendsto (fun z : ℝ × ℝ => stressX z.1 z.2 / z.1)
      (𝓝[{z : ℝ × ℝ | z.1 ≠ 0}] ((0:ℝ),a))
      (𝓝 (-(∫ t in (0:ℝ)..a, K 0 t ^ 5) / 3)) := by
  let A := fun z : ℝ × ℝ => ∫ t in (0:ℝ)..z.2, horizontalRate z.1 t
  have c : Continuous (fun z : (ℝ × ℝ) × ℝ => horizontalRate z.1.1 z.2) :=
    horizontalRate_cont.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have cA : Continuous A := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) (f := fun z : ℝ × ℝ => horizontalRate z.1) c continuous_snd
  obtain ⟨cw, dU, dG, zero⟩ := frozen_data
  have atZero : A (0,a) = -(∫ t in (0:ℝ)..a, K 0 t ^ 5) / 3 := by
    change (∫ t in (0:ℝ)..a, horizontalRate 0 t) = _
    rw [frozen_rate, CrossingParity.integral_horizontalRate_of_zeros (K 0) (V 0) (Y 0) cw dU dG zero root]
  rw [← atZero]
  apply Tendsto.congr' _ ((cA.tendsto (0,a)).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with z hz
  change z.1 ≠ 0 at hz
  rw [stressX_exact, mul_div_cancel_left₀ _ hz]
  rfl

end ClosedSimilarity.CrossingResponse
#print axioms ClosedSimilarity.CrossingResponse.frozen_eq_oscillator
#print axioms ClosedSimilarity.CrossingResponse.physical_fast_support
#print axioms ClosedSimilarity.CrossingResponse.actual_response_at_zero
#print axioms ClosedSimilarity.CrossingResponse.joint_response_quotient
