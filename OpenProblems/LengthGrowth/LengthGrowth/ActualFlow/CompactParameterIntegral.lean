import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Fixed-parameter scalar integration for an actual moving-curve calculation.
All domination constants below are derived from continuity on compact products.
There is no flow structure, assumed integral identity, or supplied bound here.
The compact-product proof pattern was also used in the independently developed
OpenTranslators.ParameterHigher; this module imports only Mathlib.
-/

namespace LengthGrowth.ActualFlow

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private theorem continuousOn_space_slice {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    {a b t : ℝ} (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ uIcc a b))
    (ht : t ∈ I) : ContinuousOn (F t) (uIcc a b) :=
  hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hu => ⟨ht, hu⟩)

private theorem continuousOn_time_slice {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    {a b u : ℝ} (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ uIcc a b))
    (hu : u ∈ uIcc a b) : ContinuousOn (fun t => F t u) I :=
  hF.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨ht, hu⟩)

/-- Spatial integrability on the fixed compact parameter interval. -/
theorem intervalIntegrable_parameter_slice {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    {a b t : ℝ} (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ uIcc a b))
    (ht : t ∈ I) : IntervalIntegrable (F t) volume a b :=
  (continuousOn_space_slice hF ht).intervalIntegrable

/-- Continuity up to both endpoints of any compact time set; no time derivative is required. -/
theorem continuousOn_intervalIntegral_of_isCompact {K : Set ℝ} {F : ℝ → ℝ → ℝ}
    {a b : ℝ} (hK : IsCompact K)
    (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (K ×ˢ uIcc a b)) :
    ContinuousOn (fun t => ∫ u in a..b, F t u) K := by
  obtain ⟨M, hM⟩ := (hK.prod isCompact_uIcc).bddAbove_image hF.norm
  intro t ht
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => M)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact ((continuousOn_space_slice hF hx).mono uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact ae_of_all _ fun u hu => hM (mem_image_of_mem
      (fun z : ℝ × ℝ => ‖F z.1 z.2‖)
      (show (x, u) ∈ K ×ˢ uIcc a b from ⟨hx, uIoc_subset_uIcc hu⟩))
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun u hu =>
      continuousOn_time_slice hF (uIoc_subset_uIcc hu) t ht

/-- A closed forward time slab is covered without any backwards extension. -/
theorem continuousOn_intervalIntegral_on_closed_slab {F : ℝ → ℝ → ℝ}
    {a b c d : ℝ}
    (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (Icc c d ×ˢ uIcc a b)) :
    ContinuousOn (fun t => ∫ u in a..b, F t u) (Icc c d) :=
  continuousOn_intervalIntegral_of_isCompact isCompact_Icc hF

/-- Continuity on an open time domain needs only joint continuity. -/
theorem continuousOn_intervalIntegral_of_isOpen {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    {a b : ℝ} (hI : IsOpen I)
    (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ uIcc a b)) :
    ContinuousOn (fun t => ∫ u in a..b, F t u) I := by
  intro t ht
  obtain ⟨r, hr, hrI⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds ht)
  have hc := continuousOn_intervalIntegral_of_isCompact (isCompact_closedBall t r)
    (hF.mono (show Metric.closedBall t r ×ˢ uIcc a b ⊆ I ×ˢ uIcc a b from
      fun _ hz => ⟨hrI hz.1, hz.2⟩))
  exact ((hc t (Metric.mem_closedBall_self hr.le)).continuousAt
    (Metric.closedBall_mem_nhds t hr)).continuousWithinAt

/-- A true time derivative passes through the fixed interval integral. The bound
on the derivative is obtained from a compact time neighborhood, not assumed. -/
theorem hasDerivAt_intervalIntegral_of_continuousOn {I : Set ℝ}
    {F D : ℝ → ℝ → ℝ} {a b t : ℝ} (hI : IsOpen I)
    (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ uIcc a b))
    (hD : ContinuousOn (fun z : ℝ × ℝ => D z.1 z.2) (I ×ˢ uIcc a b))
    (hd : ∀ x ∈ I, ∀ u ∈ uIcc a b, HasDerivAt (fun y => F y u) (D x u) x)
    (ht : t ∈ I) :
    HasDerivAt (fun x => ∫ u in a..b, F x u) (∫ u in a..b, D t u) t := by
  obtain ⟨r, hr, hrI⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds ht)
  have hDc : ContinuousOn (fun z : ℝ × ℝ => D z.1 z.2)
      (Metric.closedBall t r ×ˢ uIcc a b) :=
    hD.mono (fun _ hz => ⟨hrI hz.1, hz.2⟩)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t r).prod isCompact_uIcc).bddAbove_image hDc.norm
  have hset : HasDerivAt (fun x => ∫ u in uIoc a b, F x u)
      (∫ u in uIoc a b, D t u) t := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (uIoc a b))
      (F' := D) (bound := fun _ => M)
      (s := Metric.closedBall t r) (Metric.closedBall_mem_nhds t hr) ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards [hI.mem_nhds ht] with x hx
      exact ((continuousOn_space_slice hF hx).mono uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc
    · exact (intervalIntegrable_parameter_slice hF ht).def'
    · exact ((continuousOn_space_slice hD ht).mono uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu x hx
      exact hM (mem_image_of_mem (fun z : ℝ × ℝ => ‖D z.1 z.2‖)
        (show (x, u) ∈ Metric.closedBall t r ×ˢ uIcc a b from
          ⟨hx, uIoc_subset_uIcc hu⟩))
    · exact (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume a b).def'
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu x hx
      exact hd x (hrI hx) u (uIoc_subset_uIcc hu)
  simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul] using
    hset.const_mul (if a ≤ b then (1 : ℝ) else -1)

/-- Open-time continuity follows from the proved integral derivative. -/
theorem continuousOn_intervalIntegral_of_time_derivative {I : Set ℝ}
    {F D : ℝ → ℝ → ℝ} {a b : ℝ} (hI : IsOpen I)
    (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ uIcc a b))
    (hD : ContinuousOn (fun z : ℝ × ℝ => D z.1 z.2) (I ×ˢ uIcc a b))
    (hd : ∀ x ∈ I, ∀ u ∈ uIcc a b, HasDerivAt (fun y => F y u) (D x u) x) :
    ContinuousOn (fun x => ∫ u in a..b, F x u) I := by
  intro t ht
  exact (hasDerivAt_intervalIntegral_of_continuousOn hI hF hD hd ht).continuousAt.continuousWithinAt

/-- The derivative family can be the actual `deriv`, rather than a supplied field. -/
theorem hasDerivAt_intervalIntegral_actualTimeDeriv {I : Set ℝ}
    {F : ℝ → ℝ → ℝ} {a b t : ℝ} (hI : IsOpen I)
    (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ uIcc a b))
    (hD : ContinuousOn (fun z : ℝ × ℝ => deriv (fun x => F x z.2) z.1)
      (I ×ˢ uIcc a b))
    (hd : ∀ x ∈ I, ∀ u ∈ uIcc a b, DifferentiableAt ℝ (fun y => F y u) x)
    (ht : t ∈ I) :
    HasDerivAt (fun x => ∫ u in a..b, F x u)
      (∫ u in a..b, deriv (fun x => F x u) t) t :=
  hasDerivAt_intervalIntegral_of_continuousOn hI hF hD
    (fun x hx u hu => (hd x hx u hu).hasDerivAt) ht

/-- Joint C1 regularity on the open time domain supplies all actual partial
derivatives and their continuity; no derivative family is an extra premise. -/
theorem hasDerivAt_intervalIntegral_of_jointC1 {I : Set ℝ}
    {F : ℝ → ℝ → ℝ} {a b t : ℝ} (hI : IsOpen I)
    (hF : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    (ht : t ∈ I) :
    HasDerivAt (fun x => ∫ u in a..b, F x u)
      (∫ u in a..b, deriv (fun x => F x u) t) t := by
  let D : ℝ → ℝ → ℝ := fun x u =>
    (fderiv ℝ (fun z : ℝ × ℝ => F z.1 z.2) (x, u)) (1, 0)
  have hD : ContinuousOn (fun z : ℝ × ℝ => D z.1 z.2)
      (I ×ˢ (univ : Set ℝ)) :=
    (hF.continuousOn_fderiv_of_isOpen (hI.prod isOpen_univ) le_rfl).clm_apply
      continuousOn_const
  have hd (x : ℝ) (hx : x ∈ I) (u : ℝ) :
      HasDerivAt (fun y => F y u) (D x u) x := by
    have hfd : DifferentiableAt ℝ (fun z : ℝ × ℝ => F z.1 z.2) (x, u) :=
      (hF.differentiableOn (by norm_num) (x, u) ⟨hx, mem_univ u⟩).differentiableAt
        ((hI.prod isOpen_univ).mem_nhds ⟨hx, mem_univ u⟩)
    have hp : HasDerivAt (fun y : ℝ => (y, u)) (1, 0) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x u)
    exact hfd.hasFDerivAt.comp_hasDerivAt x hp
  have hsub : I ×ˢ uIcc a b ⊆ I ×ˢ (univ : Set ℝ) :=
    fun _ hz => ⟨hz.1, mem_univ _⟩
  have hi := hasDerivAt_intervalIntegral_of_continuousOn hI
    (hF.continuousOn.mono hsub) (hD.mono hsub) (fun x hx u _ => hd x hx u) ht
  convert hi using 1
  apply intervalIntegral.integral_congr
  intro u _
  exact (hd t ht u).deriv

end
end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Compact parameter integral audit passed: {checked} declarations; standard axioms only."
