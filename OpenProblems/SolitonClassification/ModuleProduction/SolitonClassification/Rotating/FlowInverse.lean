module

public import SolitonClassification.Rotating.QuantitativeVariation
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Ring.Units

@[expose] public section

/-! The genuine variational matrix is invertible by backwards uniqueness
for its actual linear ODE. Its canonical ring inverse is continuous; no
inverse matrix or invertibility premise is supplied independently. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

theorem supportFlow_fderiv_hasDerivWithinAt_left (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Ioc 0 T) :
    HasDerivWithinAt (fun s => fderiv ℝ (supportFlow σ hσ s) a)
      ((flowLinearCoefficient σ hσ a t).comp (fderiv ℝ (supportFlow σ hσ t) a)) (Iic t) t := by
  have hc := flowVariationalIntegrand_continuousOn σ hσ hreg ha
  have hn : Icc (0:ℝ) T∈𝓝[Iic t] t :=
    Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (fun _ hs => ⟨hs.1,hs.2.trans ht.2⟩)
  have hint : IntervalIntegrable (flowVariationalIntegrand σ hσ a) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    apply hc.mono
    rw [uIcc_of_le ht.1.le]
    exact Icc_subset_Icc_right ht.2
  have hmeas : StronglyMeasurableAtFilter (flowVariationalIntegrand σ hσ a) (𝓝[Iic t] t) volume :=
    ⟨Icc 0 T,hn,hc.aestronglyMeasurable measurableSet_Icc⟩
  have hi := intervalIntegral.integral_hasDerivWithinAt_right (s:=Iic t) (t:=Iic t)
    hint hmeas ((hc t ⟨ht.1.le,ht.2⟩).mono_of_mem_nhdsWithin hn)
  have he : (fun s => fderiv ℝ (supportFlow σ hσ s) a)=ᶠ[𝓝[Iic t] t]
      fun s => ContinuousLinearMap.id ℝ State+∫u in (0:ℝ)..s,flowVariationalIntegrand σ hσ a u := by
    filter_upwards [hn] with s hs
    exact supportFlow_fderiv_integral σ hσ hreg ha hs
  exact (hi.const_add (ContinuousLinearMap.id ℝ State)).congr_of_eventuallyEq_of_mem he (le_refl t)

theorem supportFlow_fderiv_injective (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Icc 0 T) :
    Function.Injective (fderiv ℝ (supportFlow σ hσ t) a) := by
  let P : ℝ → State →L[ℝ] State := fun s => fderiv ℝ (supportFlow σ hσ s) a
  let A := flowLinearCoefficient σ hσ a
  have hc := supportFlow_fderiv_time_continuousOn σ hσ hreg ha
  have hsub : Icc 0 t⊆Icc 0 T := Icc_subset_Icc_right ht.2
  have hLip : ∀s∈Ioc 0 t,LipschitzOnWith 17 (A s) (univ : Set State) := by
    intro s hs
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [dist_eq_norm,←map_sub,NNReal.coe_ofNat]
    exact ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (flowLinearCoefficient_bound σ hσ (hreg a ha s ⟨hs.1.le,hs.2.trans ht.2⟩)) (norm_nonneg _))
  intro u v huv
  have hleft : ∀s∈Ioc 0 t,HasDerivWithinAt (fun s => P s (u-v))
      (A s (P s (u-v))) (Iic s) s := by
    intro s hs
    have hd := (supportFlow_fderiv_hasDerivWithinAt_left σ hσ hreg ha
      ⟨hs.1,hs.2.trans ht.2⟩).clm_apply (hasDerivWithinAt_const s (Iic s) (u-v))
    simpa only [ContinuousLinearMap.comp_apply,map_zero,add_zero] using hd
  have hz : ∀s∈Ioc 0 t,HasDerivWithinAt (fun _ : ℝ => (0:State)) (A s 0) (Iic s) s := by
    intro s hs
    simpa only [map_zero] using hasDerivWithinAt_const s (Iic s) (0:State)
  have he := ODE_solution_unique_of_mem_Icc_left (v:=fun s x => A s x) (s:=fun _ => univ)
    hLip ((hc.mono hsub).clm_apply continuousOn_const) hleft (by intros; trivial)
    continuousOn_const hz (by intros; trivial)
    (show P t (u-v)=0 by simp only [P,map_sub,huv,sub_self])
  have hh := he ⟨le_rfl,ht.1⟩
  simpa only [P,supportFlow_fderiv_initial,ContinuousLinearMap.id_apply,sub_eq_zero] using hh

theorem supportFlow_fderiv_isUnit (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Icc 0 T) :
    IsUnit (fderiv ℝ (supportFlow σ hσ t) a) := by
  have hi := supportFlow_fderiv_injective σ hσ hreg ha ht
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi,(LinearMap.injective_iff_surjective (f:=(fderiv ℝ (supportFlow σ hσ t) a).toLinearMap)).mp hi⟩

/-- The canonical inverse of the actual initial-state derivative. It is
only asserted to be an inverse where actual tube hypotheses are proved. -/
def supportFlowInverse (σ : ℝ) (hσ : |σ|≤1) (a : State) (t : ℝ) : State →L[ℝ] State :=
  Ring.inverse (fderiv ℝ (supportFlow σ hσ t) a)

theorem supportFlow_fderiv_comp_inverse (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Icc 0 T) :
    (fderiv ℝ (supportFlow σ hσ t) a).comp (supportFlowInverse σ hσ a t)=
      ContinuousLinearMap.id ℝ State :=
  Ring.mul_inverse_cancel _ (supportFlow_fderiv_isUnit σ hσ hreg ha ht)

theorem supportFlow_inverse_comp_fderiv (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Icc 0 T) :
    (supportFlowInverse σ hσ a t).comp (fderiv ℝ (supportFlow σ hσ t) a)=
      ContinuousLinearMap.id ℝ State :=
  Ring.inverse_mul_cancel _ (supportFlow_fderiv_isUnit σ hσ hreg ha ht)

theorem supportFlow_inverse_continuousOn (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) :
    ContinuousOn (supportFlowInverse σ hσ a) (Icc 0 T) := by
  intro t ht
  obtain ⟨u,hu⟩ := supportFlow_fderiv_isUnit σ hσ hreg ha ht
  have hc := NormedRing.inverse_continuousAt u
  rw [hu] at hc
  exact hc.comp_continuousWithinAt (f:=fun s : ℝ => fderiv ℝ (supportFlow σ hσ s) a)
    (supportFlow_fderiv_time_continuousOn σ hσ hreg ha t ht)

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual inverse audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual inverse audit passed for {count} declarations."

end
