import OpenTranslators.ParameterFlowClock
import Mathlib.Topology.Order.IntermediateValue

/-! The actual scalar parameter flow exists globally, is unique, and its
time slices are increasing bijections. Joint/spatial smoothness is separate. -/
namespace OpenTranslator.TranslatorParameter
noncomputable section
open Set Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

variable {z : ℝ → TranslatorState}
variable (hz : ∀ s, HasDerivAt z (translatorNumerator (z s)) s)

def parameterFlow (t u : ℝ) : ℝ :=
  (exists_unique_global_parameter_flow hz u).exists.choose t

theorem parameterFlow_zero (u : ℝ) : parameterFlow hz 0 u=u :=
  (exists_unique_global_parameter_flow hz u).exists.choose_spec.1

theorem parameterFlow_derivative (u t : ℝ) :
    HasDerivAt (fun s => parameterFlow hz s u)
      (parameterField z (parameterFlow hz t u)) t :=
  (exists_unique_global_parameter_flow hz u).exists.choose_spec.2 t

theorem parameterFlow_time_smooth (u : ℝ) :
    ContDiff ℝ ∞ (fun t => parameterFlow hz t u) :=
  smooth_integral_curve_of_smooth_field (parameterField_smooth hz)
    (parameterFlow_derivative hz u)

theorem parameterFlow_unique {φ : ℝ → ℝ} {u : ℝ} (hφ0 : φ 0=u)
    (hφ : ∀ t, HasDerivAt φ (parameterField z (φ t)) t) :
    φ=fun t => parameterFlow hz t u := by
  have hC1 : ContDiff ℝ 1 (parameterField z) := (parameterField_smooth hz).of_le (by simp)
  exact unique_global_of_locallyLipschitz hC1.locallyLipschitz hφ
    (parameterFlow_derivative hz u) (hφ0.trans (parameterFlow_zero hz u).symm)

theorem parameterFlow_add (s t u : ℝ) :
    parameterFlow hz (s+t) u=parameterFlow hz s (parameterFlow hz t u) := by
  have he : (fun r => parameterFlow hz (r+t) u)=
      fun r => parameterFlow hz r (parameterFlow hz t u) := by
    apply parameterFlow_unique hz
    · simp only [zero_add]
    · intro r
      convert (parameterFlow_derivative hz u (r+t)).comp r
        ((hasDerivAt_id r).add_const t) using 1 <;> first | rfl | simp
  exact congrFun he s

theorem parameterFlow_inverse (t u : ℝ) :
    parameterFlow hz (-t) (parameterFlow hz t u)=u := by
  rw [← parameterFlow_add,neg_add_cancel,parameterFlow_zero]

theorem parameterFlow_bijective (t : ℝ) : Function.Bijective (parameterFlow hz t) := by
  constructor
  · intro u v he
    have h := congrArg (parameterFlow hz (-t)) he
    simpa only [parameterFlow_inverse] using h
  · intro v
    refine ⟨parameterFlow hz (-t) v,?_⟩
    simpa only [neg_neg] using parameterFlow_inverse hz (-t) v

theorem parameterFlow_strictMono (t : ℝ) : StrictMono (parameterFlow hz t) := by
  intro u v huv
  by_contra hn
  have hle : parameterFlow hz t v-parameterFlow hz t u≤0 := by linarith
  have hpos : 0≤parameterFlow hz 0 v-parameterFlow hz 0 u := by
    rw [parameterFlow_zero,parameterFlow_zero]
    linarith
  have hc : Continuous (fun r => parameterFlow hz r v-parameterFlow hz r u) :=
    (parameterFlow_time_smooth hz v).continuous.sub (parameterFlow_time_smooth hz u).continuous
  obtain ⟨r,hr⟩ := intermediate_value_univ t 0 hc ⟨hle,hpos⟩
  have he : parameterFlow hz r v=parameterFlow hz r u := sub_eq_zero.mp hr
  exact huv.ne' ((parameterFlow_bijective hz r).1 he)

def parameterFlowOrderIso (t : ℝ) : ℝ ≃o ℝ :=
  (parameterFlow_strictMono hz t).orderIsoOfSurjective (parameterFlow hz t)
    (parameterFlow_bijective hz t).2

theorem parameterFlow_space_continuous (t : ℝ) : Continuous (parameterFlow hz t) :=
  (parameterFlowOrderIso hz t).toHomeomorph.continuous

theorem parameterFlow_time_distance (u s t : ℝ) :
    |parameterFlow hz t u-parameterFlow hz s u|≤|t-s| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r∈(univ : Set ℝ)) => (parameterFlow_derivative hz u r).hasDerivWithinAt)
    (fun r _ => parameterField_abs_le_one z (parameterFlow hz r u))
    convex_univ (mem_univ s) (mem_univ t)
  simpa only [Real.norm_eq_abs,one_mul] using h

theorem parameterFlow_displacement (u t : ℝ) : |parameterFlow hz t u-u|≤|t| := by
  simpa only [parameterFlow_zero,sub_zero] using parameterFlow_time_distance hz u 0 t

end
end OpenTranslator.TranslatorParameter

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Parameter flow audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Parameter flow audit passed for {count} declarations."
