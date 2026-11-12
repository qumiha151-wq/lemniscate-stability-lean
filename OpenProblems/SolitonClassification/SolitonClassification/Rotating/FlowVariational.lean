import SolitonClassification.Rotating.FlowJoint
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The first variational equation for the actual initial-state derivative.
It is obtained by differentiating the actual ODE integral equation in the
initial state. No numerically computed fundamental matrix is identified
with this derivative without a separate proof. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff
set_option backward.isDefEq.respectTransparency false

def flowLinearCoefficient (σ : ℝ) (hσ : |σ|≤1) (a : State) (t : ℝ) : State →L[ℝ] State :=
  σ • fderiv ℝ field (supportFlow σ hσ t a)

def flowVariationalIntegrand (σ : ℝ) (hσ : |σ|≤1) (a : State) (t : ℝ) : State →L[ℝ] State :=
  (flowLinearCoefficient σ hσ a t).comp (fderiv ℝ (supportFlow σ hσ t) a)

theorem flowLinearCoefficient_continuous (σ : ℝ) (hσ : |σ|≤1) (a : State) :
    Continuous (flowLinearCoefficient σ hσ a) := by
  have hc : Continuous (fderiv ℝ field) := field_smooth.continuous_fderiv (by simp)
  exact (hc.comp (supportFlow_time_lipschitz σ hσ a).continuous).const_smul σ

theorem supportFlow_fderiv_time_continuousOn (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) :
    ContinuousOn (fun t => fderiv ℝ (supportFlow σ hσ t) a) (Icc 0 T) := by
  have hLip : LipschitzOnWith ⟨17*Real.exp (17*T),by positivity⟩
      (fun t => fderiv ℝ (supportFlow σ hσ t) a) (Icc 0 T) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro s hs t ht
    change dist _ _≤(17*Real.exp (17*T))*dist s t
    simpa only [dist_eq_norm] using supportFlow_fderiv_time_variation σ hσ T ht hs
      (supportFlow_hasFDerivAt_initial σ hσ hreg ha ht).differentiableAt
      (supportFlow_hasFDerivAt_initial σ hσ hreg ha hs).differentiableAt
  exact hLip.continuousOn

theorem flowVariationalIntegrand_continuousOn (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) :
    ContinuousOn (flowVariationalIntegrand σ hσ a) (Icc 0 T) :=
  (flowLinearCoefficient_continuous σ hσ a).continuousOn.clm_comp
    (supportFlow_fderiv_time_continuousOn σ hσ hreg ha)

theorem flowVariationalIntegrand_bound (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Icc 0 T) :
    ‖flowVariationalIntegrand σ hσ a t‖≤17*Real.exp (17*T) := by
  have hP := norm_fderiv_le_of_lipschitz ℝ (x₀:=a) (supportFlow_initial_lipschitz σ hσ ht.1)
  have hP' : ‖fderiv ℝ (supportFlow σ hσ t) a‖≤Real.exp (17*T) :=
    hP.trans (Real.exp_le_exp.mpr (by linarith [ht.2]))
  have hA : ‖flowLinearCoefficient σ hσ a t‖≤17 := by
    rw [flowLinearCoefficient,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hσ (field_fderiv_bound (hreg a ha t ht)) (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul 17)
  exact ((flowLinearCoefficient σ hσ a t).opNorm_comp_le _).trans
    (mul_le_mul hA hP' (norm_nonneg _) (by norm_num))

theorem actualField_integral_eq (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Icc 0 T) :
    (∫s in (0:ℝ)..t,σ • field (supportFlow σ hσ s a))=supportFlow σ hσ t a-a := by
  have hc : Continuous (fun s => σ • field (supportFlow σ hσ s a)) :=
    (field_smooth.continuous.comp (supportFlow_time_lipschitz σ hσ a).continuous).const_smul σ
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=t)
    (fun s hs => supportFlow_original_derivative σ hσ a s (hreg a ha s (by
      rw [uIcc_of_le ht.1] at hs
      exact ⟨hs.1,hs.2.trans ht.2⟩))) (hc.intervalIntegrable 0 t)
  simpa only [supportFlow_zero] using hi

/-- This integral identity is for the genuine initial derivative constructed
from difference quotients. It derives, rather than assumes, the first
variational equation. -/
theorem supportFlow_fderiv_integral (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Icc 0 T) :
    fderiv ℝ (supportFlow σ hσ t) a=ContinuousLinearMap.id ℝ State+
      ∫s in (0:ℝ)..t,flowVariationalIntegrand σ hσ a s := by
  let F : State → ℝ → State := fun b s => σ • field (supportFlow σ hσ s b)
  have hFc (b : State) : Continuous (F b) :=
    (field_smooth.continuous.comp (supportFlow_time_lipschitz σ hσ b).continuous).const_smul σ
  have hs : Metric.ball c R∈𝓝 a := Metric.isOpen_ball.mem_nhds ha
  have hsub : uIoc (0:ℝ) t⊆Icc 0 T := by
    rw [uIoc_of_le ht.1]
    intro s hs
    exact ⟨hs.1.le,hs.2.trans ht.2⟩
  have hD : HasFDerivAt (fun b => ∫s in (0:ℝ)..t,F b s)
      (∫s in (0:ℝ)..t,flowVariationalIntegrand σ hσ a s) a := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (F':=fun b s => flowVariationalIntegrand σ hσ b s)
      (bound:=fun _ => 17*Real.exp (17*T)) hs
    · exact Filter.Eventually.of_forall fun b => (hFc b).aestronglyMeasurable
    · exact (hFc a).intervalIntegrable 0 t
    · exact ((flowVariationalIntegrand_continuousOn σ hσ hreg ha).mono hsub).aestronglyMeasurable
        measurableSet_uIoc
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs b hb
      exact flowVariationalIntegrand_bound σ hσ hreg hb (hsub hs)
    · exact intervalIntegrable_const
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs b hb
      have hd := ((field_smooth.differentiable (by simp) (supportFlow σ hσ s b)).hasFDerivAt.comp b
        (supportFlow_hasFDerivAt_initial σ hσ hreg hb (hsub hs))).const_smul σ
      convert! hd using 1
  have he : (fun b => ∫s in (0:ℝ)..t,F b s)=ᶠ[𝓝 a] fun b => supportFlow σ hσ t b-b := by
    filter_upwards [hs] with b hb
    exact actualField_integral_eq σ hσ hreg hb ht
  have hD' := hD.congr_of_eventuallyEq he.symm
  have hTrue := (supportFlow_hasFDerivAt_initial σ hσ hreg ha ht).sub (hasFDerivAt_id a)
  have hu := hD'.unique hTrue
  rw [hu]
  abel

theorem supportFlow_fderiv_initial (σ : ℝ) (hσ : |σ|≤1) (a : State) :
    fderiv ℝ (supportFlow σ hσ 0) a=ContinuousLinearMap.id ℝ State := by
  have he : supportFlow σ hσ 0=id := funext (supportFlow_zero σ hσ)
  rw [he]
  exact fderiv_id

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating first-variation audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating first-variation audit passed for {count} declarations."
