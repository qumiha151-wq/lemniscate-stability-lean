import SolitonClassification.Rotating.AnalyticMajorantScalar

/-! One kernel-checked rational scalar budget, shared by all local centers.
The exact finite residual is used; no analytic-series tail is assumed. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

def universalStepCap : ℚ := 1561/200000

def scalarValue60 : ℚ :=
  ∑ n ∈ Finset.range 61,scalarCoeff n*universalStepCap^n

def scalarDerivative60 : ℚ :=
  ∑ n ∈ Finset.range 61,scalarCoeff n*n*universalStepCap^(n-1)

def residualValue60 : ℚ := 61*scalarValue60^3-(19/2)*scalarDerivative60

theorem residualValue60_bound : 0≤residualValue60 ∧ residualValue60≤1/10^57 := by
  decide +kernel

theorem excursionValue60_bound : (19/2)*(scalarValue60-1)≤129/250 := by
  decide +kernel

lemma scalarPolynomial60_value :
    (scalarPolynomial 60).eval (universalStepCap:ℝ)=(scalarValue60:ℝ) := by
  simp [scalarPolynomial,scalarValue60,eval_finsetSum]

lemma scalarPolynomial60_derivative_value :
    (derivative (scalarPolynomial 60)).eval (universalStepCap:ℝ)=
      (scalarDerivative60:ℝ) := by
  simp [scalarPolynomial,scalarDerivative60,derivative_monomial,eval_finsetSum]

lemma scalarResidual60_value :
    (scalarResidual 60).eval (universalStepCap:ℝ)=(residualValue60:ℝ) := by
  simp only [scalarResidual,displacementPolynomial,derivative_mul,derivative_sub,
    derivative_C,derivative_one,zero_mul,zero_add,sub_zero,eval_sub,eval_mul,
    eval_C,eval_pow,scalarPolynomial60_value,scalarPolynomial60_derivative_value]
  simp only [residualValue60,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,
    Rat.cast_ofNat]

theorem scalarResidual60_uniform {t : ℝ} (ht : 0≤t)
    (hT : t≤(universalStepCap:ℝ)) :
    0≤(scalarResidual 60).eval t ∧ (scalarResidual 60).eval t≤1/10^57 := by
  have h:=scalarResidual_uniform 60 ht hT
  rw [scalarResidual60_value] at h
  have hb : (residualValue60:ℝ)≤1/10^57 := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr residualValue60_bound.2
    norm_num at hh ⊢
    exact hh
  exact ⟨h.1,h.2.trans hb⟩

theorem displacement60_uniform {t : ℝ} (ht : 0≤t)
    (hT : t≤(universalStepCap:ℝ)) :
    0≤(displacementPolynomial 60).eval t ∧
      (displacementPolynomial 60).eval t≤129/250 := by
  refine ⟨eval_nonneg_of_coeff_nonneg (displacementPolynomial_nonneg 60) ht,?_⟩
  have h:=eval_monotone_of_coeff_nonneg (displacementPolynomial_nonneg 60) ht hT
  apply h.trans
  simp only [displacementPolynomial,eval_mul,eval_C,eval_sub,eval_one,scalarPolynomial60_value]
  have hh := (Rat.cast_le (K:=ℝ)).mpr excursionValue60_bound
  push_cast at hh ⊢
  exact hh

theorem eval_abs_le_of_coeff_nonneg {p : ℝ[X]} (hp : ∀n,0≤p.coeff n) (t : ℝ) :
    |p.eval t|≤p.eval |t| := by
  rw [eval_eq_sum,eval_eq_sum,Polynomial.sum,Polynomial.sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n _
  simp only [abs_mul,abs_pow,abs_of_nonneg (hp n)]
  exact le_rfl

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.scalarResidual60_uniform
#print axioms SolitonClassification.Rotating.UniversalMajorant.displacement60_uniform

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (←collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked+1
  logInfo m!"Universal finite scalar budget audit passed: {checked} declarations; standard axioms only."
