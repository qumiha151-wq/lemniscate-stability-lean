import SolitonClassification.Rotating.UniversalPolynomialTube
import SolitonClassification.Rotating.UniversalTaylorResidual
import SolitonClassification.Rotating.SignedLocalTail

/-! A universal, two-sided actual-flow order-60 truncation bound. The
numeric scalar budget is checked once and applies to every inner-tube
center. No per-center residual data or assumed solution tube is needed. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Set
set_option Elab.async false

theorem universalStepCap_pos : (0:ℝ)<(universalStepCap:ℝ) := by
  norm_num [universalStepCap]

theorem universalStepCap_le_local : (universalStepCap:ℝ)≤1/125 := by
  norm_num [universalStepCap]

theorem taylorPolynomial60_excursion_uniform {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (taylorPolynomial a 60) t-a‖≤129/250 :=
  (taylorPolynomial_excursion ha 60 t).trans (displacement60_uniform (abs_nonneg t) ht).2

theorem taylorPolynomial60_tube_uniform {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) : polynomialPath (taylorPolynomial a 60) t∈outerTube := by
  apply taylorPolynomial_tube_of_coarse_excursion ha 60 universalStepCap_pos.le universalStepCap_le_local
    (fun s hs=>taylorPolynomial60_excursion_uniform ha hs) _ ht
  intro s hs
  exact (taylorResidual60_uniform ha hs).trans (by norm_num)

theorem universal_signed_trueTaylor60_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖supportFlow σ hσ t a-polynomialPath (taylorPolynomial a 60) (σ*t)‖≤
      2*((1:ℝ)/10^57)*t := by
  have hs (s : ℝ) (hs : s∈Icc 0 (universalStepCap:ℝ)) : |σ*s|≤(universalStepCap:ℝ) := by
    rw [abs_mul,abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_right hσ hs.1).trans (by simpa using hs.2)
  exact signedTrueTaylorSegment_error σ hσ ha 60 universalStepCap_le_local (by positivity)
    (fun s h=>taylorPolynomial60_tube_uniform ha (hs s h))
    (fun s h=>taylorResidual60_uniform ha (hs s h)) t ht

theorem universal_signed_trueTaylor60_error_uniform (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖supportFlow σ hσ t a-polynomialPath (taylorPolynomial a 60) (σ*t)‖≤
      (2:ℝ)/10^59 := by
  apply (universal_signed_trueTaylor60_error σ hσ ha ht).trans
  calc
    _ ≤ 2*((1:ℝ)/10^57)*(universalStepCap:ℝ) :=
      mul_le_mul_of_nonneg_left ht.2 (by positivity)
    _ ≤ _ := by norm_num [universalStepCap]

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.universal_signed_trueTaylor60_error_uniform
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Universal actual two-sided state tail audit passed for {count} declarations; standard axioms only."
