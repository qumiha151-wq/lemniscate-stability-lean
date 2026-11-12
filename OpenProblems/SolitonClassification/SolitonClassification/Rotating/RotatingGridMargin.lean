import SolitonClassification.Rotating.FlowBootstrapGeometry
import SolitonClassification.Rotating.UniversalTrueStateTail

/-! A uniform reference-polynomial margin for grid assembly. The exact
constant b-row is essential: a generic residual bound alone would leave
only 0.002 margin there. The other rows use actual polynomial derivatives. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Polynomial UniversalMajorant
set_option backward.isDefEq.respectTransparency false

theorem taylorCoeff_parameter_succ (a : State) (n : ℕ) : taylorCoeff a (n+1) 4=0 := by
  rw [taylorCoeff]
  simp [realTaylorRHS]

theorem taylorPolynomial_parameter_constant (a : State) (N : ℕ) : taylorPolynomial a N 4=C (a 4) := by
  apply Polynomial.ext
  intro n
  cases n with
  | zero => simp [taylorPolynomial_coeff,taylorCoeff_zero]
  | succ n => simp [taylorPolynomial_coeff,taylorCoeff_parameter_succ]

theorem polynomialPath_taylor_parameter_constant (a : State) (N : ℕ) (t : ℝ) :
    polynomialPath (taylorPolynomial a N) t 4=a 4 := by
  simp only [polynomialPath,taylorPolynomial_parameter_constant,eval_C]

theorem polynomial_margin_of_coarse (P : StatePolynomial) {a : State}
    (ha : a∈innerTube) (hinit : polynomialPath P 0=a) {H : ℝ} (hH : 0≤H) (hcap : H≤1/125)
    (hexc : ∀t,|t|≤H → ‖polynomialPath P t-a‖≤129/250)
    (hres : ∀t,|t|≤H → ‖polynomialVelocity P t-field (polynomialPath P t)‖≤1)
    (hb : ∀t,polynomialPath P t 4=a 4) {t : ℝ} (ht : |t|≤H) :
    outerTubeMargin (polynomialPath P t) (1/100) := by
  have habs : |t|≤1/125 := ht.trans hcap
  have h (i : Fin 6) : |polynomialPath P t i|≤|a i|+(expandedCoordinateSpeed i+1)*|t| := by
    have hd := polynomial_coordinate_displacement_of_coarse P ha hinit hH hexc hres ht i
    have he := abs_add_le (polynomialPath P t i-a i) (a i)
    rw [sub_add_cancel] at he
    linarith
  rcases ha with ⟨ha0,ha1,ha2,ha3,ha4⟩
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  norm_num [expandedCoordinateSpeed] at h0 h1 h2 h3
  change |polynomialPath P t 2|≤|a 2|+(69+1)*|t| at h2
  change |polynomialPath P t 3|≤|a 3|+(69+1)*|t| at h3
  norm_num at h2 h3
  change |polynomialPath P t 0|+1/100≤17/2 ∧ |polynomialPath P t 1|+1/100≤9/2 ∧
    |polynomialPath P t 2|+1/100≤17/2 ∧ |polynomialPath P t 3|+1/100≤17/2 ∧
    |polynomialPath P t 4|+1/100≤1/50
  rw [hb t]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem taylorPolynomial_margin_of_coarse {a : State} (ha : a∈innerTube) (N : ℕ)
    {H : ℝ} (hH : 0≤H) (hcap : H≤1/125)
    (hexc : ∀t,|t|≤H → ‖polynomialPath (taylorPolynomial a N) t-a‖≤129/250)
    (hres : ∀t,|t|≤H → ‖polynomialPath (taylorResidual a N) t‖≤1)
    {t : ℝ} (ht : |t|≤H) : outerTubeMargin (polynomialPath (taylorPolynomial a N) t) (1/100) :=
  polynomial_margin_of_coarse _ ha (polynomialPath_taylor_zero a N) hH hcap hexc
    (fun s hs => by simpa only [polynomial_residual_actual] using hres s hs)
    (polynomialPath_taylor_parameter_constant a N) ht

theorem taylorPolynomial60_margin_uniform {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) : outerTubeMargin (polynomialPath (taylorPolynomial a 60) t) (1/100) := by
  apply taylorPolynomial_margin_of_coarse ha 60 universalStepCap_pos.le universalStepCap_le_local
    (fun s hs => taylorPolynomial60_excursion_uniform ha hs) _ ht
  intro s hs
  exact (taylorResidual60_uniform ha hs).trans (by norm_num)

theorem outerTubeMargin_mono {a : State} {r R : ℝ} (h : outerTubeMargin a R) (hr : r≤R) :
    outerTubeMargin a r := by
  rcases h with ⟨h0,h1,h2,h3,h4⟩
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem taylorPolynomial60_bootstrap_margin {a : State} (ha : a∈innerTube) {K R t : ℝ}
    (hKR : K*R≤1/100) (ht : |t|≤(universalStepCap:ℝ)) :
    outerTubeMargin (polynomialPath (taylorPolynomial a 60) t) (K*R) :=
  outerTubeMargin_mono (taylorPolynomial60_margin_uniform ha ht) hKR

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating uniform reference-margin audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating uniform reference-margin audit passed for {count} declarations."
