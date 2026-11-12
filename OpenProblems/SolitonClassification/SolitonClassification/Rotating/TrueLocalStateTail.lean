import SolitonClassification.Rotating.FlowTube
import SolitonClassification.Rotating.ResidualDataCertificate

/-! A genuine ODE truncation bound. The actual chosen flow exists globally;
its short-segment agreement with the original field is already proved.
Only finite polynomial tube/residual checks remain to instantiate this lemma. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Polynomial

theorem polynomialPath_taylor_zero (a : State) (N : ℕ) :
    polynomialPath (taylorPolynomial a N) 0=a := by
  funext i
  change (taylorPolynomial a N i).eval 0=a i
  rw [←coeff_zero_eq_eval_zero,taylorPolynomial_coeff,if_pos (Nat.zero_le _),taylorCoeff_zero]

theorem short_gronwall_bound {ε t : ℝ} (hε : 0≤ε) (ht : 0≤t) (hT : t≤1/125) :
    gronwallBound 0 17 ε t≤2*ε*t := by
  have hpos : 0≤17*t := by positivity
  have hex := Real.abs_exp_sub_one_le (show |17*t|≤1 by rw [abs_of_nonneg hpos]; linarith)
  rw [abs_of_nonneg hpos] at hex
  have he : Real.exp (17*t)-1≤2*(17*t) := (le_abs_self _).trans hex
  simp only [gronwallBound,show (17:ℝ)≠0 by norm_num,if_false,zero_mul,zero_add]
  calc
    _ ≤ (ε/17)*(2*(17*t)) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

theorem trueTaylorSegment_error {a : State} (ha : a∈innerTube) (N : ℕ)
    {T ε : ℝ} (hT : T≤1/125) (hε : 0≤ε)
    (hp : ∀t∈Icc 0 T,polynomialPath (taylorPolynomial a N) t∈outerTube)
    (hr : ∀t∈Icc 0 T,‖polynomialPath (taylorResidual a N) t‖≤ε) :
    ∀t∈Icc 0 T,‖supportFlow 1 (by norm_num) t a-polynomialPath (taylorPolynomial a N) t‖≤2*ε*t := by
  have hc : Continuous (fun t=>supportFlow 1 (by norm_num) t a) :=
    continuous_iff_continuousAt.mpr fun t=>(supportFlow_derivative 1 (by norm_num) a t).continuousAt
  have hd : ∀t∈Ico 0 T,HasDerivWithinAt (fun t=>supportFlow 1 (by norm_num) t a)
      (field (supportFlow 1 (by norm_num) t a)) (Ici t) t := by
    intro t ht
    simpa only [one_smul] using
      (supportFlow_short_original 1 (by norm_num) ha ht.1 (ht.2.le.trans hT)).hasDerivWithinAt (s:=Ici t)
  have hxt : ∀t∈Ico 0 T,supportFlow 1 (by norm_num) t a∈outerTube := by
    intro t ht
    exact supportFlow_short_mem_outerTube 1 (by norm_num) ha ht.1 (ht.2.le.trans hT)
  have hinit : dist (supportFlow 1 (by norm_num) 0 a) (polynomialPath (taylorPolynomial a N) 0)≤0 := by
    rw [supportFlow_zero,polynomialPath_taylor_zero]
    simp
  have he:=polynomial_ode_comparison a N hc.continuousOn hd hxt
    (fun t ht=>hp t (Ico_subset_Icc_self ht)) (fun t ht=>hr t (Ico_subset_Icc_self ht)) hinit
  intro t ht
  have he' : ‖supportFlow 1 (by norm_num) t a-polynomialPath (taylorPolynomial a N) t‖≤
      gronwallBound 0 17 ε t := by simpa only [dist_eq_norm] using he t ht
  exact he'.trans (short_gronwall_bound hε ht.1 (ht.2.trans hT))

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.trueTaylorSegment_error
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Actual ODE local state-truncation audit passed."
