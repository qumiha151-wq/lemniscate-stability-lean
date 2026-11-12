import SolitonClassification.Rotating.ResidualODE
import SolitonClassification.Rotating.FixedField
import SolitonClassification.Rotating.VariationTaylor
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Finite coefficient envelopes for the actual state and variational
residuals. These lemmas turn finite rational checks into bounds for every
real point of a segment, not just the endpoint. -/
namespace SolitonClassification.Rotating
noncomputable section
open Polynomial

lemma degree_sub_bound {p q : ℝ[X]} {M : ℕ}
    (hp : p.natDegree≤M) (hq : q.natDegree≤M) : (p-q).natDegree≤M := by
  simpa using natDegree_sub_le_of_le hp hq

lemma degree_add_bound {p q : ℝ[X]} {M : ℕ}
    (hp : p.natDegree≤M) (hq : q.natDegree≤M) : (p+q).natDegree≤M :=
  natDegree_add_le_of_degree_le hp hq

theorem taylorPolynomial_degree (a : State) (N : ℕ) (i : Fin 6) :
    (taylorPolynomial a N i).natDegree≤N := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [taylorPolynomial_coeff,if_neg (by omega)]

theorem variationPolynomial_degree (a v : State) (N : ℕ) (i : Fin 6) :
    (variationPolynomial a v N i).natDegree≤N := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [variationPolynomial_coeff,if_neg (by omega)]

theorem polynomialField_degree {P : StatePolynomial} {N : ℕ}
    (hp : ∀i,(P i).natDegree≤N) (i : Fin 6) :
    (polynomialField P i).natDegree≤3*N := by
  have hl (i : Fin 6) : (P i).natDegree≤3*N := (hp i).trans (by omega)
  have hq (i j : Fin 6) : (P i*P j).natDegree≤3*N :=
    (natDegree_mul_le_of_le (hp i) (hp j)).trans (by omega)
  have hc : ((P 0)^2*P 0).natDegree≤3*N :=
    (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 (hp 0)) (hp 0)).trans (by omega)
  fin_cases i
  · exact (natDegree_C_mul_le _ _).trans (hl 1)
  · change (-C (1/16)*((P 0)^2*P 0)-C (1/8)*P 2-C (1/8)*(P 4*P 3)).natDegree≤_
    rw [neg_mul]
    apply degree_sub_bound
    · apply degree_sub_bound
      · exact natDegree_neg_le_of_le ((natDegree_C_mul_le _ _).trans hc)
      · exact (natDegree_C_mul_le _ _).trans (hl 2)
    · exact (natDegree_C_mul_le _ _).trans (hq 4 3)
  · exact natDegree_neg_le_of_le (hq 0 3)
  · exact degree_add_bound (by simp) (hq 0 2)
  · simp [polynomialField]
  · exact hl 0

theorem taylorResidual_degree (a : State) (N : ℕ) (i : Fin 6) :
    (taylorResidual a N i).natDegree≤3*N := by
  apply degree_sub_bound
  · exact (natDegree_derivative_le _).trans
      ((Nat.sub_le _ _).trans ((taylorPolynomial_degree a N i).trans (by omega)))
  · exact polynomialField_degree (taylorPolynomial_degree a N) i

theorem polynomialVariation_degree {P W : StatePolynomial} {N : ℕ}
    (hp : ∀i,(P i).natDegree≤N) (hw : ∀i,(W i).natDegree≤N) (i : Fin 6) :
    (polynomialVariation P W i).natDegree≤3*N := by
  have hl (i : Fin 6) : (W i).natDegree≤3*N := (hw i).trans (by omega)
  have hq (i j : Fin 6) : (P i*W j).natDegree≤3*N :=
    (natDegree_mul_le_of_le (hp i) (hw j)).trans (by omega)
  have hc : ((P 0)^2*W 0).natDegree≤3*N :=
    (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 (hp 0)) (hw 0)).trans (by omega)
  fin_cases i
  · exact (natDegree_C_mul_le _ _).trans (hl 1)
  · change (-C (3/16)*((P 0)^2*W 0)-C (1/8)*W 2-
      C (1/8)*(P 4*W 3)-C (1/8)*(P 3*W 4)).natDegree≤_
    rw [neg_mul]
    apply degree_sub_bound
    · apply degree_sub_bound
      · apply degree_sub_bound
        · exact natDegree_neg_le_of_le ((natDegree_C_mul_le _ _).trans hc)
        · exact (natDegree_C_mul_le _ _).trans (hl 2)
      · exact (natDegree_C_mul_le _ _).trans (hq 4 3)
    · exact (natDegree_C_mul_le _ _).trans (hq 3 4)
  · exact degree_sub_bound (natDegree_neg_le_of_le (hq 0 3)) (hq 3 0)
  · exact degree_add_bound (hq 0 2) (hq 2 0)
  · simp [polynomialVariation]
  · exact hl 0

theorem variationResidual_degree (a v : State) (N : ℕ) (i : Fin 6) :
    (variationResidual a v N i).natDegree≤3*N := by
  apply degree_sub_bound
  · exact (natDegree_derivative_le _).trans
      ((Nat.sub_le _ _).trans ((variationPolynomial_degree a v N i).trans (by omega)))
  · exact polynomialVariation_degree (taylorPolynomial_degree a N) (variationPolynomial_degree a v N) i

def rationalEnvelope (c : ℕ → ℚ) (h : ℚ) (M : ℕ) : ℚ :=
  ∑n∈Finset.range (M+1),c n*h^n

theorem finitePolynomial_abs_bound {p : ℝ[X]} {M : ℕ} {c : ℕ → ℚ} {h : ℚ} {t : ℝ}
    (hd : p.natDegree≤M) (hc : ∀n≤M,|p.coeff n|≤(c n:ℝ)) (ht : |t|≤(h:ℝ)) :
    |p.eval t|≤(rationalEnvelope c h M:ℝ) := by
  rw [eval_eq_sum_range' (show p.natDegree<M+1 by omega)]
  have hh : 0≤(h:ℝ) := (abs_nonneg t).trans ht
  have hsum : (rationalEnvelope c h M:ℝ)=
      ∑n∈Finset.range (M+1),(c n:ℝ)*(h:ℝ)^n := by simp [rationalEnvelope]
  rw [hsum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  have hn' : n≤M := by have := Finset.mem_range.mp hn; omega
  rw [abs_mul,abs_pow]
  exact mul_le_mul (hc n hn') (pow_le_pow_left₀ (abs_nonneg t) ht n)
    (pow_nonneg (abs_nonneg t) n) ((abs_nonneg _).trans (hc n hn'))

theorem finitePolynomial_norm_bound {P : StatePolynomial} {M : ℕ}
    {c : Fin 6 → ℕ → ℚ} {h B : ℚ} {t : ℝ}
    (hd : ∀i,(P i).natDegree≤M) (hc : ∀i n,n≤M→|(P i).coeff n|≤(c i n:ℝ))
    (hB : 0≤B) (hb : ∀i,rationalEnvelope (c i) h M≤B) (ht : |t|≤(h:ℝ)) :
    ‖polynomialPath P t‖≤(B:ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (show 0≤(B:ℝ) by exact_mod_cast hB)).mpr
  intro i
  change |(P i).eval t|≤(B:ℝ)
  exact (finitePolynomial_abs_bound (hd i) (hc i) ht).trans (by exact_mod_cast hb i)

def fixedAbsUpper (S : ℕ) (b : FixedBall) : ℚ :=
  |(b.toRational S).center|+(b.toRational S).radius

theorem fixedAbsUpper_sound {S : ℕ} {b : FixedBall} {x : ℝ}
    (hx : b.Contains S x) : |x|≤(fixedAbsUpper S b:ℝ) := by
  change |x-((b.toRational S).center:ℝ)|≤((b.toRational S).radius:ℝ) at hx
  have h:=abs_add_le (x-((b.toRational S).center:ℝ)) ((b.toRational S).center:ℝ)
  rw [sub_add_cancel] at h
  simp only [fixedAbsUpper,Rat.cast_add,Rat.cast_abs]
  linarith

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.finitePolynomial_norm_bound
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Finite state/variation residual-envelope audit passed."
