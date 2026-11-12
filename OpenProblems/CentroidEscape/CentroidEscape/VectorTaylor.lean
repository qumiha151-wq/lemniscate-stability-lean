import CentroidEscape.WeightedExpansion
import CentroidEscape.ScalarMajorant

/-!
# Coefficient majorization for the actual weighted field

The Taylor recurrence is the finite convolution recurrence obtained from the
proved concrete linear/bilinear/trilinear expansion. Coefficient norm bounds
are conclusions of the recurrence, not input assumptions.
-/
namespace CentroidEscape
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def displacementMajorant : ℝ[X] := C (1/3)*(scalarMajorant-1)

lemma displacementMajorant_zero : displacementMajorant.coeff 0 = 0 := by
  simp [displacementMajorant, scalarMajorant_coeff_zero]

lemma displacementMajorant_coeff_pos (n : ℕ) (hn : 0 < n) :
    displacementMajorant.coeff n = scalarMajorant.coeff n/3 := by
  simp [displacementMajorant, coeff_sub, coeff_one, ne_of_gt hn]
  ring

lemma displacementMajorant_nonneg (n : ℕ) : 0 ≤ displacementMajorant.coeff n := by
  by_cases hn : n = 0
  · simp [hn, displacementMajorant_zero]
  · rw [displacementMajorant_coeff_pos n (Nat.pos_of_ne_zero hn)]
    exact div_nonneg (scalarMajorant_coeff_nonneg n) (by norm_num)

def scalarForcing : ℝ[X] := C 2+C 18*displacementMajorant+
  C 54*displacementMajorant^2+C 54*displacementMajorant^3

lemma scalarForcing_eq : scalarForcing = C 2*scalarMajorant^3 := by
  have hu : scalarMajorant = 1+C 3*displacementMajorant := by
    rw [displacementMajorant, ← mul_assoc, ← C_mul]
    norm_num
  rw [scalarForcing, hu]
  simp only [C_ofNat]
  ring

lemma scalarForcing_recurrence (n : ℕ) (hn : n < 160) :
    scalarForcing.coeff n = (n+1:ℝ)*displacementMajorant.coeff (n+1) := by
  have hh := scalarResidual_low_coeff_zero n hn
  simp only [scalarResidual, coeff_sub, coeff_C_mul, coeff_derivative] at hh
  rw [scalarForcing_eq, coeff_C_mul, displacementMajorant_coeff_pos (n+1) (by omega)]
  linarith

def quadraticTaylorCoeff (a : WeightedState) (p : ℕ → WeightedState) (n : ℕ) : WeightedState :=
  ∑ ij ∈ Finset.antidiagonal n, weightedBilinear a (p ij.1) (p ij.2)

def cubicTaylorCoeff (p : ℕ → WeightedState) (n : ℕ) : WeightedState :=
  ∑ ij ∈ Finset.antidiagonal n, ∑ jk ∈ Finset.antidiagonal ij.2,
    weightedTrilinear (p ij.1) (p jk.1) (p jk.2)

def vectorTaylorRHS (a : WeightedState) (p : ℕ → WeightedState) (n : ℕ) : WeightedState :=
  (if n = 0 then weightedField a else 0)+weightedLinear a (p n)+
    quadraticTaylorCoeff a p n+cubicTaylorCoeff p n

lemma quadraticTaylorCoeff_bound {a : WeightedState} (ha : a ∈ weightedTube)
    (p : ℕ → WeightedState) (n : ℕ)
    (hp : ∀ j ≤ n, ‖p j‖ ≤ displacementMajorant.coeff j) :
    ‖quadraticTaylorCoeff a p n‖ ≤ 22*(displacementMajorant^2).coeff n := by
  rw [quadraticTaylorCoeff, pow_two, coeff_mul, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  have hwi := displacementMajorant_nonneg ij.1
  have hwj := displacementMajorant_nonneg ij.2
  calc
    _ ≤ 22*‖p ij.1‖*‖p ij.2‖ := weightedBilinear_bound ha _ _
    _ ≤ 22*displacementMajorant.coeff ij.1*displacementMajorant.coeff ij.2 := by
      gcongr <;> apply hp <;> omega
    _ = _ := by ring

lemma cubicTaylorCoeff_bound (p : ℕ → WeightedState) (n : ℕ)
    (hp : ∀ j ≤ n, ‖p j‖ ≤ displacementMajorant.coeff j) :
    ‖cubicTaylorCoeff p n‖ ≤ 32*(displacementMajorant^3).coeff n := by
  have heq : displacementMajorant^3 = displacementMajorant*(displacementMajorant*displacementMajorant) := by ring
  rw [cubicTaylorCoeff, heq, coeff_mul, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  rw [coeff_mul, Finset.mul_sum, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro jk hjk
  have hj := Finset.mem_antidiagonal.mp hjk
  have hwi := displacementMajorant_nonneg ij.1
  have hwj := displacementMajorant_nonneg jk.1
  have hwk := displacementMajorant_nonneg jk.2
  calc
    _ ≤ 32*‖p ij.1‖*‖p jk.1‖*‖p jk.2‖ := weightedTrilinear_bound _ _ _
    _ ≤ 32*displacementMajorant.coeff ij.1*displacementMajorant.coeff jk.1*displacementMajorant.coeff jk.2 := by
      gcongr <;> apply hp <;> omega
    _ = _ := by ring

lemma vectorTaylorRHS_bound {a : WeightedState} (ha : a ∈ weightedTube)
    (p : ℕ → WeightedState) (n : ℕ)
    (hp : ∀ j ≤ n, ‖p j‖ ≤ displacementMajorant.coeff j) :
    ‖vectorTaylorRHS a p n‖ ≤ scalarForcing.coeff n := by
  have hzero : ‖if n = 0 then weightedField a else 0‖ ≤ (C 2 : ℝ[X]).coeff n := by
    by_cases hn : n = 0
    · subst n
      simpa using weightedField_bound ha
    · simp [hn, coeff_C]
  have hl : ‖weightedLinear a (p n)‖ ≤ 8*displacementMajorant.coeff n :=
    (weightedLinear_bound ha _).trans (mul_le_mul_of_nonneg_left (hp n le_rfl) (by norm_num))
  have hq := quadraticTaylorCoeff_bound ha p n hp
  have hc := cubicTaylorCoeff_bound p n hp
  have hw := displacementMajorant_nonneg n
  have hw2 : 0 ≤ (displacementMajorant^2).coeff n := by
    rw [pow_two]
    exact coeff_mul_nonneg_all displacementMajorant_nonneg displacementMajorant_nonneg n
  have hw3 : 0 ≤ (displacementMajorant^3).coeff n := by
    have h := coeff_mul_nonneg_all
      (coeff_mul_nonneg_all displacementMajorant_nonneg displacementMajorant_nonneg)
      displacementMajorant_nonneg n
    convert h using 1
    congr 1
    ring
  have h1 := norm_add_le (if n = 0 then weightedField a else 0) (weightedLinear a (p n))
  have h2 := norm_add_le ((if n = 0 then weightedField a else 0)+weightedLinear a (p n))
    (quadraticTaylorCoeff a p n)
  have h3 := norm_add_le ((if n = 0 then weightedField a else 0)+weightedLinear a (p n)+
    quadraticTaylorCoeff a p n) (cubicTaylorCoeff p n)
  simp only [vectorTaylorRHS, scalarForcing, coeff_add, coeff_C_mul]
  linarith

/-- Coefficient norms follow from the actual weighted-field convolution
recurrence. No coefficient bound is assumed in this theorem. -/
theorem vectorTaylor_majorized {a : WeightedState} (ha : a ∈ weightedTube)
    (p : ℕ → WeightedState) (hp0 : p 0 = 0)
    (hrec : ∀ (n : ℕ), n < 160 → (n+1:ℝ) • p (n+1) = vectorTaylorRHS a p n) :
    ∀ n ≤ 160, ‖p n‖ ≤ displacementMajorant.coeff n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp [hp0, displacementMajorant_zero]
    | succ n =>
      have hprev : ∀ j ≤ n, ‖p j‖ ≤ displacementMajorant.coeff j := by
        intro j hj
        exact ih j (by omega) (by omega)
      have hbound := vectorTaylorRHS_bound ha p n hprev
      rw [← hrec n (by omega), norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), scalarForcing_recurrence n (by omega)] at hbound
      by_contra hnot
      have hpos := mul_pos (by positivity : (0:ℝ) < n+1)
        (sub_pos.mpr (lt_of_not_ge hnot))
      nlinarith

lemma vectorTaylorRHS_congr (a : WeightedState) (p q : ℕ → WeightedState) (n : ℕ)
    (hpq : ∀ j ≤ n, p j = q j) : vectorTaylorRHS a p n = vectorTaylorRHS a q n := by
  have hl : weightedLinear a (p n) = weightedLinear a (q n) := congrArg _ (hpq n le_rfl)
  have hq : quadraticTaylorCoeff a p n = quadraticTaylorCoeff a q n := by
    apply Finset.sum_congr rfl
    intro ij hij
    have h := Finset.mem_antidiagonal.mp hij
    rw [hpq ij.1 (by omega), hpq ij.2 (by omega)]
  have hc : cubicTaylorCoeff p n = cubicTaylorCoeff q n := by
    apply Finset.sum_congr rfl
    intro ij hij
    have h := Finset.mem_antidiagonal.mp hij
    apply Finset.sum_congr rfl
    intro jk hjk
    have h' := Finset.mem_antidiagonal.mp hjk
    rw [hpq ij.1 (by omega), hpq jk.1 (by omega), hpq jk.2 (by omega)]
  simp only [vectorTaylorRHS, hl, hq, hc]

/-- Canonical coefficients are defined by the concrete finite field
convolution recurrence. The well-founded definition uses only earlier indices. -/
def canonicalTaylorCoeff (a : WeightedState) : ℕ → WeightedState
  | 0 => 0
  | n+1 => (1/(n+1:ℝ)) • vectorTaylorRHS a
      (fun j => if _h : j ≤ n then canonicalTaylorCoeff a j else 0) n
termination_by n => n
decreasing_by omega

lemma canonicalTaylorCoeff_zero (a : WeightedState) : canonicalTaylorCoeff a 0 = 0 := by
  rw [canonicalTaylorCoeff]

theorem canonicalTaylorCoeff_recurrence (a : WeightedState) (n : ℕ) :
    (n+1:ℝ) • canonicalTaylorCoeff a (n+1) = vectorTaylorRHS a (canonicalTaylorCoeff a) n := by
  rw [canonicalTaylorCoeff]
  have he : vectorTaylorRHS a
      (fun j => if h : j ≤ n then canonicalTaylorCoeff a j else 0) n =
      vectorTaylorRHS a (canonicalTaylorCoeff a) n := by
    apply vectorTaylorRHS_congr
    intro j hj
    simp [hj]
  rw [he, smul_smul]
  simp [show (n+1:ℝ) ≠ 0 by positivity]

theorem canonicalTaylorCoeff_majorized {a : WeightedState} (ha : a ∈ weightedTube) :
    ∀ n ≤ 160, ‖canonicalTaylorCoeff a n‖ ≤ displacementMajorant.coeff n :=
  vectorTaylor_majorized ha _ (canonicalTaylorCoeff_zero a)
    (fun n _ => canonicalTaylorCoeff_recurrence a n)

def canonicalTaylorPolynomial (a : WeightedState) (t : ℝ) : WeightedState :=
  a+∑ n ∈ Finset.range 161, t^n • canonicalTaylorCoeff a n

lemma displacementMajorant_sum (t : ℝ) :
    (∑ n ∈ Finset.range 161, t^n*displacementMajorant.coeff n) =
      (majorantPoly t-1)/3 := by
  have hs0 : (∑ n ∈ Finset.range 161, t^n*(1:ℝ[X]).coeff n) = 1 := by
    simp [coeff_one]
  have hsu : (∑ n ∈ Finset.range 161, t^n*scalarMajorant.coeff n) = majorantPoly t := by
    unfold majorantPoly
    apply Finset.sum_congr rfl
    intro n hn
    rw [scalarMajorant_coeff, if_pos (Finset.mem_range.mp hn)]
    ring
  calc
    _ = ((∑ n ∈ Finset.range 161, t^n*scalarMajorant.coeff n)-
        (∑ n ∈ Finset.range 161, t^n*(1:ℝ[X]).coeff n))/3 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [displacementMajorant, coeff_C_mul, coeff_sub]
      ring
    _ = _ := by rw [hs0, hsu]

theorem canonicalTaylorPolynomial_excursion {a : WeightedState} (ha : a ∈ weightedTube)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖canonicalTaylorPolynomial a t-a‖ ≤ (majorantPoly t-1)/3 := by
  rw [canonicalTaylorPolynomial, add_sub_cancel_left, ← displacementMajorant_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht n)]
  exact mul_le_mul_of_nonneg_left
    (canonicalTaylorCoeff_majorized ha n (by have := Finset.mem_range.mp hn; omega))
    (pow_nonneg ht n)

theorem canonicalTaylorPolynomial_excursion_uniform {a : WeightedState} (ha : a ∈ weightedTube)
    {t : ℝ} (ht : 0 ≤ t) (htmax : t ≤ 1/100) :
    ‖canonicalTaylorPolynomial a t-a‖ < 23/1000 :=
  lt_of_le_of_lt (canonicalTaylorPolynomial_excursion ha ht)
    (finite_majorant_excursion_uniform ht htmax).2

theorem canonicalTaylorPolynomial_in_tube {a : WeightedState}
    (ha : ∀ i : Fin 7, i ≠ 6 → |a i| ≤ tubeRadius i-23/1000)
    {t : ℝ} (ht : 0 ≤ t) (htmax : t ≤ 1/100) :
    canonicalTaylorPolynomial a t ∈ weightedTube := by
  have hatube : a ∈ weightedTube := by intro i hi; linarith [ha i hi]
  have he := canonicalTaylorPolynomial_excursion_uniform hatube ht htmax
  intro i hi
  have hc : |canonicalTaylorPolynomial a t i-a i| ≤ ‖canonicalTaylorPolynomial a t-a‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      norm_le_pi_norm (canonicalTaylorPolynomial a t-a) i
  have htri := abs_add_le (canonicalTaylorPolynomial a t i-a i) (a i)
  rw [sub_add_cancel] at htri
  linarith [ha i hi]

def canonicalTaylorDerivative (a : WeightedState) (t : ℝ) : WeightedState :=
  ∑ n ∈ Finset.range 161, ((n:ℝ)*t^(n-1)) • canonicalTaylorCoeff a n

theorem canonicalTaylorPolynomial_hasDerivAt (a : WeightedState) (t : ℝ) :
    HasDerivAt (canonicalTaylorPolynomial a) (canonicalTaylorDerivative a t) t := by
  have hh : HasDerivAt (fun s : ℝ => ∑ n ∈ Finset.range 161, s^n • canonicalTaylorCoeff a n)
      (canonicalTaylorDerivative a t) t := by
    apply HasDerivAt.fun_sum
    intro n hn
    simpa only [mul_one, Pi.pow_apply, id_eq] using
      ((hasDerivAt_id t).pow n).smul_const (canonicalTaylorCoeff a n)
  exact hh.const_add a

end
end CentroidEscape

#print axioms CentroidEscape.vectorTaylor_majorized
#print axioms CentroidEscape.canonicalTaylorCoeff_majorized

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Vector-Taylor audit passed for {checked} declarations."
