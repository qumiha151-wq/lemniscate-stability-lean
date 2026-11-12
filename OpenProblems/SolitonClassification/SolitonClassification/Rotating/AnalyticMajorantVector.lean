import SolitonClassification.Rotating.AnalyticMajorantScalar
import SolitonClassification.Rotating.FlowTube

/-! Finite vector majorization for the actual rotating field.
The convolution norm argument is independently ported from this workspace's
CentroidEscape/VectorTaylor.lean (first 160 lines), with the actual rotating
field and arbitrary truncation order. There is no cross-problem import.
The companion AnalyticMajorantVectorActual connects this generic finite
recurrence directly to Rotating.taylorCoeff, whose constant term is a. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

lemma innerTube_subset_outerTube {a : State} (ha : a ∈ innerTube) : a ∈ outerTube := by
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

/-- The actual inner-tube field bound, including the unrestricted angle. -/
theorem field_inner_bound {a : State} (ha : a ∈ innerTube) : ‖field a‖ ≤ 61 := by
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  fin_cases i
  · change |8*a 1| ≤ 61
    rw [abs_mul]; norm_num; linarith
  · change |-(a 0)^3/16-a 2/8-a 4*a 3/8| ≤ 61
    calc
      _ ≤ |-(a 0)^3/16-a 2/8|+|a 4*a 3/8| := abs_sub _ _
      _ ≤ (|-(a 0)^3/16|+|a 2/8|)+|a 4*a 3/8| := by gcongr; apply abs_sub
      _ = |a 0|^3/16+|a 2|/8+|a 4| * |a 3|/8 := by simp [abs_div,abs_mul,abs_pow]
      _ ≤ (407/50)^3/16+(731/100)/8+(1/100)*(731/100)/8 := by gcongr
      _ ≤ 61 := by norm_num
  · change |-a 0*a 3| ≤ 61
    rw [abs_mul,abs_neg]
    calc
      _ ≤ (407/50:ℝ)*(731/100) := by gcongr
      _ ≤ 61 := by norm_num
  · change |1+a 0*a 2| ≤ 61
    calc
      _ ≤ |(1:ℝ)|+|a 0*a 2| := abs_add_le _ _
      _ = 1+|a 0| * |a 2| := by simp [abs_mul]
      _ ≤ 1+(407/50)*(731/100) := by gcongr
      _ ≤ 61 := by norm_num
  · simp [field]
  · change |a 0| ≤ 61
    linarith

def quadraticTaylorCoeff (a : State) (p : ℕ → State) (n : ℕ) : State :=
  ∑ ij ∈ Finset.antidiagonal n, bilinear a (p ij.1) (p ij.2)

def cubicTaylorCoeff (p : ℕ → State) (n : ℕ) : State :=
  ∑ ij ∈ Finset.antidiagonal n, ∑ jk ∈ Finset.antidiagonal ij.2,
    trilinear (p ij.1) (p jk.1) (p jk.2)

def vectorTaylorRHS (a : State) (p : ℕ → State) (n : ℕ) : State :=
  (if n=0 then field a else 0)+linear a (p n)+
    quadraticTaylorCoeff a p n+cubicTaylorCoeff p n

lemma quadraticTaylorCoeff_bound {a : State} (ha : a ∈ innerTube)
    (N : ℕ) (p : ℕ → State) (n : ℕ)
    (hp : ∀ j ≤ n, ‖p j‖ ≤ (displacementPolynomial N).coeff j) :
    ‖quadraticTaylorCoeff a p n‖ ≤ 2*((displacementPolynomial N)^2).coeff n := by
  rw [quadraticTaylorCoeff,pow_two,coeff_mul,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  have hwi := displacementPolynomial_nonneg N ij.1
  have hwj := displacementPolynomial_nonneg N ij.2
  calc
    _ ≤ 2*‖p ij.1‖*‖p ij.2‖ := bilinear_bound (innerTube_subset_outerTube ha) _ _
    _ ≤ 2*(displacementPolynomial N).coeff ij.1*(displacementPolynomial N).coeff ij.2 := by
      gcongr <;> apply hp <;> omega
    _ = _ := by ring

lemma cubicTaylorCoeff_bound (N : ℕ) (p : ℕ → State) (n : ℕ)
    (hp : ∀ j ≤ n, ‖p j‖ ≤ (displacementPolynomial N).coeff j) :
    ‖cubicTaylorCoeff p n‖ ≤ (1/16)*((displacementPolynomial N)^3).coeff n := by
  have heq : (displacementPolynomial N)^3 =
      displacementPolynomial N*(displacementPolynomial N*displacementPolynomial N) := by ring
  rw [cubicTaylorCoeff,heq,coeff_mul,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  rw [coeff_mul,Finset.mul_sum,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro jk hjk
  have hj := Finset.mem_antidiagonal.mp hjk
  have hwi := displacementPolynomial_nonneg N ij.1
  have hwj := displacementPolynomial_nonneg N jk.1
  have hwk := displacementPolynomial_nonneg N jk.2
  calc
    _ ≤ (1/16)*‖p ij.1‖*‖p jk.1‖*‖p jk.2‖ := trilinear_bound _ _ _
    _ ≤ (1/16)*(displacementPolynomial N).coeff ij.1*
        (displacementPolynomial N).coeff jk.1*(displacementPolynomial N).coeff jk.2 := by
      gcongr <;> apply hp <;> omega
    _ = _ := by ring

lemma vectorTaylorRHS_bound {a : State} (ha : a ∈ innerTube)
    (N : ℕ) (p : ℕ → State) (n : ℕ)
    (hp : ∀ j ≤ n, ‖p j‖ ≤ (displacementPolynomial N).coeff j) :
    ‖vectorTaylorRHS a p n‖ ≤ (scalarForcing (displacementPolynomial N)).coeff n := by
  have hzero : ‖if n=0 then field a else 0‖ ≤ (C 61 : ℝ[X]).coeff n := by
    by_cases hn : n=0
    · subst n
      simpa using field_inner_bound ha
    · simp [hn,coeff_C]
  have hl : ‖linear a (p n)‖ ≤ 17*(displacementPolynomial N).coeff n :=
    (linear_bound (innerTube_subset_outerTube ha) _).trans
      (mul_le_mul_of_nonneg_left (hp n le_rfl) (by norm_num))
  have hq := quadraticTaylorCoeff_bound ha N p n hp
  have hc := cubicTaylorCoeff_bound N p n hp
  have hw := displacementPolynomial_nonneg N n
  have hw2 : 0 ≤ ((displacementPolynomial N)^2).coeff n := by
    rw [pow_two]
    exact coeff_mul_nonneg_all (displacementPolynomial_nonneg N) (displacementPolynomial_nonneg N) n
  have hw3 : 0 ≤ ((displacementPolynomial N)^3).coeff n := by
    have h := coeff_mul_nonneg_all
      (coeff_mul_nonneg_all (displacementPolynomial_nonneg N) (displacementPolynomial_nonneg N))
      (displacementPolynomial_nonneg N) n
    convert h using 1
    congr 1
    ring
  have h1 := norm_add_le (if n=0 then field a else 0) (linear a (p n))
  have h2 := norm_add_le ((if n=0 then field a else 0)+linear a (p n))
    (quadraticTaylorCoeff a p n)
  have h3 := norm_add_le ((if n=0 then field a else 0)+linear a (p n)+
    quadraticTaylorCoeff a p n) (cubicTaylorCoeff p n)
  simp only [vectorTaylorRHS,scalarForcing,coeff_add,coeff_C_mul]
  linarith

/-- Arbitrary finite order. The coefficient norm bound is derived, not assumed. -/
theorem vectorTaylor_majorized {a : State} (ha : a ∈ innerTube)
    (N : ℕ) (p : ℕ → State) (hp0 : p 0=0)
    (hrec : ∀ n < N, (n+1:ℝ) • p (n+1)=vectorTaylorRHS a p n) :
    ∀ n ≤ N, ‖p n‖ ≤ (displacementPolynomial N).coeff n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp [hp0,displacementPolynomial_zero]
    | succ n =>
      have hprev : ∀ j ≤ n, ‖p j‖ ≤ (displacementPolynomial N).coeff j := by
        intro j hj
        exact ih j (by omega) (by omega)
      have hbound := vectorTaylorRHS_bound ha N p n hprev
      rw [← hrec n (by omega),norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (by positivity),scalarForcing_recurrence N n (by omega)] at hbound
      by_contra hnot
      have hpos := mul_pos (by positivity : (0:ℝ)<n+1)
        (sub_pos.mpr (lt_of_not_ge hnot))
      nlinarith

lemma vectorTaylorRHS_congr (a : State) (p q : ℕ → State) (n : ℕ)
    (hpq : ∀ j ≤ n, p j=q j) : vectorTaylorRHS a p n=vectorTaylorRHS a q n := by
  have hl : linear a (p n)=linear a (q n) := congrArg _ (hpq n le_rfl)
  have hq : quadraticTaylorCoeff a p n=quadraticTaylorCoeff a q n := by
    apply Finset.sum_congr rfl
    intro ij hij
    have h := Finset.mem_antidiagonal.mp hij
    rw [hpq ij.1 (by omega),hpq ij.2 (by omega)]
  have hc : cubicTaylorCoeff p n=cubicTaylorCoeff q n := by
    apply Finset.sum_congr rfl
    intro ij hij
    have h := Finset.mem_antidiagonal.mp hij
    apply Finset.sum_congr rfl
    intro jk hjk
    have h' := Finset.mem_antidiagonal.mp hjk
    rw [hpq ij.1 (by omega),hpq jk.1 (by omega),hpq jk.2 (by omega)]
  simp only [vectorTaylorRHS,hl,hq,hc]

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.vectorTaylor_majorized
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
  logInfo m!"Universal vector majorant audit passed: {checked} declarations; standard axioms only."
