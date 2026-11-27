import SolitonClassification.Rotating.UniversalTrueStateTail

namespace SolitonClassification.Rotating.IntegerWinding
noncomputable section
open Set Polynomial UniversalMajorant
set_option maxHeartbeats 2000000

/-- This shared box allows the positive pitch of the winding-one certificate. -/
def nodeBox : Set State := {a | |a 0| ≤ 83/10 ∧ |a 1| ≤ 43/10 ∧
    |a 2| ≤ 36/5 ∧ |a 3| ≤ 36/5 ∧ |a 4| ≤ 3/25}

theorem node_field {a : State} (ha : a ∈ nodeBox) : ‖field a‖ ≤ 61 := by
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
      _ ≤ (83/10)^3/16+(36/5)/8+(3/25)*(36/5)/8 := by gcongr
      _ ≤ 61 := by norm_num
  · change |-a 0*a 3| ≤ 61
    rw [abs_mul,abs_neg]
    calc
      _ ≤ (83/10:ℝ)*(36/5) := by gcongr
      _ ≤ 61 := by norm_num
  · change |1+a 0*a 2| ≤ 61
    calc
      _ ≤ |(1:ℝ)|+|a 0*a 2| := abs_add_le _ _
      _ = 1+|a 0| * |a 2| := by simp [abs_mul]
      _ ≤ 1+(83/10)*(36/5) := by gcongr
      _ ≤ 61 := by norm_num
  · simp [field]
  · change |a 0| ≤ 61
    linarith

theorem node_linear {a : State} (ha : a∈nodeBox) (u : State) :
    ‖linear a u‖≤17*‖u‖ := by
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  have hn := norm_nonneg u
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · change |8*u 1|≤_
    rw [abs_mul]; norm_num
    linarith [coordinate_bound u 1]
  · change |-3*(a 0)^2*u 0/16-u 2/8-a 4*u 3/8-u 4*a 3/8|≤_
    calc
      _ ≤ |-3*(a 0)^2*u 0/16-u 2/8-a 4*u 3/8|+|u 4*a 3/8| := abs_sub _ _
      _ ≤ (|-3*(a 0)^2*u 0/16-u 2/8|+|a 4*u 3/8|)+|u 4*a 3/8| := by
        gcongr; apply abs_sub
      _ ≤ ((|-3*(a 0)^2*u 0/16|+|u 2/8|)+|a 4*u 3/8|)+|u 4*a 3/8| := by
        gcongr; apply abs_sub
      _ = 3*|a 0|^2*|u 0|/16+|u 2|/8+|a 4| * |u 3|/8+|u 4| * |a 3|/8 := by
        simp only [abs_div,abs_mul,abs_pow]; norm_num
      _ ≤ 3*(83/10)^2*‖u‖/16+‖u‖/8+(3/25)*‖u‖/8+‖u‖*(36/5)/8 := by
        gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith
  · change |-a 0*u 3-u 0*a 3|≤_
    calc
      _ ≤ |-a 0*u 3|+|u 0*a 3| := abs_sub _ _
      _ = |a 0| * |u 3|+|u 0| * |a 3| := by simp [abs_mul]
      _ ≤ (83/10)*‖u‖+‖u‖*(36/5) := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith
  · change |a 0*u 2+u 0*a 2|≤_
    calc
      _ ≤ |a 0*u 2|+|u 0*a 2| := abs_add_le _ _
      _ = |a 0| * |u 2|+|u 0| * |a 2| := by simp [abs_mul]
      _ ≤ (83/10)*‖u‖+‖u‖*(36/5) := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith
  · simp [linear]
  · change |u 0|≤_
    linarith [coordinate_bound u 0]

private theorem node_bilinear {a : State} (ha : a ∈ nodeBox) (u v : State) :
    ‖bilinear a u v‖ ≤ 2*‖u‖*‖v‖ := by
  let b : State := ![a 0,0,0,0,0,0]
  have h : b ∈ outerTube := ⟨by change |a 0| ≤ 17/2; linarith [ha.1],
    by change |(0:ℝ)| ≤ 9/2; norm_num, by change |(0:ℝ)| ≤ 17/2; norm_num,
    by change |(0:ℝ)| ≤ 17/2; norm_num, by change |(0:ℝ)| ≤ 1/50; norm_num⟩
  exact bilinear_bound h u v

lemma node_quadratic {a : State} (ha : a ∈ nodeBox)
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
    _ ≤ 2*‖p ij.1‖*‖p ij.2‖ := node_bilinear ha _ _
    _ ≤ 2*(displacementPolynomial N).coeff ij.1*(displacementPolynomial N).coeff ij.2 := by
      gcongr <;> apply hp <;> omega
    _ = _ := by ring

lemma node_rhs {a : State} (ha : a ∈ nodeBox)
    (N : ℕ) (p : ℕ → State) (n : ℕ)
    (hp : ∀ j ≤ n, ‖p j‖ ≤ (displacementPolynomial N).coeff j) :
    ‖vectorTaylorRHS a p n‖ ≤ (scalarForcing (displacementPolynomial N)).coeff n := by
  have hzero : ‖if n=0 then field a else 0‖ ≤ (C 61 : ℝ[X]).coeff n := by
    by_cases hn : n=0
    · subst n
      simpa using node_field ha
    · simp [hn,coeff_C]
  have hl : ‖linear a (p n)‖ ≤ 17*(displacementPolynomial N).coeff n :=
    (node_linear ha _).trans
      (mul_le_mul_of_nonneg_left (hp n le_rfl) (by norm_num))
  have hq := node_quadratic ha N p n hp
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

theorem node_majorized {a : State} (ha : a ∈ nodeBox)
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
      have hbound := node_rhs ha N p n hprev
      rw [← hrec n (by omega),norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (by positivity),scalarForcing_recurrence N n (by omega)] at hbound
      by_contra hnot
      have hpos := mul_pos (by positivity : (0:ℝ)<n+1)
        (sub_pos.mpr (lt_of_not_ge hnot))
      nlinarith

theorem node_coeff {a : State} (ha : a∈nodeBox) (N : ℕ) :
    ∀ n≤N, ‖actualDisplacementCoeff a n‖≤(displacementPolynomial N).coeff n :=
  node_majorized ha N _ (actualDisplacementCoeff_zero a)
    (fun n _ => actualDisplacementCoeff_recurrence a n)

theorem node_polynomial {a : State} (ha : a∈nodeBox)
    (N n : ℕ) : ‖vectorPolynomialCoeff (actualDisplacementPolynomial a N) n‖≤
      (displacementPolynomial N).coeff n := by
  rw [actualDisplacementPolynomial_coeff]
  split_ifs with hn
  · exact node_coeff ha N n hn
  · simpa only [norm_zero] using displacementPolynomial_nonneg N n

theorem node_residual_coeff {a : State} (ha : a∈nodeBox) (N n : ℕ) :
    ‖vectorPolynomialCoeff (taylorResidual a N) n‖≤(scalarResidual N).coeff n := by
  by_cases hn : n<N
  · have hz : vectorPolynomialCoeff (taylorResidual a N) n=0 := by
      funext i
      exact taylorResidual_low_zero a N n hn i
    rw [hz,norm_zero,scalarResidual_low N n hn]
  · have hd : ∀i,(derivative (taylorPolynomial a N i)).coeff n=0 := by
      intro i
      rw [coeff_derivative,taylorPolynomial_coeff,if_neg (by omega),zero_mul]
    have he : vectorPolynomialCoeff (taylorResidual a N) n=
        -vectorPolynomialCoeff (polynomialField (taylorPolynomial a N)) n := by
      funext i
      simp only [vectorPolynomialCoeff,taylorResidual,coeff_sub,hd,zero_sub,Pi.neg_apply]
    rw [he,norm_neg,actualPolynomialField_displaced,displacedPolynomialField_coeff,
      ←scalarForcing_high N n (by omega)]
    exact node_rhs ha N _ n
      (fun j _=>node_polynomial ha N j)

/-- Actual polynomial's degree-60 velocity defect, uniform over the enlarged inputs. -/
theorem node_residual {a : State} (ha : a∈nodeBox) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (taylorResidual a 60) t‖ ≤ 1/10^57 :=
  (vectorPolynomialEval_norm_le _ _ (node_residual_coeff ha 60) t).trans
    (scalarResidual60_uniform (abs_nonneg t) ht).2

theorem node_excursion {a : State} (ha : a∈nodeBox) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (taylorPolynomial a 60) t-a‖ ≤ 129/250 := by
  change ‖(fun i => (taylorPolynomial a 60 i).eval t)-a‖ ≤ _
  rw [←actualDisplacementPolynomial_eval]
  exact (vectorPolynomialEval_norm_le _ _ (node_polynomial ha 60) t).trans
    (displacement60_uniform (abs_nonneg t) ht).2

end
end SolitonClassification.Rotating.IntegerWinding

#print axioms SolitonClassification.Rotating.IntegerWinding.node_residual
