import Lemniscate.PeriodicBlochOddFinite

/-! Transfer the certified odd Bloch estimate to every actual H4 function in
the odd-frequency sector, by simultaneous convergence of all four derivatives. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic OddArithmetic Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

theorem circle_h4_derivative_basis (j : Fin 4) (n : ℤ) :
    circleH4Derivative T j (circleFourierH4 T n) =
      (circleFrequencyFactor T n)^(j.val+1) • fourierBasis (T := T) n := by
  have hj : circleH4Jet T (circleFourierH4 T n) = circleFourierH4Jet T n :=
    circle_fourier_h4_jet T n
  fin_cases j
  · change (circleH4Jet T (circleFourierH4 T n)).first =
      (circleFrequencyFactor T n)^1 • fourierBasis (T := T) n
    rw [hj]
    simp only [circleFourierH4Jet, pow_one]
  · change (circleH4Jet T (circleFourierH4 T n)).second =
      (circleFrequencyFactor T n)^2 • fourierBasis (T := T) n
    rw [hj]
    rfl
  · change (circleH4Jet T (circleFourierH4 T n)).third =
      (circleFrequencyFactor T n)^3 • fourierBasis (T := T) n
    rw [hj]
    rfl
  · change (circleH4Jet T (circleFourierH4 T n)).fourth =
      (circleFrequencyFactor T n)^4 • fourierBasis (T := T) n
    rw [hj]
    rfl

theorem circle_h4_derivative_fourier (f : circleH4Domain T) (j : Fin 4) (n : ℤ) :
    fourierCoeff (circleH4Derivative T j f) n =
      fourierCoeff (f : CircleL2 T) n*(circleFrequencyFactor T n)^(j.val+1) := by
  have h1 := fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hfirst n
  have h2 := fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hsecond n
  have h3 := fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hthird n
  have h4 := fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hfourth n
  fin_cases j
  · change fourierCoeff (circleH4Jet T f).first n =
      fourierCoeff (f : CircleL2 T) n*(circleFrequencyFactor T n)^1
    rw [h1]
    ring
  · change fourierCoeff (circleH4Jet T f).second n =
      fourierCoeff (f : CircleL2 T) n*(circleFrequencyFactor T n)^2
    rw [h2, h1]
    ring
  · change fourierCoeff (circleH4Jet T f).third n =
      fourierCoeff (f : CircleL2 T) n*(circleFrequencyFactor T n)^3
    rw [h3, h2, h1]
    ring
  · change fourierCoeff (circleH4Jet T f).fourth n =
      fourierCoeff (f : CircleL2 T) n*(circleFrequencyFactor T n)^4
    rw [h4, h3, h2, h1]
    ring

theorem circle_odd_polynomial_h4_derivative (I : Finset ℤ) (v : ℤ → ℂ) (j : Fin 4) :
    circleH4Derivative T j (circleOddPolynomialH4 T I v) =
      circleContinuousL2 T (circleOddPolynomial T I v (j.val+1)) := by
  simp only [circleOddPolynomialH4, map_sum, map_smul, circle_h4_derivative_basis,
    circle_odd_polynomial_l2, smul_smul]

theorem circle_odd_polynomial_h4_derivative_tendsto (f : circleH4Domain T)
    (hf : InCircleOddSector T (f : CircleL2 T)) (j : Fin 4) :
    Tendsto (fun I : Finset ℤ => circleH4Derivative T j
      (circleOddPolynomialH4 T I (fun i => fourierCoeff (f : CircleL2 T) (2*i+1))))
        atTop (𝓝 (circleH4Derivative T j f)) := by
  have hj : InCircleOddSector T (circleH4Derivative T j f) := by
    intro n hn
    rw [circle_h4_derivative_fourier, hf n hn, zero_mul]
  have ht : Tendsto (fun I : Finset ℤ =>
      ∑ i ∈ I, fourierCoeff (circleH4Derivative T j f) (2*i+1) •
        fourierBasis (T := T) (2*i+1)) atTop (𝓝 (circleH4Derivative T j f)) :=
    circle_odd_fourier_hasSum T _ hj
  simpa only [circle_odd_polynomial_h4_derivative, circle_odd_polynomial_l2,
    circle_h4_derivative_fourier] using ht

theorem circle_bloch_operator_expanded (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ)
    (f : circleH4Domain T) :
    circleBlochOperator T h h₁ h₂ α f =
      (-4:ℂ) • (circleH4Derivative T 3 f+
        (4*((α:ℂ)*circleFrequencyFactor T 1)) • circleH4Derivative T 2 f+
        (6*((α:ℂ)*circleFrequencyFactor T 1)^2) • circleH4Derivative T 1 f+
        (4*((α:ℂ)*circleFrequencyFactor T 1)^3) • circleH4Derivative T 0 f+
        ((α:ℂ)*circleFrequencyFactor T 1)^4 • (f : CircleL2 T))-
      (45:ℂ) • circleMultiplyL2 T h (circleH4Derivative T 1 f+
        (2*((α:ℂ)*circleFrequencyFactor T 1)) • circleH4Derivative T 0 f+
        ((α:ℂ)*circleFrequencyFactor T 1)^2 • (f : CircleL2 T))-
      (75/2:ℂ) • circleMultiplyL2 T h₁ (circleH4Derivative T 0 f+
        ((α:ℂ)*circleFrequencyFactor T 1) • (f : CircleL2 T))-
      (42:ℂ) • (f : CircleL2 T)+(15/2:ℂ) • circleMultiplyL2 T h₂ (f : CircleL2 T) := rfl

theorem circle_bloch_operator_tendsto {ι : Type*} {l : Filter ι}
    (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ) (u : ι → circleH4Domain T) (f : circleH4Domain T)
    (hu : Tendsto (fun i => (u i : CircleL2 T)) l (𝓝 (f : CircleL2 T)))
    (hd : ∀ j : Fin 4, Tendsto (fun i => circleH4Derivative T j (u i)) l
      (𝓝 (circleH4Derivative T j f))) :
    Tendsto (fun i => circleBlochOperator T h h₁ h₂ α (u i)) l
      (𝓝 (circleBlochOperator T h h₁ h₂ α f)) := by
  let z : ℂ := (α:ℂ)*circleFrequencyFactor T 1
  have hfirst := (hd 0).add (hu.const_smul z)
  have hsecond := ((hd 1).add ((hd 0).const_smul (2*z))).add (hu.const_smul (z^2))
  have hfourth := ((((hd 3).add ((hd 2).const_smul (4*z))).add
    ((hd 1).const_smul (6*z^2))).add ((hd 0).const_smul (4*z^3))).add (hu.const_smul (z^4))
  have hm1 := ((circleMultiplyL2 T h₁).continuous.tendsto _).comp hfirst
  have hm2 := ((circleMultiplyL2 T h).continuous.tendsto _).comp hsecond
  have hm0 := ((circleMultiplyL2 T h₂).continuous.tendsto _).comp hu
  simpa only [circle_bloch_operator_expanded, z, Function.comp_def] using
    ((((hfourth.const_smul (-4:ℂ)).sub (hm2.const_smul (45:ℂ))).sub
      (hm1.const_smul (75/2:ℂ))).sub (hu.const_smul (42:ℂ))).add (hm0.const_smul (15/2:ℂ))

theorem circle_odd_bloch_energy_eq_coefficients (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2)
    (f : circleH4Domain T) (hf : InCircleOddSector T (f : CircleL2 T)) :
    (inner ℂ (f : CircleL2 T) (circleBlochOperator T h h₁ h₂ α f)).re =
      oddH2Form α (fun i => fourierCoeff (f : CircleL2 T) (2*i+1)) := by
  let v : ℤ → ℂ := fun i => fourierCoeff (f : CircleL2 T) (2*i+1)
  have hu : Tendsto (fun I : Finset ℤ => (circleOddPolynomialH4 T I v : CircleL2 T))
      atTop (𝓝 (f : CircleL2 T)) := by
    simpa only [circle_odd_polynomial_h4_coe] using circle_odd_polynomial_tendsto T _ hf
  have ha := circle_bloch_operator_tendsto T h h₁ h₂ α (fun I : Finset ℤ => circleOddPolynomialH4 T I v)
    f hu (circle_odd_polynomial_h4_derivative_tendsto T f hf)
  have he := (Complex.continuous_re.tendsto _).comp (hu.inner ha)
  have hv := circle_odd_h2_coefficients T (f : CircleL2 T) (circle_h4_mem_h2 T f) hr
  have hm : Tendsto (fun I : Finset ℤ =>
      (inner ℂ (circleOddPolynomialH4 T I v : CircleL2 T)
        (circleBlochOperator T h h₁ h₂ α (circleOddPolynomialH4 T I v))).re)
      atTop (𝓝 (oddH2Form α v)) := by
    simpa only [circle_odd_polynomial_bloch_energy T h h₁ h₂ hh hh₁ hs hc hr,
      oddH2Form, Function.comp_def] using
        (Complex.continuous_re.tendsto _).comp (odd_energy_tendsto v hv α hα hα')
  exact tendsto_nhds_unique he hm

theorem circle_h4_bloch_odd_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2)
    (f : circleH4Domain T) (hf : InCircleOddSector T (f : CircleL2 T)) :
    (inner ℂ (f : CircleL2 T) (circleBlochOperator T h h₁ h₂ α f)).re ≤ -‖(f : CircleL2 T)‖^2 := by
  rw [circle_odd_bloch_energy_eq_coefficients T h h₁ h₂ hh hh₁ hs hc hr α hα hα' f hf,
    circle_odd_norm_sq T (f : CircleL2 T) hf]
  exact odd_h2_form_dissipative _ (circle_odd_h2_coefficients T _ (circle_h4_mem_h2 T f) hr) α hα hα'

theorem paper_h4_bloch_odd_dissipative (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2)
    (f : circleH4Domain T) (hf : InCircleOddSector T (f : CircleL2 T)) :
    (inner ℂ (f : CircleL2 T)
      (circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α f)).re ≤
        -‖(f : CircleL2 T)‖^2 :=
  circle_h4_bloch_odd_dissipative T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
    (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
    hs hc hr α hα hα' f hf

end Lemniscate
