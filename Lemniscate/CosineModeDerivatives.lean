import Lemniscate.PeriodicSecondCandidate

/-! Classical derivatives of the concrete cosine modes. The multiplier in
PeriodicSecondCandidate uses angular frequency; here the factor (2*pi/T)^2 is
kept explicitly for differentiation in the real coordinate of a circle of period T. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleFrequencyFactor (n : ℤ) : ℂ :=
  ((2*Real.pi/T*(n:ℝ):ℝ):ℂ)*I

theorem circle_frequency_factor_sq (n : ℤ) :
    (circleFrequencyFactor T n)^2 = ((-((2*Real.pi/T)^2*(n:ℝ)^2):ℝ):ℂ) := by
  unfold circleFrequencyFactor
  push_cast
  rw [mul_pow, Complex.I_sq]
  ring

theorem hasDerivAt_circle_fourier (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fourier n (y : AddCircle T))
      (circleFrequencyFactor T n * fourier n (x : AddCircle T)) x := by
  convert! hasDerivAt_fourier T n x using 1
  unfold circleFrequencyFactor
  push_cast
  ring

noncomputable def cosineModeValue (j : ℕ) (x : AddCircle T) : ℂ :=
  if j = 0 then fourier 0 x else
    evenCosineFactor*(fourier (2*(j:ℤ)) x + fourier (-(2*(j:ℤ))) x)

noncomputable def cosineModeFirstValue (j : ℕ) (x : AddCircle T) : ℂ :=
  if j = 0 then 0 else
    evenCosineFactor*(circleFrequencyFactor T (2*(j:ℤ))*fourier (2*(j:ℤ)) x +
      circleFrequencyFactor T (-(2*(j:ℤ)))*fourier (-(2*(j:ℤ))) x)

theorem cosine_mode_value_ae (j : ℕ) :
    (circleEvenCosineMode T j : AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle]
      cosineModeValue T j := by
  by_cases hj : j = 0
  · subst j
    have h := coeFn_fourierLp (T := T) 2 0
    filter_upwards [h] with x hx
    simpa only [circleEvenCosineMode, evenCosineMode, ite_true, cosineModeValue,
      coe_fourierBasis] using hx
  · simp only [circleEvenCosineMode, evenCosineMode, if_neg hj, coe_fourierBasis]
    filter_upwards [Lp.coeFn_smul evenCosineFactor
      (fourierLp (T := T) 2 (2*(j:ℤ)) + fourierLp (T := T) 2 (-(2*(j:ℤ)))),
      Lp.coeFn_add (fourierLp (T := T) 2 (2*(j:ℤ)))
        (fourierLp (T := T) 2 (-(2*(j:ℤ)))),
      coeFn_fourierLp (T := T) 2 (2*(j:ℤ)),
      coeFn_fourierLp (T := T) 2 (-(2*(j:ℤ)))] with x hs ha hp hn
    simp only [cosineModeValue, if_neg hj]
    calc
      _ = evenCosineFactor *
          ((fourierLp (T := T) 2 (2*(j:ℤ)) + fourierLp (T := T) 2 (-(2*(j:ℤ)))) x) := hs
      _ = evenCosineFactor *
          (fourierLp (T := T) 2 (2*(j:ℤ)) x + fourierLp (T := T) 2 (-(2*(j:ℤ))) x) := by
        simpa only [Pi.add_apply] using congrArg (fun z : ℂ => evenCosineFactor*z) ha
      _ = _ := by rw [hp, hn]

theorem hasDerivAt_cosine_mode (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => cosineModeValue T j (y : AddCircle T))
      (cosineModeFirstValue T j (x : AddCircle T)) x := by
  by_cases hj : j = 0
  · subst j
    simpa [cosineModeValue, cosineModeFirstValue, circleFrequencyFactor] using
      hasDerivAt_circle_fourier T 0 x
  · simp only [cosineModeValue, cosineModeFirstValue, if_neg hj]
    exact ((hasDerivAt_circle_fourier T (2*(j:ℤ)) x).add
      (hasDerivAt_circle_fourier T (-(2*(j:ℤ))) x)).const_mul evenCosineFactor

theorem hasDerivAt_cosine_mode_first (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => cosineModeFirstValue T j (y : AddCircle T))
      ((((2*Real.pi/T)^2:ℝ):ℂ) * ((-(2*(j:ℝ))^2:ℝ):ℂ) *
        cosineModeValue T j (x : AddCircle T)) x := by
  by_cases hj : j = 0
  · subst j
    simpa [cosineModeFirstValue] using (hasDerivAt_const x (0:ℂ))
  · simp only [cosineModeFirstValue, cosineModeValue, if_neg hj]
    have h := (((hasDerivAt_circle_fourier T (2*(j:ℤ)) x).const_mul
      (circleFrequencyFactor T (2*(j:ℤ)))).add
      ((hasDerivAt_circle_fourier T (-(2*(j:ℤ))) x).const_mul
        (circleFrequencyFactor T (-(2*(j:ℤ)))))).const_mul evenCosineFactor
    convert! h using 1
    have hp := circle_frequency_factor_sq T (2*(j:ℤ))
    have hn := circle_frequency_factor_sq T (-(2*(j:ℤ)))
    push_cast at hp hn ⊢
    calc
      _ = evenCosineFactor*((circleFrequencyFactor T (2*(j:ℤ)))^2 *
          fourier (2*(j:ℤ)) (x : AddCircle T) +
          (circleFrequencyFactor T (-(2*(j:ℤ))))^2 *
          fourier (-(2*(j:ℤ))) (x : AddCircle T)) := by rw [hp, hn]; ring
      _ = _ := by ring

noncomputable def cosinePartialValue (v : ℕ → ℂ) (N : ℕ) (x : AddCircle T) : ℂ :=
  ∑ j ∈ Finset.range N, v j * cosineModeValue T j x

noncomputable def cosinePartialFirstValue (v : ℕ → ℂ) (N : ℕ) (x : AddCircle T) : ℂ :=
  ∑ j ∈ Finset.range N, v j * cosineModeFirstValue T j x

theorem hasDerivAt_cosine_partial (v : ℕ → ℂ) (N : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => cosinePartialValue T v N (y : AddCircle T))
      (cosinePartialFirstValue T v N (x : AddCircle T)) x := by
  exact HasDerivAt.fun_sum (fun j _ => (hasDerivAt_cosine_mode T j x).const_mul (v j))

theorem hasDerivAt_cosine_partial_first (v : ℕ → ℂ) (N : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => cosinePartialFirstValue T v N (y : AddCircle T))
      ((((2*Real.pi/T)^2:ℝ):ℂ) *
        cosinePartialValue T (evenSecondCoefficients v) N (x : AddCircle T)) x := by
  have h := HasDerivAt.fun_sum (u := Finset.range N)
    (fun j _ => (hasDerivAt_cosine_mode_first T j x).const_mul (v j))
  convert! h using 1
  unfold cosinePartialValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold evenSecondCoefficients
  ring

end Lemniscate
