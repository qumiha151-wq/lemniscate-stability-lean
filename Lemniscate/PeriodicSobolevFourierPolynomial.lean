import Lemniscate.PeriodicSobolevSpace
import Lemniscate.PeriodicAdjointFourier
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Data.Complex.BigOperators

/-! Fourier modes and arbitrary finite Fourier reconstruction in the complete
periodic Sobolev spaces. Coordinate j is the actual weak derivative of order j.
The finite coefficient synthesis is a continuous linear map; its source is
the finite coefficient space indexed by I, not the full infinite product.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal ComplexConjugate BigOperators

variable (T : ℝ) [Fact (0 < T)]

def circleSobolevFourierMode (m : ℕ) (n : ℤ) : CircleSobolevSpace T m :=
  ⟨WithLp.toLp 2 (fun j : Fin (m+1) =>
      (circleFrequencyFactor T n)^j.val • fourierBasis (T := T) n),by
    apply (circle_sobolev_jet_mem_iff T m _).mpr
    intro j
    simp only [PiLp.toLp_apply]
    change HasWeakCircleDeriv T
      ((circleFrequencyFactor T n)^j.val • fourierBasis (T := T) n)
      ((circleFrequencyFactor T n)^(j.val+1) • fourierBasis (T := T) n)
    exact circle_fourier_power_weak_deriv T n j.val⟩

@[simp] theorem circle_sobolev_fourier_mode_coordinate (m : ℕ) (n : ℤ)
    (j : Fin (m+1)) :
    circleSobolevCoordinate T m j (circleSobolevFourierMode T m n) =
      (circleFrequencyFactor T n)^j.val • fourierBasis (T := T) n := rfl

def circleSobolevFourierPolynomial (m : ℕ) (I : Finset ℤ) (c : ℤ → ℂ) :
    CircleSobolevSpace T m :=
  ∑ n ∈ I, c n • circleSobolevFourierMode T m n

/-- Every Sobolev coordinate is exactly the corresponding differentiated
Fourier polynomial. In particular j=0 gives the value polynomial. -/
theorem circle_sobolev_fourier_polynomial_coordinate (m : ℕ) (I : Finset ℤ)
    (c : ℤ → ℂ) (j : Fin (m+1)) :
    circleSobolevCoordinate T m j (circleSobolevFourierPolynomial T m I c) =
      ∑ n ∈ I, ((circleFrequencyFactor T n)^j.val*c n) • fourierBasis (T := T) n := by
  simp only [circleSobolevFourierPolynomial,map_sum,map_smul,
    circle_sobolev_fourier_mode_coordinate,smul_smul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_comm (c n)]

/-- Reconstruction of arbitrary coefficients on a fixed finite set as a
continuous linear map into the actual Sobolev Hilbert space. -/
def circleSobolevFourierSynthesis (m : ℕ) (I : Finset ℤ) :
    (I → ℂ) →L[ℂ] CircleSobolevSpace T m :=
  ∑ n : I, (ContinuousLinearMap.proj n).smulRight (circleSobolevFourierMode T m (n:ℤ))

theorem circle_sobolev_fourier_synthesis_restrict (m : ℕ) (I : Finset ℤ)
    (c : ℤ → ℂ) :
    circleSobolevFourierSynthesis T m I (fun n : I => c n) =
      circleSobolevFourierPolynomial T m I c := by
  simp only [circleSobolevFourierSynthesis,circleSobolevFourierPolynomial,
    sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]
  exact Finset.sum_coe_sort I (fun n => c n • circleSobolevFourierMode T m n)

/-- The norm is the derivative square-sum Sobolev norm. Orthogonality of the
actual Fourier basis gives its exact finite coefficient weight. -/
theorem circle_sobolev_fourier_polynomial_norm_sq (m : ℕ) (I : Finset ℤ)
    (c : ℤ → ℂ) :
    ‖circleSobolevFourierPolynomial T m I c‖^2 =
      ∑ n ∈ I, ‖c n‖^2*
        (∑ j : Fin (m+1), ‖circleFrequencyFactor T n‖^(2*j.val)) := by
  calc
    ‖circleSobolevFourierPolynomial T m I c‖^2 =
        ∑ j : Fin (m+1), ∑ n ∈ I, ‖(circleFrequencyFactor T n)^j.val*c n‖^2 := by
      rw [circle_sobolev_norm_sq]
      apply Finset.sum_congr rfl
      intro j hj
      rw [circle_sobolev_fourier_polynomial_coordinate,norm_sq_eq_re_inner (𝕜 := ℂ),
        (fourierBasis (T := T)).orthonormal.inner_sum]
      simp only [Complex.re_sum,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re]
      change (RCLike.reCLM : ℂ →L[ℝ] ℝ)
        (∑ n ∈ I, ((‖(circleFrequencyFactor T n)^j.val*c n‖^2 : ℝ) : ℂ)) = _
      simp only [map_sum,RCLike.reCLM_apply]
      apply Finset.sum_congr rfl
      intro n hn
      rfl
    _ = ∑ n ∈ I, ‖c n‖^2*
        (∑ j : Fin (m+1), ‖circleFrequencyFactor T n‖^(2*j.val)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul,norm_pow,mul_pow,← pow_mul,Nat.mul_comm j.val 2]
      ring

end Lemniscate
