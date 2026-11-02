import Lemniscate.PeriodicEvenHead
import Lemniscate.PeriodicFiniteHighEnergy

/-! Ordinary Fourier coordinates of the actual finite neutral vectors.
Development source for identifying the finite quadratic-form certificate. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

noncomputable def finiteSineCoordinate (v : Fin 15 → ℝ) (i : Fin 31) : ℝ :=
  if hi : i.val < 15 then -(v ⟨14-i.val, by omega⟩)/Real.sqrt 2
  else if hi : 15 < i.val then v ⟨i.val-16, by omega⟩/Real.sqrt 2
  else 0

variable (T : ℝ) [Fact (0 < T)]

theorem circle_even_head_inner (v w : Fin 31 → ℂ) :
    inner ℂ (circleEvenHeadH4 T v : CircleL2 T) (circleEvenHeadH4 T w : CircleL2 T) =
      ∑ i, conj (v i)*w i := by
  have hon := (fourierBasis (T := T)).orthonormal.comp evenHeadFrequency
    even_head_frequency_injective
  simpa only [circle_even_head_h4_coe, Function.comp_apply] using
    hon.inner_sum v w Finset.univ

theorem circle_even_head_projection_of_support (f : circleH4Domain T)
    (hf : ∀ n : ℤ, ¬(Even n ∧ |(n:ℝ)| < 32) → fourierCoeff (f : CircleL2 T) n = 0) :
    circleEvenHeadProjection T f = f := by
  apply Subtype.ext
  apply circle_fourier_ext T
  intro n
  by_cases hn : ∃ i : Fin 31, evenHeadFrequency i = n
  · obtain ⟨i, rfl⟩ := hn
    exact circle_even_head_fourier_at T _ i
  · rw [circleEvenHeadProjection, circle_even_head_fourier_outside,
      hf n (by simpa only [← even_head_frequency_range] using hn)]
    intro i hi
    exact hn ⟨i, hi.symm⟩

theorem circle_sine_phase_fourier (v : Fin 15 → ℝ) (n : ℤ) :
    fourierCoeff ((I • circleSineTrialH4 T 15 (fun j => (v j:ℂ)) : circleH4Domain T) :
      CircleL2 T) n =
      ∑ j : Fin 15, (v j:ℂ)*evenCosineFactor*
        ((if n = 2*((j.val+1:ℕ):ℤ) then 1 else 0)-
          (if n = -(2*((j.val+1:ℕ):ℤ)) then 1 else 0)) := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  change inner ℂ (fourierBasis (T := T) n)
    (I • ∑ j : Fin 15, (v j:ℂ) • (evenSineFactor •
      (fourierBasis (T := T) (2*((j.val+1:ℕ):ℤ))-
        fourierBasis (T := T) (-(2*((j.val+1:ℕ):ℤ)))))) = _
  simp only [inner_smul_right, inner_sum, inner_sub_right,
    orthonormal_iff_ite.mp (fourierBasis (T := T)).orthonormal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold evenSineFactor
  ring_nf
  simp only [Complex.I_sq]
  ring

set_option maxHeartbeats 2000000 in
theorem circle_sine_phase_fourier_at (v : Fin 15 → ℝ) (i : Fin 31) :
    fourierCoeff ((I • circleSineTrialH4 T 15 (fun j => (v j:ℂ)) : circleH4Domain T) :
      CircleL2 T) (evenHeadFrequency i) = (finiteSineCoordinate v i:ℂ) := by
  rw [circle_sine_phase_fourier]
  fin_cases i <;>
    norm_num [finiteSineCoordinate, evenHeadFrequency, Fin.sum_univ_succ,
      evenCosineFactor] <;> push_cast <;> ring

theorem circle_sine_phase_head (v : Fin 15 → ℝ) :
    I • circleSineTrialH4 T 15 (fun j => (v j:ℂ)) =
      circleEvenHeadH4 T (fun i => (finiteSineCoordinate v i:ℂ)) := by
  let f := I • circleSineTrialH4 T 15 (fun j => (v j:ℂ))
  have hsupp (n : ℤ) (hn : ¬(Even n ∧ |(n:ℝ)| < 32)) :
      fourierCoeff (f : CircleL2 T) n = 0 := by
    have hpos (j : Fin 15) : n ≠ 2*((j.val+1:ℕ):ℤ) := by
      intro he
      apply hn
      apply (even_head_frequency_range n).mp
      refine ⟨⟨j.val+16, by omega⟩, ?_⟩
      dsimp only [evenHeadFrequency]
      omega
    have hneg (j : Fin 15) : n ≠ -(2*((j.val+1:ℕ):ℤ)) := by
      intro he
      apply hn
      apply (even_head_frequency_range n).mp
      refine ⟨⟨14-j.val, by omega⟩, ?_⟩
      have hj := j.isLt
      dsimp only [evenHeadFrequency]
      omega
    rw [circle_sine_phase_fourier]
    simp only [if_neg (hpos _), if_neg (hneg _), sub_self, mul_zero, Finset.sum_const_zero]
  have hp := circle_even_head_projection_of_support T f hsupp
  calc
    f = circleEvenHeadProjection T f := hp.symm
    _ = _ := by
      unfold circleEvenHeadProjection
      congr 1
      funext i
      exact circle_sine_phase_fourier_at T v i

theorem circle_finite_rotation_phase_head :
    circleFiniteRotationPhase T =
      circleEvenHeadH4 T (fun i => (finiteSineCoordinate rotationFiniteCoefficient i:ℂ)) := by
  exact circle_sine_phase_head T rotationFiniteCoefficient

theorem circle_finite_adjoint_phase_head :
    circleFiniteAdjointPhase T =
      (circleEvenHeadH4 T (fun i => (finiteSineCoordinate adjointFiniteCoefficient i:ℂ)) :
        CircleL2 T) := by
  exact congrArg (fun f : circleH4Domain T => (f : CircleL2 T))
    (circle_sine_phase_head T adjointFiniteCoefficient)

theorem circle_finite_phase_normalization :
    ‖(circleFiniteRotationPhase T : CircleL2 T)‖ = 1 ∧
    inner ℂ (circleFiniteAdjointPhase T) (circleFiniteRotationPhase T : CircleL2 T) = 1 := by
  rcases circle_finite_normalization_bounds T with ⟨he, hp, _⟩
  constructor
  · change ‖I • (circleRotationApproximation T : CircleL2 T)‖ = 1
    rw [norm_smul, Complex.norm_I, one_mul, he]
  · change inner ℂ (I • (circleAdjointApproximation T : CircleL2 T))
      (I • (circleRotationApproximation T : CircleL2 T)) = 1
    rw [inner_smul_left, inner_smul_right, hp, Complex.conj_I]
    norm_num

end Lemniscate
