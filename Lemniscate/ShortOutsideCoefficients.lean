import Lemniscate.ShortOutsideTransforms

namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0<T)]

theorem circle_short_head_single (i : Fin 15) :
    circleShortHead T (Pi.single i 1)=circleFourierH4 T (shortHeadFrequency i) := by
  simp [circleShortHead]

theorem circle_short_operator_head_fourier
    (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) (v : Fin 15 → ℂ) (n : ℤ) :
    fourierCoeff (A (circleShortHead T v)) n =
      ∑ i, v i*fourierCoeff (A (circleFourierH4 T (shortHeadFrequency i))) n := by
  have hf (f : CircleL2 T) : fourierCoeff f n=inner ℂ (fourierBasis (T:=T) n) f := by
    rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  simp only [hf,circleShortHead,
    LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,inner_sum,inner_smul_right]

section Coefficients
variable (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ,fourierCoeff h (-n)=fourierCoeff h n)
    (hc : ∀ j : ℕ,fourierCoeff h (2*(j:ℤ))=(shortActualCoefficient j:ℂ))
    (hr : (2*Real.pi/T)^2=lemniscateFrequencySquared)

include hh hh₁ hs hc hr in
theorem circle_short_bloch_basis_fourier (j : Fin 5) (n m : ℤ) :
    fourierCoeff (circleBlochCoefficient T h h₁ h₂ j (circleFourierH4 T (2*m))) (2*n)=
      (shortBlochEntry lemniscateFrequencySquared shortActualCoefficient j (2*n) (2*m):ℂ) := by
  rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  exact short_circle_bloch_basis_pairing T h h₁ h₂ hh hh₁ _ _ hs hc hr j n m

include hh hh₁ hs hc hr in
theorem circle_short_bloch_head_outside (j : Fin 5) (n : ℤ) :
    circleShortHeadCoordinates T
      (circleBlochCoefficient T h h₁ h₂ j (circleFourierH4 T (2*n)))=
      fun i => (shortBlochEntry lemniscateFrequencySquared shortActualCoefficient j
        (shortHeadFrequency i) (2*n):ℂ) := by
  funext i
  have hf : shortHeadFrequency i=2*((i.val:ℤ)-7) := by
    dsimp only [shortHeadFrequency]
    ring
  simp only [circleShortHeadCoordinates,hf]
  exact circle_short_bloch_basis_fourier T h h₁ h₂ hh hh₁ hs hc hr j _ n

include hh hh₁ hs hc hr in
theorem circle_short_bloch_outside_head (j : Fin 5) (v : Fin 15 → ℂ) (n : ℤ) :
    fourierCoeff (circleBlochCoefficient T h h₁ h₂ j (circleShortHead T v)) (2*n)=
      ∑ i, v i*(shortBlochEntry lemniscateFrequencySquared shortActualCoefficient j
        (2*n) (shortHeadFrequency i):ℂ) := by
  rw [circle_short_operator_head_fourier]
  apply Finset.sum_congr rfl
  intro i _
  have hf : shortHeadFrequency i=2*((i.val:ℤ)-7) := by
    dsimp only [shortHeadFrequency]
    ring
  rw [hf,circle_short_bloch_basis_fourier T h h₁ h₂ hh hh₁ hs hc hr]

include hh hh₁ hs hc hr in
theorem circle_short_transformed_head_outside (j : Fin 5) (n : ℤ)
    (hn : shortHeadIndex n=none) :
    circleShortHeadCoordinates T
      (circleShortTransformedCoefficient T h h₁ h₂ j (circleFourierH4 T (2*n)))=
      shortComplexMatrix (shortHouseholder shortActualCoefficient*
        shortNeutral shortActualCoefficient)*ᵥ
      (fun i => (shortBlochEntry lemniscateFrequencySquared shortActualCoefficient j
        (shortHeadFrequency i) (2*n):ℂ)) := by
  unfold circleShortTransformedCoefficient circleShortHouseholder circleShortHouseholderH4
  rw [← circle_householder_anchor_h4_coe T,circle_short_rotation_head,
    circle_short_adjoint_head,circle_short_anchor_head]
  rw [circle_short_head_householder_outside T _ _ _ (short_outside_frequency_ne n hn),
    circle_short_head_neutral_inv_outside T _ _ _ (short_outside_frequency_ne n hn),
    circle_short_head_coordinates_householder,circle_short_head_coordinates_neutral,
    short_householder_matrix_real,short_neutral_matrix_real,
    circle_short_bloch_head_outside T h h₁ h₂ hh hh₁ hs hc hr]
  rw [short_complex_matrix_mul,Matrix.mulVec_mulVec]

include hh hh₁ hs hc hr in
theorem circle_short_transformed_outside_head (j : Fin 5) (v : Fin 15 → ℂ)
    (n : ℤ) (hn : shortHeadIndex n=none) :
    fourierCoeff (circleShortTransformedCoefficient T h h₁ h₂ j (circleShortHead T v)) (2*n)=
      ∑ i, (shortComplexMatrix (shortNeutralInv shortActualCoefficient*
        shortHouseholder shortActualCoefficient)*ᵥv) i *
        (shortBlochEntry lemniscateFrequencySquared shortActualCoefficient j
          (2*n) (shortHeadFrequency i):ℂ) := by
  unfold circleShortTransformedCoefficient circleShortHouseholder circleShortHouseholderH4
  rw [← circle_householder_anchor_h4_coe T,circle_short_rotation_head,
    circle_short_adjoint_head,circle_short_anchor_head]
  rw [circle_short_householder_output_outside T _ _ _ _ (short_outside_frequency_ne n hn),
    circle_short_neutral_output_outside T _ _ _ _ (short_outside_frequency_ne n hn),
    circle_short_head_householder,circle_short_head_neutral_inv,
    short_householder_matrix_real,short_neutral_inv_matrix_real,
    circle_short_bloch_outside_head T h h₁ h₂ hh hh₁ hs hc hr]
  rw [short_complex_matrix_mul,Matrix.mulVec_mulVec]

end Coefficients
end Lemniscate
