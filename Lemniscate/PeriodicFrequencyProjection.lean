import Lemniscate.PeriodicBlochOddLimit
import Lemniscate.PeriodicBoundedMultiplier

/-! Fourier parity projections on the actual L2 and weak H4 spaces. The
projection commutes with a Bloch operator whose coefficients have only even
Fourier indices. This suffices to split eigenvectors, without a new energy
calculation on the full space. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleEvenProjection : CircleL2 T →L[ℂ] CircleL2 T :=
  circleBoundedMultiplier T (fun n => if Even n then 1 else 0) 1 (by norm_num)
    (by intro n; split_ifs <;> norm_num)

theorem circle_even_projection_fourier (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleEvenProjection T f) n =
      (if Even n then (1:ℂ) else 0)*fourierCoeff f n :=
  circle_bounded_multiplier_fourier T _ _ _ _ f n

theorem circle_even_projection_basis (m : ℤ) :
    circleEvenProjection T (fourierBasis (T := T) m) =
      (if Even m then (1:ℂ) else 0) • fourierBasis (T := T) m := by
  apply circle_fourier_ext T
  intro n
  rw [circle_even_projection_fourier,circle_fourierCoeff_smul,
    ← circle_continuous_l2_fourier_basis, circle_continuous_l2_fourier,
    circle_continuous_fourier_mode]
  by_cases h : n = m
  · subst n
    rfl
  · simp only [if_neg h,mul_zero]

theorem circle_even_projection_mem_h4 (f : circleH4Domain T) :
    InCircleH4 T (circleEvenProjection T (f:CircleL2 T)) := by
  apply circle_h4_of_fourth_fourier T _ (circleEvenProjection T (circleH4Jet T f).fourth)
  intro n
  rw [circle_even_projection_fourier,circle_even_projection_fourier,circle_h4_fourth_fourier]
  ring

noncomputable def circleEvenProjectionH4 (f : circleH4Domain T) : circleH4Domain T :=
  ⟨circleEvenProjection T (f:CircleL2 T),circle_even_projection_mem_h4 T f⟩

theorem circle_even_projection_h4_coe (f : circleH4Domain T) :
    (circleEvenProjectionH4 T f:CircleL2 T) = circleEvenProjection T (f:CircleL2 T) := rfl

theorem circle_even_projection_derivative (f : circleH4Domain T) (j : Fin 4) :
    circleH4Derivative T j (circleEvenProjectionH4 T f) =
      circleEvenProjection T (circleH4Derivative T j f) := by
  apply circle_fourier_ext T
  intro n
  rw [circle_h4_derivative_fourier,circle_even_projection_fourier,circle_h4_derivative_fourier]
  change fourierCoeff (circleEvenProjection T (f:CircleL2 T)) n*
    (circleFrequencyFactor T n)^(j.val+1) = _
  rw [circle_even_projection_fourier]
  ring

theorem circle_even_projection_multiply_basis (h : C(AddCircle T, ℂ))
    (ho : ∀ n : ℤ, Odd n → fourierCoeff h n = 0) (m : ℤ) :
    circleEvenProjection T (circleMultiplyL2 T h (fourierBasis (T := T) m)) =
      circleMultiplyL2 T h (circleEvenProjection T (fourierBasis (T := T) m)) := by
  apply circle_fourier_ext T
  intro n
  rw [circle_even_projection_fourier,circle_even_projection_basis,map_smul,
    circle_fourierCoeff_smul,circle_multiply_basis_fourier]
  by_cases hn : Even n <;> by_cases hm : Even m
  · simp only [if_pos hn,if_pos hm]
  · have hod : Odd (n-m) := Int.odd_sub'.mpr (by simp [hn,Int.not_even_iff_odd.mp hm])
    simp only [if_pos hn,if_neg hm,ho _ hod,mul_zero]
  · have hod : Odd (n-m) := Int.odd_sub.mpr (by simp [hm,Int.not_even_iff_odd.mp hn])
    simp only [if_neg hn,if_pos hm,ho _ hod,mul_zero]
  · simp only [if_neg hn,if_neg hm]

theorem circle_even_projection_multiply (h : C(AddCircle T, ℂ))
    (ho : ∀ n : ℤ, Odd n → fourierCoeff h n = 0) (f : CircleL2 T) :
    circleEvenProjection T (circleMultiplyL2 T h f) =
      circleMultiplyL2 T h (circleEvenProjection T f) := by
  let F := (circleEvenProjection T).comp (circleMultiplyL2 T h)
  let G := (circleMultiplyL2 T h).comp (circleEvenProjection T)
  have hb (m : ℤ) : F (fourierBasis (T := T) m) = G (fourierBasis (T := T) m) :=
    circle_even_projection_multiply_basis T h ho m
  have hF := ((fourierBasis (T := T)).hasSum_repr f).mapL F
  have hG := ((fourierBasis (T := T)).hasSum_repr f).mapL G
  simp only [map_smul,hb] at hF
  simp only [map_smul] at hG
  exact hF.unique hG

theorem circle_even_projection_bloch (h h₁ h₂ : C(AddCircle T, ℂ))
    (ho : ∀ n : ℤ, Odd n → fourierCoeff h n = 0)
    (ho₁ : ∀ n : ℤ, Odd n → fourierCoeff h₁ n = 0)
    (ho₂ : ∀ n : ℤ, Odd n → fourierCoeff h₂ n = 0)
    (α : ℝ) (f : circleH4Domain T) :
    circleBlochOperator T h h₁ h₂ α (circleEvenProjectionH4 T f) =
      circleEvenProjection T (circleBlochOperator T h h₁ h₂ α f) := by
  simp only [circle_bloch_operator_expanded,circle_even_projection_derivative,
    circle_even_projection_h4_coe,map_add,map_sub,map_smul,
    circle_even_projection_multiply T h ho,circle_even_projection_multiply T h₁ ho₁,
    circle_even_projection_multiply T h₂ ho₂]

theorem circle_even_projection_is_even (f : CircleL2 T) (n : ℤ) (hn : Odd n) :
    fourierCoeff (circleEvenProjection T f) n = 0 := by
  rw [circle_even_projection_fourier,if_neg (Int.not_even_iff_odd.mpr hn),zero_mul]

theorem circle_odd_remainder_is_odd (f : CircleL2 T) :
    InCircleOddSector T (f-circleEvenProjection T f) := by
  intro n hn
  rw [circle_fourierCoeff_sub,circle_even_projection_fourier,
    if_pos (Int.not_odd_iff_even.mp hn),one_mul,sub_self]

end Lemniscate
