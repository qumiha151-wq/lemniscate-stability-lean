import Lemniscate.ShortKernelIdentification

namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0<T)]

theorem circle_fixed_projection_sum {ι : Type*} (I : Finset ι)
    (f : ι → circleH4Domain T) :
    circleFixedProjectionH4 T (∑ i∈I,f i)=∑ i∈I,circleFixedProjectionH4 T (f i) := by
  simp only [circleFixedProjectionH4,Submodule.coe_sum,inner_sum,Finset.sum_smul]

theorem circle_fixed_projection_smul (c : ℂ) (f : circleH4Domain T) :
    circleFixedProjectionH4 T (c • f)=c • circleFixedProjectionH4 T f := by
  simp only [circleFixedProjectionH4,Submodule.coe_smul_of_tower,inner_smul_right,mul_smul]

theorem circle_short_reduced_sum_left {ι : Type*} (I : Finset ι)
    (h h₁ h₂ : C(AddCircle T, ℂ)) (k : Fin 5)
    (f : ι → circleH4Domain T) (g : circleH4Domain T) :
    circleReducedShiftedCoefficient T (circleShortSymmetricCoefficient T h h₁ h₂)
      k (∑ i∈I,f i) g=
      ∑ i∈I,circleReducedShiftedCoefficient T (circleShortSymmetricCoefficient T h h₁ h₂)
        k (f i) g := by
  fin_cases k <;>
    simp only [circleReducedShiftedCoefficient,Matrix.cons_val_zero',Matrix.cons_val_succ',
      circle_fixed_projection_sum,← Finset.sum_sub_distrib,
      circle_short_symmetric_sum_left,Submodule.coe_sum,sum_inner,
      Finset.sum_add_distrib,Finset.mul_sum]

theorem circle_short_reduced_sum_right {ι : Type*} (I : Finset ι)
    (h h₁ h₂ : C(AddCircle T, ℂ)) (k : Fin 5)
    (f : circleH4Domain T) (g : ι → circleH4Domain T) :
    circleReducedShiftedCoefficient T (circleShortSymmetricCoefficient T h h₁ h₂)
      k f (∑ i∈I,g i)=
      ∑ i∈I,circleReducedShiftedCoefficient T (circleShortSymmetricCoefficient T h h₁ h₂)
        k f (g i) := by
  fin_cases k <;>
    simp only [circleReducedShiftedCoefficient,Matrix.cons_val_zero',Matrix.cons_val_succ',
      circle_fixed_projection_sum,← Finset.sum_sub_distrib,
      circle_short_symmetric_sum_right,Submodule.coe_sum,inner_sum,
      Finset.sum_add_distrib,Finset.mul_sum]

theorem circle_short_reduced_smul_left (h h₁ h₂ : C(AddCircle T, ℂ))
    (k : Fin 5) (c : ℂ) (f g : circleH4Domain T) :
    circleReducedShiftedCoefficient T (circleShortSymmetricCoefficient T h h₁ h₂)
      k (c • f) g=conj c*
      circleReducedShiftedCoefficient T (circleShortSymmetricCoefficient T h h₁ h₂) k f g := by
  fin_cases k <;>
    simp only [circleReducedShiftedCoefficient,Matrix.cons_val_zero',Matrix.cons_val_succ',
      circle_fixed_projection_smul,← smul_sub,circle_short_symmetric_smul_left,
      Submodule.coe_smul_of_tower,inner_smul_left] <;> ring

theorem circle_short_reduced_smul_right (h h₁ h₂ : C(AddCircle T, ℂ))
    (k : Fin 5) (c : ℂ) (f g : circleH4Domain T) :
    circleReducedShiftedCoefficient T (circleShortSymmetricCoefficient T h h₁ h₂)
      k f (c • g)=c*
      circleReducedShiftedCoefficient T (circleShortSymmetricCoefficient T h h₁ h₂) k f g := by
  fin_cases k <;>
    simp only [circleReducedShiftedCoefficient,Matrix.cons_val_zero',Matrix.cons_val_succ',
      circle_fixed_projection_smul,← smul_sub,circle_short_symmetric_smul_right,
      Submodule.coe_smul_of_tower,inner_smul_right] <;> ring

theorem circle_short_bernstein_sum_left {ι : Type*} (I : Finset ι)
    (h h₁ h₂ : C(AddCircle T, ℂ)) (j : Fin 5)
    (f : ι → circleH4Domain T) (g : circleH4Domain T) :
    circleShortBernsteinPairing T h h₁ h₂ j (∑ i∈I,f i) g=
      ∑ i∈I,circleShortBernsteinPairing T h h₁ h₂ j (f i) g := by
  simp only [circleShortBernsteinPairing,circleShiftedBernsteinPairing,
    circle_short_reduced_sum_left,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem circle_short_bernstein_sum_right {ι : Type*} (I : Finset ι)
    (h h₁ h₂ : C(AddCircle T, ℂ)) (j : Fin 5)
    (f : circleH4Domain T) (g : ι → circleH4Domain T) :
    circleShortBernsteinPairing T h h₁ h₂ j f (∑ i∈I,g i)=
      ∑ i∈I,circleShortBernsteinPairing T h h₁ h₂ j f (g i) := by
  simp only [circleShortBernsteinPairing,circleShiftedBernsteinPairing,
    circle_short_reduced_sum_right,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem circle_short_bernstein_smul_left (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (c : ℂ) (f g : circleH4Domain T) :
    circleShortBernsteinPairing T h h₁ h₂ j (c • f) g=
      conj c*circleShortBernsteinPairing T h h₁ h₂ j f g := by
  simp only [circleShortBernsteinPairing,circleShiftedBernsteinPairing,
    circle_short_reduced_smul_left,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem circle_short_bernstein_smul_right (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (c : ℂ) (f g : circleH4Domain T) :
    circleShortBernsteinPairing T h h₁ h₂ j f (c • g)=
      c*circleShortBernsteinPairing T h h₁ h₂ j f g := by
  simp only [circleShortBernsteinPairing,circleShiftedBernsteinPairing,
    circle_short_reduced_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem circle_short_bernstein_polynomial (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x,conj (h x)=h x) (h₁real : ∀ x,conj (h₁ x)=h₁ x)
    (h₂real : ∀ x,conj (h₂ x)=h₂ x)
    (hs : ∀ n : ℤ,fourierCoeff h (-n)=fourierCoeff h n)
    (hc : ∀ j : ℕ,fourierCoeff h (2*(j:ℤ))=(shortActualCoefficient j:ℂ))
    (hr : (2*Real.pi/T)^2=lemniscateFrequencySquared)
    (j : Fin 5) (I J : Finset ℤ) (a b : ℤ → ℂ) :
    circleShortBernsteinPairing T h h₁ h₂ j
      (∑ n∈I,a n • circleFourierH4 T (2*n))
      (∑ m∈J,b m • circleFourierH4 T (2*m))=
      ∑ n∈I,∑ m∈J,conj (a n)*
        (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j n m:ℂ)*b m := by
  simp only [circle_short_bernstein_sum_left,circle_short_bernstein_sum_right,
    circle_short_bernstein_smul_left,circle_short_bernstein_smul_right,
    circle_short_bernstein_kernel T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  ring

end Lemniscate
