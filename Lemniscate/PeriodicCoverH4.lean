import Lemniscate.PeriodicCoverFourier
import Lemniscate.PeriodicBlochOddLimit

/-! Fourier sampling preserves the weak H4 domain. Long-period derivatives
become shifted derivatives on the short period, with Bloch parameter j/M. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

theorem circle_cover_frequency (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T) (j n : ℤ) :
    circleFrequencyFactor S (circleCoverIndex M j n) =
      circleFrequencyFactor T n+(((j:ℝ)/(M:ℝ):ℝ):ℂ)*circleFrequencyFactor T 1 := by
  have hMC : (M:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hTC : (T:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Fact.out : 0 < T))
  simp only [circleFrequencyFactor,circleCoverIndex,hS]
  push_cast
  field_simp
  <;> ring

theorem circle_cover_component_mem_h4 (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (j : ℤ) (f : circleH4Domain S) :
    InCircleH4 T (circleCoverComponent T S M hM j (f:CircleL2 S)) := by
  let C := circleCoverComponent T S M hM j
  let z : ℂ := (((j:ℝ)/(M:ℝ):ℝ):ℂ)*circleFrequencyFactor T 1
  let g : CircleL2 T := C (circleH4Derivative S 3 f)-
    (4*z) • C (circleH4Derivative S 2 f)+
    (6*z^2) • C (circleH4Derivative S 1 f)-
    (4*z^3) • C (circleH4Derivative S 0 f)+z^4 • C (f:CircleL2 S)
  apply circle_h4_of_fourth_fourier T _ g
  intro n
  simp only [g,C,circle_fourierCoeff_add,circle_fourierCoeff_sub,circle_fourierCoeff_smul,
    circle_cover_component_fourier,circle_h4_derivative_fourier]
  rw [circle_cover_frequency T S M hM hS j n]
  dsimp only [z]
  norm_num only [show ((2:Fin 4):ℕ) = 2 from rfl,show ((3:Fin 4):ℕ) = 3 from rfl,
    Fin.val_zero,Fin.val_one]
  ring

noncomputable def circleCoverComponentH4 (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (j : ℤ) (f : circleH4Domain S) : circleH4Domain T :=
  ⟨circleCoverComponent T S M hM j (f:CircleL2 S),circle_cover_component_mem_h4 T S M hM hS j f⟩

theorem circle_cover_component_h4_coe (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (j : ℤ) (f : circleH4Domain S) :
    (circleCoverComponentH4 T S M hM hS j f:CircleL2 T) =
      circleCoverComponent T S M hM j (f:CircleL2 S) := rfl

private theorem shifted_first_fourier (z : ℂ) (f : circleH4Domain T) (n : ℤ) :
    fourierCoeff (circleShiftedFirst T z f) n =
      (circleFrequencyFactor T n+z)*fourierCoeff (f:CircleL2 T) n := by
  simp only [circleShiftedFirst,LinearMap.add_apply,LinearMap.smul_apply,Submodule.subtype_apply,
    circle_fourierCoeff_add,circle_fourierCoeff_smul,circle_h4_derivative_fourier]
  norm_num only [Fin.val_zero]
  ring

private theorem shifted_second_fourier (z : ℂ) (f : circleH4Domain T) (n : ℤ) :
    fourierCoeff (circleShiftedSecond T z f) n =
      (circleFrequencyFactor T n+z)^2*fourierCoeff (f:CircleL2 T) n := by
  simp only [circleShiftedSecond,LinearMap.add_apply,LinearMap.smul_apply,Submodule.subtype_apply,
    circle_fourierCoeff_add,circle_fourierCoeff_smul,circle_h4_derivative_fourier]
  norm_num only [Fin.val_zero,Fin.val_one]
  ring

private theorem shifted_fourth_fourier (z : ℂ) (f : circleH4Domain T) (n : ℤ) :
    fourierCoeff (circleShiftedFourth T z f) n =
      (circleFrequencyFactor T n+z)^4*fourierCoeff (f:CircleL2 T) n := by
  simp only [circleShiftedFourth,LinearMap.add_apply,LinearMap.smul_apply,Submodule.subtype_apply,
    circle_fourierCoeff_add,circle_fourierCoeff_smul,circle_h4_derivative_fourier]
  norm_num only [show ((2:Fin 4):ℕ) = 2 from rfl,show ((3:Fin 4):ℕ) = 3 from rfl,
    Fin.val_zero,Fin.val_one]
  ring

theorem circle_cover_shifted_first (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (j : ℤ) (f : circleH4Domain S) :
    circleShiftedFirst T ((((j:ℝ)/(M:ℝ):ℝ):ℂ)*circleFrequencyFactor T 1)
      (circleCoverComponentH4 T S M hM hS j f) =
        circleCoverComponent T S M hM j (circleH4Derivative S 0 f) := by
  apply circle_fourier_ext T
  intro n
  rw [shifted_first_fourier,circle_cover_component_h4_coe,circle_cover_component_fourier,
    circle_cover_component_fourier,circle_h4_derivative_fourier,circle_cover_frequency T S M hM hS j n]
  norm_num <;> ring

theorem circle_cover_shifted_second (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (j : ℤ) (f : circleH4Domain S) :
    circleShiftedSecond T ((((j:ℝ)/(M:ℝ):ℝ):ℂ)*circleFrequencyFactor T 1)
      (circleCoverComponentH4 T S M hM hS j f) =
        circleCoverComponent T S M hM j (circleH4Derivative S 1 f) := by
  apply circle_fourier_ext T
  intro n
  rw [shifted_second_fourier,circle_cover_component_h4_coe,circle_cover_component_fourier,
    circle_cover_component_fourier,circle_h4_derivative_fourier,circle_cover_frequency T S M hM hS j n]
  norm_num <;> ring

theorem circle_cover_shifted_fourth (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (j : ℤ) (f : circleH4Domain S) :
    circleShiftedFourth T ((((j:ℝ)/(M:ℝ):ℝ):ℂ)*circleFrequencyFactor T 1)
      (circleCoverComponentH4 T S M hM hS j f) =
        circleCoverComponent T S M hM j (circleH4Derivative S 3 f) := by
  apply circle_fourier_ext T
  intro n
  rw [shifted_fourth_fourier,circle_cover_component_h4_coe,circle_cover_component_fourier,
    circle_cover_component_fourier,circle_h4_derivative_fourier,circle_cover_frequency T S M hM hS j n]
  norm_num <;> ring

end Lemniscate
