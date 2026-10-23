import Lemniscate.PeriodicReflectionOperator
import Lemniscate.PeriodicCosineSector
import Lemniscate.PeriodicSineSector
import Mathlib.Tactic.Module

/-! Orthogonal reflection splitting on L2 and on the actual H4 domain.
For functions supported on even Fourier frequencies, its two parts lie in
the complete cosine and sine sectors already estimated. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleCosinePart (f : CircleL2 T) : CircleL2 T :=
  (1/2:ℂ) • (f+circleReflect T f)

noncomputable def circleSinePart (f : CircleL2 T) : CircleL2 T :=
  (1/2:ℂ) • (f-circleReflect T f)

theorem circle_fourierCoeff_sub (f g : CircleL2 T) (n : ℤ) :
    fourierCoeff (f-g) n = fourierCoeff f n-fourierCoeff g n := by
  simp only [← fourierBasis_repr, HilbertBasis.repr_apply_apply, inner_sub_right]

theorem circle_cosine_part_fourier (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleCosinePart T f) n =
      (1/2:ℂ)*(fourierCoeff f n+fourierCoeff f (-n)) := by
  simp only [circleCosinePart, circle_fourierCoeff_smul, circle_fourierCoeff_add,
    circle_reflect_fourier]

theorem circle_sine_part_fourier (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleSinePart T f) n =
      (1/2:ℂ)*(fourierCoeff f n-fourierCoeff f (-n)) := by
  simp only [circleSinePart, circle_fourierCoeff_smul, circle_fourierCoeff_sub,
    circle_reflect_fourier]

theorem circle_reflect_cosine_part (f : CircleL2 T) :
    circleReflect T (circleCosinePart T f) = circleCosinePart T f := by
  simp only [circleCosinePart, circle_reflect_smul, circle_reflect_add, circle_reflect_involutive]
  rw [add_comm]

theorem circle_reflect_sine_part (f : CircleL2 T) :
    circleReflect T (circleSinePart T f) = -circleSinePart T f := by
  simp only [circleSinePart, circle_reflect_smul, circle_reflect_sub, circle_reflect_involutive]
  module

theorem circle_reflection_parts_sum (f : CircleL2 T) :
    circleCosinePart T f + circleSinePart T f = f := by
  simp only [circleCosinePart, circleSinePart]
  module

theorem circle_reflection_orthogonal (f g : CircleL2 T)
    (hf : circleReflect T f = f) (hg : circleReflect T g = -g) : inner ℂ f g = 0 := by
  have h := circle_reflect_inner T f g
  rw [hf, hg, inner_neg_right] at h
  linear_combination (-1/2:ℂ)*h

theorem circle_reflection_parts_orthogonal (f : CircleL2 T) :
    inner ℂ (circleCosinePart T f) (circleSinePart T f) = 0 :=
  circle_reflection_orthogonal T _ _ (circle_reflect_cosine_part T f) (circle_reflect_sine_part T f)

theorem circle_reflection_parts_norm_sq (f : CircleL2 T) :
    ‖f‖^2 = ‖circleCosinePart T f‖^2+‖circleSinePart T f‖^2 := by
  have h := circle_reflection_parts_orthogonal T f
  have h' : inner ℂ (circleSinePart T f) (circleCosinePart T f) = 0 := by
    rw [← inner_conj_symm, h, map_zero]
  have he : inner ℂ f f = inner ℂ (circleCosinePart T f) (circleCosinePart T f)+
      inner ℂ (circleSinePart T f) (circleSinePart T f) := by
    conv_lhs => rw [← circle_reflection_parts_sum T f]
    simp only [inner_add_left, inner_add_right, h, h', zero_add, add_zero]
  calc
    ‖f‖^2 = (inner ℂ f f).re := norm_sq_eq_re_inner (𝕜 := ℂ) f
    _ = (inner ℂ (circleCosinePart T f) (circleCosinePart T f)).re +
        (inner ℂ (circleSinePart T f) (circleSinePart T f)).re := by rw [he, Complex.add_re]
    _ = ‖circleCosinePart T f‖^2+‖circleSinePart T f‖^2 :=
      congrArg₂ (fun a b : ℝ => a+b)
        (norm_sq_eq_re_inner (𝕜 := ℂ) (circleCosinePart T f)).symm
        (norm_sq_eq_re_inner (𝕜 := ℂ) (circleSinePart T f)).symm

theorem circle_cosine_part_mem_sector (f : CircleL2 T)
    (ho : ∀ n : ℤ, fourierCoeff f (2*n+1) = 0) :
    InCircleEvenCosineSector T (circleCosinePart T f) := by
  constructor
  · intro n
    simp only [circle_cosine_part_fourier, neg_neg]
    ring
  · intro n
    rw [circle_cosine_part_fourier, ho, show -(2*n+1) = 2*(-n-1)+1 by omega, ho]
    ring

theorem circle_sine_part_mem_sector (f : CircleL2 T)
    (ho : ∀ n : ℤ, fourierCoeff f (2*n+1) = 0) :
    InCircleEvenSineSector T (circleSinePart T f) := by
  constructor
  · intro n
    simp only [circle_sine_part_fourier, neg_neg]
    ring
  · intro n
    rw [circle_sine_part_fourier, ho, show -(2*n+1) = 2*(-n-1)+1 by omega, ho]
    ring

noncomputable def circleCosinePartH4 (f : circleH4Domain T) : circleH4Domain T :=
  (1/2:ℂ) • (f+circleReflectH4 T f)

noncomputable def circleSinePartH4 (f : circleH4Domain T) : circleH4Domain T :=
  (1/2:ℂ) • (f-circleReflectH4 T f)

theorem circle_cosine_part_h4_coe (f : circleH4Domain T) :
    (circleCosinePartH4 T f : CircleL2 T) = circleCosinePart T (f : CircleL2 T) := rfl

theorem circle_sine_part_h4_coe (f : circleH4Domain T) :
    (circleSinePartH4 T f : CircleL2 T) = circleSinePart T (f : CircleL2 T) := rfl

theorem circle_reflection_h4_parts_sum (f : circleH4Domain T) :
    circleCosinePartH4 T f + circleSinePartH4 T f = f := by
  apply Subtype.ext
  exact circle_reflection_parts_sum T (f : CircleL2 T)

theorem circle_sine_constraint_reflect :
    circleReflect T (circleSineConstraintVector T) = -circleSineConstraintVector T := by
  apply circle_fourier_ext T
  intro n
  rw [circle_reflect_fourier, circle_sine_constraint_coeff_neg]
  simpa only [neg_one_smul, neg_one_mul] using
    (circle_fourierCoeff_smul T (-1) (circleSineConstraintVector T) n).symm

theorem circle_sine_part_constraint (f : CircleL2 T)
    (horth : inner ℂ (circleSineConstraintVector T) f = 0) :
    inner ℂ (circleSineConstraintVector T) (circleSinePart T f) = 0 := by
  have hz := circle_reflection_orthogonal T (circleCosinePart T f)
    (circleSineConstraintVector T) (circle_reflect_cosine_part T f) (circle_sine_constraint_reflect T)
  have hz' : inner ℂ (circleSineConstraintVector T) (circleCosinePart T f) = 0 := by
    rw [← inner_conj_symm, hz, map_zero]
  rw [← circle_reflection_parts_sum T f, inner_add_right, hz', zero_add] at horth
  exact horth

end Lemniscate
