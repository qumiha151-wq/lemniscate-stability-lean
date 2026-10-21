import Lemniscate.PeriodicSineCoefficients
import Lemniscate.SineHilbert

/-! Separate the first sine mode from its infinite tail in the actual periodic
L2 space. Index j of the tail has frequency 2(j+2). -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_tail_orthonormal :
    Orthonormal ℂ (fun j : ℕ => circleEvenSineMode T (j+1)) :=
  (circle_even_sine_orthonormal T).comp (fun j : ℕ => j+1) (by
    intro a b h
    change a+1 = b+1 at h
    omega)

noncomputable def circleSineTailSynthesis : SineTailSpace →ₗᵢ[ℂ] CircleL2 T :=
  (circle_sine_tail_orthonormal T).orthogonalFamily.linearIsometry

theorem circle_sine_tail_hasSum (v : SineTailSpace) :
    HasSum (fun j : ℕ => v j • circleEvenSineMode T (j+1))
      (circleSineTailSynthesis T v) := by
  simpa only [circleSineTailSynthesis, LinearIsometry.toSpanSingleton_apply] using
    (circle_sine_tail_orthonormal T).orthogonalFamily.hasSum_linearIsometry v

theorem circle_sine_first_inner_tail (v : SineTailSpace) :
    inner ℂ (circleEvenSineMode T 0) (circleSineTailSynthesis T v) = 0 := by
  have hj (j : ℕ) : inner ℂ (circleEvenSineMode T 0) (circleEvenSineMode T (j+1)) = 0 := by
    rw [orthonormal_iff_ite.mp (circle_even_sine_orthonormal T)]
    simp
  have h := (circle_sine_tail_hasSum T v).mapL (innerSL ℂ (circleEvenSineMode T 0))
  have hz : HasSum (fun _ : ℕ => (0:ℂ))
      (inner ℂ (circleEvenSineMode T 0) (circleSineTailSynthesis T v)) := by
    simpa only [innerSL_apply_apply, inner_smul_right, hj, mul_zero] using h
  exact hz.unique hasSum_zero

noncomputable def circleSineBlockFunction (u : ℂ) (v : SineTailSpace) : CircleL2 T :=
  u • circleEvenSineMode T 0 + circleSineTailSynthesis T v

theorem circle_sine_block_inner (u w : ℂ) (v z : SineTailSpace) :
    inner ℂ (circleSineBlockFunction T u v) (circleSineBlockFunction T w z) =
      conj u*w + inner ℂ v z := by
  have hfirst : inner ℂ (circleEvenSineMode T 0) (circleEvenSineMode T 0) = 1 := by
    rw [orthonormal_iff_ite.mp (circle_even_sine_orthonormal T)]
    simp
  have hrev : inner ℂ (circleSineTailSynthesis T v) (circleEvenSineMode T 0) = 0 :=
    inner_eq_zero_symm.mpr (circle_sine_first_inner_tail T v)
  simp only [circleSineBlockFunction, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, hfirst, circle_sine_first_inner_tail,
    hrev, (circleSineTailSynthesis T).inner_map_map, mul_one, mul_zero, zero_add, add_zero]
  ring

theorem circle_sine_block_norm_sq (u : ℂ) (v : SineTailSpace) :
    ‖circleSineBlockFunction T u v‖^2 = ‖u‖^2+‖v‖^2 := by
  have h := congrArg Complex.re (circle_sine_block_inner T u u v v)
  have hu : conj u*u = inner ℂ u u := by simp only [RCLike.inner_apply']
  rw [hu] at h
  simp only [Complex.add_re] at h
  calc
    _ = (inner ℂ (circleSineBlockFunction T u v) (circleSineBlockFunction T u v)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (inner ℂ u u).re + (inner ℂ v v).re := h
    _ = _ := congrArg₂ (fun a b : ℝ => a+b)
      (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm

end Lemniscate
