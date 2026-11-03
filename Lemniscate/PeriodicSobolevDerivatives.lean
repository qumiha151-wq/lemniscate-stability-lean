import Lemniscate.PeriodicSobolevEmbedding
import Lemniscate.PeriodicWeakRegularity
import Mathlib.Algebra.BigOperators.Fin

/-! Order-lowering and differentiation on the complete periodic Sobolev scale.
Both maps are contractions for the derivative square-sum norm. At order two,
the resulting continuous representatives satisfy the actual circle derivative
identity, rather than merely an L2 weak-derivative relation. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

private def circleSobolevInclusionLinear (m : ℕ) :
    CircleSobolevSpace T (m+1) →ₗ[ℂ] CircleSobolevSpace T m where
  toFun f :=
    ⟨WithLp.toLp 2 (fun j : Fin (m+1) => f.1 j.castSucc),by
      apply (circle_sobolev_jet_mem_iff T m _).mpr
      intro j
      simpa only [PiLp.toLp_apply,Fin.castSucc_succ] using
        circle_sobolev_weak_deriv T (m+1) f j.castSucc⟩
  map_add' f g := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    rfl

private def circleSobolevDerivativeLinear (m : ℕ) :
    CircleSobolevSpace T (m+1) →ₗ[ℂ] CircleSobolevSpace T m where
  toFun f :=
    ⟨WithLp.toLp 2 (fun j : Fin (m+1) => f.1 j.succ),by
      apply (circle_sobolev_jet_mem_iff T m _).mpr
      intro j
      simpa only [PiLp.toLp_apply,Fin.castSucc_succ] using
        circle_sobolev_weak_deriv T (m+1) f j.succ⟩
  map_add' f g := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    rfl

private theorem circle_sobolev_inclusion_linear_norm_le (m : ℕ)
    (f : CircleSobolevSpace T (m+1)) :
    ‖circleSobolevInclusionLinear T m f‖ ≤ ‖f‖ := by
  have hsq : ‖circleSobolevInclusionLinear T m f‖^2 ≤ ‖f‖^2 := by
    rw [circle_sobolev_norm_sq,circle_sobolev_norm_sq]
    change (∑ j : Fin (m+1), ‖f.1 j.castSucc‖^2) ≤
      ∑ j : Fin ((m+1)+1), ‖f.1 j‖^2
    rw [Fin.sum_univ_castSucc (fun j : Fin ((m+1)+1) => ‖f.1 j‖^2)]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem circle_sobolev_derivative_linear_norm_le (m : ℕ)
    (f : CircleSobolevSpace T (m+1)) :
    ‖circleSobolevDerivativeLinear T m f‖ ≤ ‖f‖ := by
  have hsq : ‖circleSobolevDerivativeLinear T m f‖^2 ≤ ‖f‖^2 := by
    rw [circle_sobolev_norm_sq,circle_sobolev_norm_sq]
    change (∑ j : Fin (m+1), ‖f.1 j.succ‖^2) ≤
      ∑ j : Fin ((m+1)+1), ‖f.1 j‖^2
    rw [Fin.sum_univ_succ (fun j : Fin ((m+1)+1) => ‖f.1 j‖^2)]
    exact le_add_of_nonneg_left (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The natural inclusion H^(m+1) into H^m, keeping the zeroth coordinate. -/
def circleSobolevInclusion (m : ℕ) :
    CircleSobolevSpace T (m+1) →L[ℂ] CircleSobolevSpace T m :=
  (circleSobolevInclusionLinear T m).mkContinuous 1
    (fun f => by simpa only [one_mul] using circle_sobolev_inclusion_linear_norm_le T m f)

/-- The weak derivative, as a bounded map H^(m+1) into H^m. -/
def circleSobolevDerivative (m : ℕ) :
    CircleSobolevSpace T (m+1) →L[ℂ] CircleSobolevSpace T m :=
  (circleSobolevDerivativeLinear T m).mkContinuous 1
    (fun f => by simpa only [one_mul] using circle_sobolev_derivative_linear_norm_le T m f)

@[simp] theorem circle_sobolev_inclusion_coordinate (m : ℕ) (j : Fin (m+1))
    (f : CircleSobolevSpace T (m+1)) :
    circleSobolevCoordinate T m j (circleSobolevInclusion T m f) =
      circleSobolevCoordinate T (m+1) j.castSucc f := rfl

@[simp] theorem circle_sobolev_derivative_coordinate (m : ℕ) (j : Fin (m+1))
    (f : CircleSobolevSpace T (m+1)) :
    circleSobolevCoordinate T m j (circleSobolevDerivative T m f) =
      circleSobolevCoordinate T (m+1) j.succ f := rfl

theorem circle_sobolev_inclusion_norm_le (m : ℕ) : ‖circleSobolevInclusion T m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ) ≤ 1)
  intro f
  change ‖circleSobolevInclusionLinear T m f‖ ≤ 1*‖f‖
  simpa only [one_mul] using circle_sobolev_inclusion_linear_norm_le T m f

theorem circle_sobolev_derivative_norm_le (m : ℕ) : ‖circleSobolevDerivative T m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ) ≤ 1)
  intro f
  change ‖circleSobolevDerivativeLinear T m f‖ ≤ 1*‖f‖
  simpa only [one_mul] using circle_sobolev_derivative_linear_norm_le T m f

theorem circle_sobolev_h2_classical_deriv (f : CircleSobolevSpace T 2) :
    HasCircleDeriv T
      (circleSobolevH1Embedding T (circleSobolevInclusion T 1 f))
      (circleSobolevH1Embedding T (circleSobolevDerivative T 1 f)) := by
  apply circle_classical_deriv_of_continuous_weak T
  rw [circle_sobolev_h1_embedding_l2,circle_sobolev_h1_embedding_l2,
    circle_sobolev_inclusion_coordinate,circle_sobolev_derivative_coordinate]
  exact circle_sobolev_weak_deriv T 2 f 0

end Lemniscate
