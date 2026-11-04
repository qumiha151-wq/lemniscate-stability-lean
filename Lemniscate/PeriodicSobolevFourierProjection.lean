import Lemniscate.PeriodicSobolevSpace
import Lemniscate.PeriodicBoundedMultiplier

/-! Finite integer Fourier projections on the complete periodic Sobolev scale.
The same Hilbert-basis projection acts on every weak derivative coordinate.
Its L2 contraction is the existing bounded-multiplier estimate for the
indicator symbol. Strong Sobolev convergence uses Hilbert-basis partial sums
and the topology of the finite L2 jet product.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped BigOperators Topology

variable (T : ℝ) [Fact (0 < T)]

/-- The finite orthogonal Fourier projection with integer frequencies in I. -/
def circleFourierProjection (I : Finset ℤ) : CircleL2 T →L[ℂ] CircleL2 T :=
  circleBoundedMultiplier T (fun n => if n ∈ I then (1:ℂ) else 0) 1
    (by norm_num) (by intro n; split_ifs <;> simp)

theorem circle_fourier_projection_fourier (I : Finset ℤ) (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleFourierProjection T I f) n =
      if n ∈ I then fourierCoeff f n else 0 := by
  simp only [circleFourierProjection,circle_bounded_multiplier_fourier]
  split_ifs <;> simp

theorem circle_fourier_projection_apply (I : Finset ℤ) (f : CircleL2 T) :
    circleFourierProjection T I f =
      ∑ n ∈ I, fourierCoeff f n • fourierBasis (T := T) n := by
  have hortho (n m : ℤ) :
      inner ℂ (fourierBasis (T := T) n) (fourierBasis (T := T) m) =
        if n = m then 1 else 0 :=
    orthonormal_iff_ite.mp (fourierBasis (T := T)).orthonormal n m
  apply circle_fourier_ext T
  intro n
  rw [circle_fourier_projection_fourier]
  symm
  rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  simp only [inner_sum,inner_smul_right,hortho]
  simp [eq_comm]

theorem circle_fourier_projection_norm_le (I : Finset ℤ) :
    ‖circleFourierProjection T I‖ ≤ 1 :=
  circle_bounded_multiplier_norm_le T _ 1 (by norm_num) _

private theorem circle_fourier_projection_apply_norm_le (I : Finset ℤ) (f : CircleL2 T) :
    ‖circleFourierProjection T I f‖ ≤ ‖f‖ := by
  simpa only [one_mul] using
    (circleFourierProjection T I).le_of_opNorm_le (circle_fourier_projection_norm_le T I) f

theorem circle_fourier_projection_weak_deriv (I : Finset ℤ) (f g : CircleL2 T)
    (hfg : HasWeakCircleDeriv T f g) :
    HasWeakCircleDeriv T (circleFourierProjection T I f) (circleFourierProjection T I g) := by
  apply weak_circle_deriv_of_fourier
  intro n
  rw [circle_fourier_projection_fourier,circle_fourier_projection_fourier]
  by_cases hn : n ∈ I
  · simp only [if_pos hn]
    exact fourier_of_weak_circle_deriv T f g hfg n
  · simp only [if_neg hn,mul_zero]

theorem circle_fourier_projection_tendsto (f : CircleL2 T) :
    Tendsto (fun I : Finset ℤ => circleFourierProjection T I f) atTop (𝓝 f) := by
  simpa only [HasSum,SummationFilter.unconditional,
    circle_fourier_projection_apply,fourierBasis_repr] using
    (fourierBasis (T := T)).hasSum_repr f

private def circleSobolevFourierProjectionLinear (m : ℕ) (I : Finset ℤ) :
    CircleSobolevSpace T m →ₗ[ℂ] CircleSobolevSpace T m where
  toFun f :=
    ⟨WithLp.toLp 2 (fun j : Fin (m+1) =>
      circleFourierProjection T I (circleSobolevCoordinate T m j f)),by
      apply (circle_sobolev_jet_mem_iff T m _).mpr
      intro j
      change HasWeakCircleDeriv T
        (circleFourierProjection T I (circleSobolevCoordinate T m j.castSucc f))
        (circleFourierProjection T I (circleSobolevCoordinate T m j.succ f))
      exact circle_fourier_projection_weak_deriv T I _ _
        (circle_sobolev_weak_deriv T m f j)⟩
  map_add' f g := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    change circleFourierProjection T I (circleSobolevCoordinate T m j (f+g)) =
      circleFourierProjection T I (circleSobolevCoordinate T m j f)+
        circleFourierProjection T I (circleSobolevCoordinate T m j g)
    simp only [map_add]
  map_smul' c f := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    change circleFourierProjection T I (circleSobolevCoordinate T m j (c • f)) =
      c • circleFourierProjection T I (circleSobolevCoordinate T m j f)
    simp only [map_smul,RingHom.id_apply]

private theorem circle_sobolev_fourier_projection_linear_norm_le
    (m : ℕ) (I : Finset ℤ) (f : CircleSobolevSpace T m) :
    ‖circleSobolevFourierProjectionLinear T m I f‖ ≤ ‖f‖ := by
  have hsq : ‖circleSobolevFourierProjectionLinear T m I f‖^2 ≤ ‖f‖^2 := by
    rw [circle_sobolev_norm_sq,circle_sobolev_norm_sq]
    apply Finset.sum_le_sum
    intro j _
    change ‖circleFourierProjection T I (circleSobolevCoordinate T m j f)‖^2 ≤
      ‖circleSobolevCoordinate T m j f‖^2
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (circle_fourier_projection_apply_norm_le T I _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Fourier truncation for the complete derivative square-sum Hm norm. -/
def circleSobolevFourierProjection (m : ℕ) (I : Finset ℤ) :
    CircleSobolevSpace T m →L[ℂ] CircleSobolevSpace T m :=
  (circleSobolevFourierProjectionLinear T m I).mkContinuous 1
    (fun f => by simpa only [one_mul] using
      circle_sobolev_fourier_projection_linear_norm_le T m I f)

theorem circle_sobolev_fourier_projection_coordinate
    (m : ℕ) (I : Finset ℤ) (f : CircleSobolevSpace T m) (j : Fin (m+1)) :
    circleSobolevCoordinate T m j (circleSobolevFourierProjection T m I f) =
      ∑ n ∈ I, fourierCoeff (circleSobolevCoordinate T m j f) n •
        fourierBasis (T := T) n := by
  change circleFourierProjection T I (circleSobolevCoordinate T m j f) = _
  exact circle_fourier_projection_apply T I _

theorem circle_sobolev_fourier_projection_norm_le (m : ℕ) (I : Finset ℤ) :
    ‖circleSobolevFourierProjection T m I‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ) ≤ 1)
  intro f
  change ‖circleSobolevFourierProjectionLinear T m I f‖ ≤ 1*‖f‖
  simpa only [one_mul] using circle_sobolev_fourier_projection_linear_norm_le T m I f

/-- The finite Fourier projections converge in the actual Hm norm. -/
theorem circle_sobolev_fourier_projection_tendsto (m : ℕ) (f : CircleSobolevSpace T m) :
    Tendsto (fun I : Finset ℤ => circleSobolevFourierProjection T m I f) atTop (𝓝 f) := by
  apply tendsto_subtype_rng.mpr
  have hpi : Tendsto
      (fun I : Finset ℤ => fun j : Fin (m+1) =>
        circleFourierProjection T I (circleSobolevCoordinate T m j f)) atTop
      (𝓝 (fun j : Fin (m+1) => circleSobolevCoordinate T m j f)) :=
    tendsto_pi_nhds.mpr fun j => circle_fourier_projection_tendsto T _
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (m+1) => CircleL2 T)).continuousAt.tendsto.comp hpi

end Lemniscate
