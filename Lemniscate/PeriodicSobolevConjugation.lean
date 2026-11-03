import Lemniscate.PeriodicSobolevDerivatives
import Lemniscate.PeriodicConjugation
import Mathlib.Topology.ContinuousMap.Star

/-! Complex conjugation on the complete periodic Sobolev scale.
It is a real linear isometric involution and agrees with pointwise
conjugation of the continuous H1 representative. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

private theorem circle_l2_conjugate_norm (f : CircleL2 T) :
    ‖circleConjugate T f‖ = ‖f‖ := by
  have hs : ‖circleConjugate T f‖^2 = ‖f‖^2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ),
      circle_conjugate_inner]
    exact Complex.conj_re _
  nlinarith only [hs,norm_nonneg f,norm_nonneg (circleConjugate T f)]

private def circleSobolevConjugateLinear (m : ℕ) :
    CircleSobolevSpace T m →ₗ[ℝ] CircleSobolevSpace T m where
  toFun f :=
    ⟨WithLp.toLp 2 (fun j : Fin (m+1) => circleConjugate T (f.1 j)),by
      apply (circle_sobolev_jet_mem_iff T m _).mpr
      intro j
      simpa only [PiLp.toLp_apply] using
        circle_conjugate_weak_deriv T _ _ (circle_sobolev_weak_deriv T m f j)⟩
  map_add' f g := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    change circleConjugate T (f.1 j+g.1 j) =
      circleConjugate T (f.1 j)+circleConjugate T (g.1 j)
    exact circle_conjugate_add T _ _
  map_smul' c f := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    change circleConjugate T (c • f.1 j) = c • circleConjugate T (f.1 j)
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),circle_conjugate_smul,
      RCLike.conj_ofReal]

private theorem circle_sobolev_conjugate_linear_involutive (m : ℕ)
    (f : CircleSobolevSpace T m) :
    circleSobolevConjugateLinear T m (circleSobolevConjugateLinear T m f) = f := by
  apply circle_sobolev_value_injective T m
  change circleConjugate T (circleConjugate T (f.1 0)) = f.1 0
  exact circle_conjugate_involutive T _

private theorem circle_sobolev_conjugate_linear_norm (m : ℕ)
    (f : CircleSobolevSpace T m) : ‖circleSobolevConjugateLinear T m f‖ = ‖f‖ := by
  have hs : ‖circleSobolevConjugateLinear T m f‖^2 = ‖f‖^2 := by
    rw [circle_sobolev_norm_sq,circle_sobolev_norm_sq]
    apply Finset.sum_congr rfl
    intro j _
    change ‖circleConjugate T (f.1 j)‖^2 = ‖f.1 j‖^2
    rw [circle_l2_conjugate_norm]
  nlinarith only [hs,norm_nonneg f,norm_nonneg (circleSobolevConjugateLinear T m f)]

/-- Coordinatewise complex conjugation, viewed as a real linear isometric equivalence. -/
def circleSobolevConjugation (m : ℕ) :
    CircleSobolevSpace T m ≃ₗᵢ[ℝ] CircleSobolevSpace T m where
  toFun := circleSobolevConjugateLinear T m
  invFun := circleSobolevConjugateLinear T m
  left_inv := circle_sobolev_conjugate_linear_involutive T m
  right_inv := circle_sobolev_conjugate_linear_involutive T m
  map_add' := (circleSobolevConjugateLinear T m).map_add
  map_smul' := (circleSobolevConjugateLinear T m).map_smul
  norm_map' := circle_sobolev_conjugate_linear_norm T m

@[simp] theorem circle_sobolev_conjugation_coordinate (m : ℕ) (j : Fin (m+1))
    (f : CircleSobolevSpace T m) :
    circleSobolevCoordinate T m j (circleSobolevConjugation T m f) =
      circleConjugate T (circleSobolevCoordinate T m j f) := rfl

@[simp] theorem circle_sobolev_conjugation_involutive (m : ℕ)
    (f : CircleSobolevSpace T m) :
    circleSobolevConjugation T m (circleSobolevConjugation T m f) = f :=
  circle_sobolev_conjugate_linear_involutive T m f

theorem circle_sobolev_conjugation_derivative (m : ℕ)
    (f : CircleSobolevSpace T (m+1)) :
    circleSobolevDerivative T m (circleSobolevConjugation T (m+1) f) =
      circleSobolevConjugation T m (circleSobolevDerivative T m f) := by
  apply circle_sobolev_value_injective T m
  simp only [circle_sobolev_derivative_coordinate,circle_sobolev_conjugation_coordinate]

theorem circle_continuous_l2_star (f : C(AddCircle T, ℂ)) :
    circleContinuousL2 T (star f) = circleConjugate T (circleContinuousL2 T f) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ) (star f),
    circle_conjugate_ae T (circleContinuousL2 T f),
    ContinuousMap.coeFn_toLp (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ) f]
    with x hstar hc hf
  change circleContinuousL2 T (star f) x = conj (f x) at hstar
  change circleContinuousL2 T f x = f x at hf
  change circleContinuousL2 T (star f) x = circleConjugate T (circleContinuousL2 T f) x
  rw [hstar,hc,hf]

theorem circle_sobolev_h1_embedding_conjugation (f : CircleSobolevSpace T 1) :
    circleSobolevH1Embedding T (circleSobolevConjugation T 1 f) =
      star (circleSobolevH1Embedding T f) := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
  change circleContinuousL2 T (circleSobolevH1Embedding T (circleSobolevConjugation T 1 f)) =
    circleContinuousL2 T (star (circleSobolevH1Embedding T f))
  rw [circle_sobolev_h1_embedding_l2,circle_continuous_l2_star,
    circle_sobolev_conjugation_coordinate,circle_sobolev_h1_embedding_l2]

@[simp] theorem circle_sobolev_h1_conjugation_apply
    (f : CircleSobolevSpace T 1) (x : AddCircle T) :
    circleSobolevH1Embedding T (circleSobolevConjugation T 1 f) x =
      conj (circleSobolevH1Embedding T f x) := by
  rw [circle_sobolev_h1_embedding_conjugation]
  rfl

end Lemniscate
