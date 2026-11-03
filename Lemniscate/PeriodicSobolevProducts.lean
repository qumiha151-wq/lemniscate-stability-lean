import Lemniscate.PeriodicSobolevH4Jet
import Lemniscate.PeriodicSobolevInterpolation
import Lemniscate.PeriodicMultiplication

/-! Products involving the second and third derivatives of H4 data.
The second derivative has a continuous representative already at H3. The
derivative square-sum interpolation estimate then gives H2-H4 product bounds.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

/-- The continuous second derivative of H3 data. -/
def circleSobolevH3Second :
    CircleSobolevSpace T 3 →L[ℂ] C(AddCircle T, ℂ) :=
  (circleSobolevH1Embedding T).comp
    ((circleSobolevDerivative T 1).comp (circleSobolevDerivative T 2))

theorem circle_sobolev_h3_second_l2 (f : CircleSobolevSpace T 3) :
    circleContinuousL2 T (circleSobolevH3Second T f) =
      circleSobolevCoordinate T 3 2 f := by
  change circleContinuousL2 T
      (circleSobolevH1Embedding T
        (circleSobolevDerivative T 1 (circleSobolevDerivative T 2 f))) = _
  rw [circle_sobolev_h1_embedding_l2]
  rfl

theorem circle_sobolev_h4_second_eq (f : CircleSobolevSpace T 4) :
    circleSobolevH3Second T (circleSobolevInclusion T 3 f) =
      circleSobolevContinuousJet T f 2 := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
  change circleContinuousL2 T
      (circleSobolevH3Second T (circleSobolevInclusion T 3 f)) =
    circleContinuousL2 T (circleSobolevContinuousJet T f 2)
  rw [circle_sobolev_h3_second_l2,circle_sobolev_continuous_jet_l2]
  rfl

theorem circle_sobolev_h3_second_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ f : CircleSobolevSpace T 3,
      ‖circleSobolevH3Second T f‖ ≤ C*‖f‖ := by
  obtain ⟨C,hC,hbound⟩ := circle_sobolev_h1_embedding_bound T
  refine ⟨C,hC,fun f => ?_⟩
  have hD₁ :
      ‖circleSobolevDerivative T 1 (circleSobolevDerivative T 2 f)‖ ≤
        ‖circleSobolevDerivative T 2 f‖ := by
    simpa only [one_mul] using (circleSobolevDerivative T 1).le_of_opNorm_le
      (circle_sobolev_derivative_norm_le T 1) (circleSobolevDerivative T 2 f)
  have hD₂ : ‖circleSobolevDerivative T 2 f‖ ≤ ‖f‖ := by
    simpa only [one_mul] using (circleSobolevDerivative T 2).le_of_opNorm_le
      (circle_sobolev_derivative_norm_le T 2) f
  exact (hbound _).trans
    (mul_le_mul_of_nonneg_left (hD₁.trans hD₂) hC.le)

private theorem circle_sobolev_h3_mixed_interpolation
    (f g : CircleSobolevSpace T 4) :
    ‖circleSobolevInclusion T 3 f‖*‖circleSobolevInclusion T 3 g‖ ≤
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖*‖g‖+
        ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖*‖f‖ := by
  let f₃ := circleSobolevInclusion T 3 f
  let g₃ := circleSobolevInclusion T 3 g
  let f₂ := circleSobolevInclusion T 2 f₃
  let g₂ := circleSobolevInclusion T 2 g₃
  change ‖f₃‖*‖g₃‖ ≤ ‖f₂‖*‖g‖+‖g₂‖*‖f‖
  have hf : ‖f₃‖^2 ≤ 2*‖f₂‖*‖f‖ := circle_sobolev_h3_interpolation T f
  have hg : ‖g₃‖^2 ≤ 2*‖g₂‖*‖g‖ := circle_sobolev_h3_interpolation T g
  have hprod : ‖f₃‖^2*‖g₃‖^2 ≤
      (2*‖f₂‖*‖f‖)*(2*‖g₂‖*‖g‖) :=
    mul_le_mul hf hg (sq_nonneg ‖g₃‖) (by positivity)
  have hsq : (‖f₃‖*‖g₃‖)^2 ≤ (‖f₂‖*‖g‖+‖g₂‖*‖f‖)^2 := by
    nlinarith [sq_nonneg (‖f₂‖*‖g‖-‖g₂‖*‖f‖)]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

/-- A single period-dependent constant gives the mixed product estimates
needed for powers and differences in the normal-graph equation. -/
theorem circle_sobolev_second_product_bounds :
    ∃ K : ℝ, 0 < K ∧ ∀ f g h : CircleSobolevSpace T 4,
      let H₂f := ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖
      let H₂g := ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖
      let H₂h := ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 h)‖
      ‖circleMultiplyL2 T (circleSobolevContinuousJet T f 2)
          (circleSobolevCoordinate T 4 2 g)‖ ≤ K*‖f‖*H₂g ∧
        ‖circleMultiplyL2 T
          (circleSobolevContinuousJet T f 2*circleSobolevContinuousJet T g 2)
          (circleSobolevCoordinate T 4 2 h)‖ ≤
            K*(H₂f*‖g‖+H₂g*‖f‖)*H₂h ∧
        ‖circleMultiplyL2 T (circleSobolevContinuousJet T f 2)
          (circleSobolevCoordinate T 4 3 g)‖ ≤
            K*(H₂f*‖g‖+H₂g*‖f‖) := by
  obtain ⟨C,hC,hbound⟩ := circle_sobolev_h3_second_bound T
  let K : ℝ := C^2+C+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hK₁ : C ≤ K := by dsimp [K]; nlinarith [sq_nonneg C]
  have hK₂ : C^2 ≤ K := by dsimp [K]; nlinarith
  have hsup (u : CircleSobolevSpace T 4) :
      ‖circleSobolevContinuousJet T u 2‖ ≤ C*‖circleSobolevInclusion T 3 u‖ := by
    rw [← circle_sobolev_h4_second_eq]
    exact hbound _
  have hsup₄ (u : CircleSobolevSpace T 4) :
      ‖circleSobolevContinuousJet T u 2‖ ≤ C*‖u‖ := by
    have hinc : ‖circleSobolevInclusion T 3 u‖ ≤ ‖u‖ := by
      simpa only [one_mul] using (circleSobolevInclusion T 3).le_of_opNorm_le
        (circle_sobolev_inclusion_norm_le T 3) u
    exact (hsup u).trans (mul_le_mul_of_nonneg_left hinc hC.le)
  have hD₂ (u : CircleSobolevSpace T 4) :
      ‖circleSobolevCoordinate T 4 2 u‖ ≤
        ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 u)‖ := by
    let u₂ := circleSobolevInclusion T 2 (circleSobolevInclusion T 3 u)
    change ‖circleSobolevCoordinate T 2 2 u₂‖ ≤ ‖u₂‖
    simpa only [one_mul] using (circleSobolevCoordinate T 2 2).le_of_opNorm_le
      (circle_sobolev_coordinate_norm_le T 2 2) u₂
  have hD₃ (u : CircleSobolevSpace T 4) :
      ‖circleSobolevCoordinate T 4 3 u‖ ≤ ‖circleSobolevInclusion T 3 u‖ := by
    let u₃ := circleSobolevInclusion T 3 u
    change ‖circleSobolevCoordinate T 3 3 u₃‖ ≤ ‖u₃‖
    simpa only [one_mul] using (circleSobolevCoordinate T 3 3).le_of_opNorm_le
      (circle_sobolev_coordinate_norm_le T 3 3) u₃
  refine ⟨K,hK,fun f g h => ?_⟩
  let f₃ := circleSobolevInclusion T 3 f
  let g₃ := circleSobolevInclusion T 3 g
  let f₂ := circleSobolevInclusion T 2 f₃
  let g₂ := circleSobolevInclusion T 2 g₃
  let h₂ := circleSobolevInclusion T 2 (circleSobolevInclusion T 3 h)
  let a := circleSobolevContinuousJet T f 2
  let b := circleSobolevContinuousJet T g 2
  let B : ℝ := ‖f₂‖*‖g‖+‖g₂‖*‖f‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmix : ‖f₃‖*‖g₃‖ ≤ B := circle_sobolev_h3_mixed_interpolation T f g
  have hab : ‖a*b‖ ≤ C^2*B := by
    calc
      ‖a*b‖ ≤ ‖a‖*‖b‖ := norm_mul_le a b
      _ ≤ (C*‖f₃‖)*(C*‖g₃‖) :=
        mul_le_mul (hsup f) (hsup g) (norm_nonneg b) (by positivity)
      _ = C^2*(‖f₃‖*‖g₃‖) := by ring
      _ ≤ C^2*B := mul_le_mul_of_nonneg_left hmix (sq_nonneg C)
  change ‖circleMultiplyL2 T a (circleSobolevCoordinate T 4 2 g)‖ ≤
      K*‖f‖*‖g₂‖ ∧
    ‖circleMultiplyL2 T (a*b) (circleSobolevCoordinate T 4 2 h)‖ ≤ K*B*‖h₂‖ ∧
    ‖circleMultiplyL2 T a (circleSobolevCoordinate T 4 3 g)‖ ≤ K*B
  refine ⟨?_,?_,?_⟩
  · calc
      ‖circleMultiplyL2 T a (circleSobolevCoordinate T 4 2 g)‖ ≤
          ‖a‖*‖circleSobolevCoordinate T 4 2 g‖ := circle_multiply_l2_norm_le T _ _
      _ ≤ (C*‖f‖)*‖g₂‖ := mul_le_mul (hsup₄ f) (hD₂ g)
        (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg f))
      _ = C*‖f‖*‖g₂‖ := by ring
      _ ≤ K*‖f‖*‖g₂‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hK₁ (norm_nonneg f)) (norm_nonneg g₂)
  · calc
      ‖circleMultiplyL2 T (a*b) (circleSobolevCoordinate T 4 2 h)‖ ≤
          ‖a*b‖*‖circleSobolevCoordinate T 4 2 h‖ := circle_multiply_l2_norm_le T _ _
      _ ≤ (C^2*B)*‖h₂‖ := mul_le_mul hab (hD₂ h)
        (norm_nonneg _) (mul_nonneg (sq_nonneg C) hB)
      _ ≤ K*B*‖h₂‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hK₂ hB) (norm_nonneg h₂)
  · calc
      ‖circleMultiplyL2 T a (circleSobolevCoordinate T 4 3 g)‖ ≤
          ‖a‖*‖circleSobolevCoordinate T 4 3 g‖ := circle_multiply_l2_norm_le T _ _
      _ ≤ (C*‖f₃‖)*‖g₃‖ := mul_le_mul (hsup f) (hD₃ g)
        (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg f₃))
      _ = C*(‖f₃‖*‖g₃‖) := by ring
      _ ≤ C*B := mul_le_mul_of_nonneg_left hmix hC.le
      _ ≤ K*B := mul_le_mul_of_nonneg_right hK₁ hB

end Lemniscate
