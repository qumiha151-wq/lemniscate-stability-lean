import Lemniscate.PeriodicFiniteSymmetricMatrix

/-! The exact finite matrix of the reduced Bloch quadratic form.
This is an identity for all finite Fourier inputs, before any numerical bound. -/
namespace Lemniscate
open Complex MeasureTheory Matrix
open scoped ComplexConjugate

theorem head_pair_add_right (v x y : Fin 31 → ℂ) :
    headPair v (x+y) = headPair v x+headPair v y := by
  simp only [headPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem head_pair_smul_right (v x : Fin 31 → ℂ) (c : ℂ) :
    headPair v (c • x) = c*headPair v x := by
  simp only [headPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

noncomputable def headProjectionMatrix (a : Fin 31 → ℂ) : Matrix (Fin 31) (Fin 31) ℂ :=
  fun i j => a i*conj (a j)

theorem head_projection_mulVec (a v : Fin 31 → ℂ) :
    headProjectionMatrix a *ᵥ v = headPair a v • a := by
  funext i
  simp only [headProjectionMatrix, mulVec, dotProduct, headPair, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def finiteAnchorProjection : Matrix (Fin 31) (Fin 31) ℂ :=
  headProjectionMatrix (fun i => (finiteAnchorHead i:ℂ))

noncomputable def finiteStableProjection : Matrix (Fin 31) (Fin 31) ℂ :=
  1-finiteAnchorProjection

variable (T : ℝ) [Fact (0 < T)]

theorem circle_fixed_projection_head (v : Fin 31 → ℂ) :
    circleFixedProjectionH4 T (circleEvenHeadH4 T v) =
      circleEvenHeadH4 T (finiteAnchorProjection *ᵥ v) := by
  rw [circleFixedProjectionH4, ← circle_householder_anchor_h4_coe T, circle_anchor_head,
    circle_even_head_inner, finiteAnchorProjection, head_projection_mulVec]
  change headPair (fun i => (finiteAnchorHead i:ℂ)) v •
      circleEvenHeadLinearMap T (fun i => (finiteAnchorHead i:ℂ)) =
    circleEvenHeadLinearMap T (headPair (fun i => (finiteAnchorHead i:ℂ)) v •
      (fun i => (finiteAnchorHead i:ℂ)))
  rw [map_smul]

theorem circle_stable_projection_head (v : Fin 31 → ℂ) :
    circleEvenHeadH4 T v-circleFixedProjectionH4 T (circleEvenHeadH4 T v) =
      circleEvenHeadH4 T (finiteStableProjection *ᵥ v) := by
  rw [circle_fixed_projection_head, finiteStableProjection, sub_mulVec, one_mulVec]
  change circleEvenHeadLinearMap T v-circleEvenHeadLinearMap T (finiteAnchorProjection *ᵥ v) =
    circleEvenHeadLinearMap T (v-finiteAnchorProjection *ᵥ v)
  rw [map_sub]

noncomputable def finiteBlochHeadMatrix (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ) :
    Matrix (Fin 31) (Fin 31) ℂ :=
  let H := finiteSymmetricHeadMatrix T h h₁ h₂
  let P₀ := finiteAnchorProjection
  let P := finiteStableProjection
  let c : ℂ := ((-4*(2*Real.pi/T)^4:ℝ):ℂ)
  P₀ᴴ*H 2*P₀+(c*(α:ℂ)^2) • (P₀ᴴ*P₀)+
    (P₀ᴴ*H 1*P+Pᴴ*H 1*P₀)+
    (α:ℂ) • (P₀ᴴ*H 2*P+Pᴴ*H 2*P₀)+
    (α:ℂ)^2 • (P₀ᴴ*H 3*P+Pᴴ*H 3*P₀)+
    Pᴴ*H 0*P+(α:ℂ) • (Pᴴ*H 1*P)+(α:ℂ)^2 • (Pᴴ*H 2*P)+
    (α:ℂ)^3 • (Pᴴ*H 3*P)+(c*(α:ℂ)^4) • (Pᴴ*P)

theorem circle_finite_bloch_head_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (α : ℝ) (v w : Fin 31 → ℂ) :
    circleFiniteBlochPairing T h h₁ h₂ α (circleEvenHeadH4 T v) (circleEvenHeadH4 T w) =
      headPair v (finiteBlochHeadMatrix T h h₁ h₂ α *ᵥ w) := by
  dsimp only [circleFiniteBlochPairing]
  rw [circle_stable_projection_head T v, circle_stable_projection_head T w]
  simp only [circle_fixed_projection_head,
    circle_finite_symmetric_head_pairing, circle_even_head_pairing, circle_even_head_fourier_at]
  change _ = headPair v (finiteBlochHeadMatrix T h h₁ h₂ α *ᵥ w)
  simp only [finiteBlochHeadMatrix, add_mulVec, smul_mulVec, head_pair_add_right,
    head_pair_smul_right, mulVec_mulVec]
  simp only [head_pair_mulVec_left, mulVec_mulVec, mul_assoc]

end Lemniscate
