import Lemniscate.NormalGraphProjection

/-! Comparison of the actual local normal projections. This is the C0
parameter-continuity step for choosing an initial rotation by a scalar
phase condition; no phase condition or rotation family is assumed here. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ComplexConjugate

/-- Local normal projections depend Lipschitz continuously on the curve
in the uniform norm. In particular, each local projection root is unique.
Only the reference Frenet frame and the C1 projection neighborhood enter. -/
theorem normal_projection_height_comparison
    (γ₀ γ₁ β T₀ Tβ : ℝ → ℂ) (k : ℝ → ℝ)
    (hγ₀ : ∀ u, HasDerivAt γ₀ (T₀ u) u)
    (hTβ : ∀ u, HasDerivAt Tβ (I*(k u:ℂ)*Tβ u) u)
    (hu₀ : ∀ u, ‖T₀ u‖ = 1) (huβ : ∀ u, ‖Tβ u‖ = 1)
    (K δ r : ℝ) (hK : 0 ≤ K)
    (hk : ∀ u, |k u| ≤ K)
    (htangent : ∀ u, ‖T₀ u-Tβ u‖ ≤ δ)
    (hsmall : δ+K*r ≤ 1/2)
    (s x₀ x₁ : ℝ) (hx₀ : |x₀-s| ≤ r) (hx₁ : |x₁-s| ≤ r)
    (hroot₀ : (conj (Tβ s)*(γ₀ x₀-β s)).re = 0)
    (hroot₁ : (conj (Tβ s)*(γ₁ x₁-β s)).re = 0) :
    |x₀-x₁| ≤ 2*‖γ₀ x₁-γ₁ x₁‖ ∧
      |(conj (Tβ s)*(γ₀ x₀-β s)).im-
        (conj (Tβ s)*(γ₁ x₁-β s)).im| ≤ 3*‖γ₀ x₁-γ₁ x₁‖ := by
  have hγlip (a b : ℝ) : ‖γ₀ b-γ₀ a‖ ≤ |b-a| := by
    simpa only [Real.norm_eq_abs,one_mul] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := (Set.univ : Set ℝ)) (C := 1)
        (fun u _ => (hγ₀ u).hasDerivWithinAt)
        (fun u _ => (hu₀ u).le) convex_univ (mem_univ a) (mem_univ b)
  have hTlip (a b : ℝ) : ‖Tβ b-Tβ a‖ ≤ K*|b-a| := by
    have hb (u : ℝ) : ‖I*(k u:ℂ)*Tβ u‖ ≤ K := by
      simpa only [norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
        huβ u,one_mul,mul_one] using hk u
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := (Set.univ : Set ℝ)) (C := K)
        (fun u _ => (hTβ u).hasDerivWithinAt) (fun u _ => hb u)
        convex_univ (mem_univ a) (mem_univ b)
  have hself : conj (Tβ s)*Tβ s = 1 := by
    rw [Complex.conj_mul',huβ s]
    norm_num
  let P : ℝ → ℝ := fun u => (conj (Tβ s)*(γ₀ u-β s)).re
  let F : ℝ → ℝ := fun u => u-P u
  have hP (u : ℝ) : HasDerivAt P (conj (Tβ s)*T₀ u).re u := by
    simpa only [P,Function.comp_def,Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt u
        (((hγ₀ u).sub_const (β s)).const_mul (conj (Tβ s)))
  have hFd (u : ℝ) : HasDerivAt F (1-(conj (Tβ s)*T₀ u).re) u :=
    (hasDerivAt_id u).sub (hP u)
  have hdbound (u : ℝ) (hu : u ∈ Metric.closedBall s r) :
      ‖1-(conj (Tβ s)*T₀ u).re‖ ≤ (1/2:ℝ) := by
    have hus : |u-s| ≤ r := by simpa only [Metric.mem_closedBall,Real.dist_eq] using hu
    have hTdist : ‖T₀ u-Tβ s‖ ≤ δ+K*r := by
      calc
        _ ≤ ‖T₀ u-Tβ u‖+‖Tβ u-Tβ s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ δ+K*|u-s| := add_le_add (htangent u) (hTlip s u)
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hus hK)
    have heq : 1-(conj (Tβ s)*T₀ u).re =
        (conj (Tβ s)*(Tβ s-T₀ u)).re := by
      rw [mul_sub,hself,Complex.sub_re,Complex.one_re]
    rw [Real.norm_eq_abs,heq]
    calc
      _ ≤ ‖conj (Tβ s)*(Tβ s-T₀ u)‖ := Complex.abs_re_le_norm _
      _ = ‖T₀ u-Tβ s‖ := by
        rw [norm_mul,Complex.norm_conj,huβ s,one_mul,norm_sub_rev]
      _ ≤ 1/2 := hTdist.trans hsmall
  have hlip : |F x₀-F x₁| ≤ (1/2:ℝ)*|x₀-x₁| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := F) (f' := fun u => 1-(conj (Tβ s)*T₀ u).re)
        (fun u _ => (hFd u).hasDerivWithinAt) hdbound
        (convex_closedBall s r)
        (show x₁ ∈ Metric.closedBall s r from by simpa only [Metric.mem_closedBall,Real.dist_eq] using hx₁)
        (show x₀ ∈ Metric.closedBall s r from by simpa only [Metric.mem_closedBall,Real.dist_eq] using hx₀)
  have hresidual : |P x₁| ≤ ‖γ₀ x₁-γ₁ x₁‖ := by
    have heq : P x₁ = (conj (Tβ s)*(γ₀ x₁-γ₁ x₁)).re := by
      change (conj (Tβ s)*(γ₀ x₁-β s)).re = _
      rw [show γ₀ x₁-β s = (γ₀ x₁-γ₁ x₁)+(γ₁ x₁-β s) by ring,
        mul_add,Complex.add_re,hroot₁,add_zero]
    rw [heq]
    exact (Complex.abs_re_le_norm _).trans_eq (by
      rw [norm_mul,Complex.norm_conj,huβ s,one_mul])
  have htriangle : |x₀-x₁| ≤ |F x₀-F x₁|+|P x₁| := by
    have heq : x₀-x₁ = (F x₀-F x₁)-P x₁ := by
      have hz : P x₀ = 0 := hroot₀
      dsimp only [F]
      rw [hz]
      ring
    rw [heq]
    exact abs_sub _ _
  have hrootdist : |x₀-x₁| ≤ 2*‖γ₀ x₁-γ₁ x₁‖ := by
    linarith only [htriangle,hlip,hresidual]
  refine ⟨hrootdist,?_⟩
  have him : (conj (Tβ s)*(γ₀ x₀-β s)).im-
      (conj (Tβ s)*(γ₁ x₁-β s)).im =
      (conj (Tβ s)*(γ₀ x₀-γ₁ x₁)).im := by
    rw [← Complex.sub_im,← mul_sub]
    congr 2
    ring
  rw [him]
  calc
    _ ≤ ‖conj (Tβ s)*(γ₀ x₀-γ₁ x₁)‖ := Complex.abs_im_le_norm _
    _ = ‖γ₀ x₀-γ₁ x₁‖ := by rw [norm_mul,Complex.norm_conj,huβ s,one_mul]
    _ ≤ ‖γ₀ x₀-γ₀ x₁‖+‖γ₀ x₁-γ₁ x₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ |x₀-x₁|+‖γ₀ x₁-γ₁ x₁‖ := add_le_add (hγlip x₁ x₀) le_rfl
    _ ≤ _ := by linarith only [hrootdist]

end Lemniscate
