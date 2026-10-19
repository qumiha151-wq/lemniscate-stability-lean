import Lemniscate.PeriodicFiniteEnergy
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul

/-! Multiplication by continuous coefficients is a genuine bounded operator on
periodic L2. The resulting second-order energy depends continuously on the
function and its first two L2 derivatives. -/
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped ENNReal ComplexConjugate Topology

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleMultiplyL2 (h : C(AddCircle T, ℂ)) : CircleL2 T →L[ℂ] CircleL2 T :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL AddCircle.haarAddCircle ∞ 2 2
    (ContinuousMap.toLp ∞ AddCircle.haarAddCircle ℂ h)

theorem circle_multiply_l2_ae (h : C(AddCircle T, ℂ)) (f : CircleL2 T) :
    (circleMultiplyL2 T h f : AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun x => h x * f x := by
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    (ContinuousMap.toLp ∞ AddCircle.haarAddCircle ℂ h) f
  filter_upwards [hm, ContinuousMap.coeFn_toLp (p := ∞) AddCircle.haarAddCircle (𝕜 := ℂ) h]
    with x hx hh
  change ((ContinuousLinearMap.mul ℂ ℂ).holder 2
    (ContinuousMap.toLp ∞ AddCircle.haarAddCircle ℂ h) f) x = h x*f x
  simpa only [ContinuousLinearMap.mul_apply', hh] using hx

theorem circle_multiply_l2_norm_le (h : C(AddCircle T, ℂ)) (f : CircleL2 T) :
    ‖circleMultiplyL2 T h f‖ ≤ ‖h‖*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [circle_multiply_l2_ae T h f] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (h.norm_coe_le_norm x) (norm_nonneg _)

theorem circle_multiply_l2_continuous (h f : C(AddCircle T, ℂ)) :
    circleMultiplyL2 T h (circleContinuousL2 T f) = circleContinuousL2 T (h*f) := by
  apply Lp.ext
  filter_upwards [circle_multiply_l2_ae T h (circleContinuousL2 T f),
    ContinuousMap.coeFn_toLp (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ) f,
    ContinuousMap.coeFn_toLp (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ) (h*f)] with x hm hf hp
  change circleMultiplyL2 T h (circleContinuousL2 T f) x = _
  rw [hm]
  change h x*((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ f) x) =
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (h*f)) x
  rw [hf, hp]
  rfl

theorem circle_multiply_pairing_integral (h : C(AddCircle T, ℂ)) (f g : CircleL2 T) :
    inner ℂ f (circleMultiplyL2 T h g) =
      ∫ x : AddCircle T, conj (f x)*h x*g x ∂AddCircle.haarAddCircle := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circle_multiply_l2_ae T h g] with x hx
  rw [RCLike.inner_apply', hx]
  ring

noncomputable def circleH2Energy (h h₂ : C(AddCircle T, ℂ)) (f f₁ f₂ : CircleL2 T) : ℝ :=
  ((-4:ℂ)*inner ℂ f₂ f₂ + 45*inner ℂ f₁ (circleMultiplyL2 T h f₁) -
    42*inner ℂ f f + (15/4:ℂ)*inner ℂ f (circleMultiplyL2 T h₂ f)).re

theorem circle_h2_energy_tendsto {ι : Type*} {l : Filter ι}
    (h h₂ : C(AddCircle T, ℂ)) (F F₁ F₂ : ι → CircleL2 T) (f f₁ f₂ : CircleL2 T)
    (hF : Tendsto F l (𝓝 f)) (hF₁ : Tendsto F₁ l (𝓝 f₁))
    (hF₂ : Tendsto F₂ l (𝓝 f₂)) :
    Tendsto (fun i => circleH2Energy T h h₂ (F i) (F₁ i) (F₂ i)) l
      (𝓝 (circleH2Energy T h h₂ f f₁ f₂)) := by
  have hm₁ := ((circleMultiplyL2 T h).continuous.tendsto f₁).comp hF₁
  have hm₂ := ((circleMultiplyL2 T h₂).continuous.tendsto f).comp hF
  exact (Complex.continuous_re.tendsto _).comp
    ((((hF₂.inner hF₂).const_mul (-4:ℂ)).add ((hF₁.inner hm₁).const_mul (45:ℂ))).sub
      ((hF.inner hF).const_mul (42:ℂ)) |>.add ((hF.inner hm₂).const_mul (15/4:ℂ)))

end Lemniscate
