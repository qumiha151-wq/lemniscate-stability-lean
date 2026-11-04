import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

/-! Comparison of aligned arclength-parametrized planar curves.

The relative unit tangent has speed equal to the absolute curvature
difference.  Integrating this speed, and then the tangent difference,
gives the comparison without a Gronwall estimate.

Candidate draft; compilation is performed separately by the parent task.
-/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory Set
open scoped Topology ComplexConjugate

/-- Curvature differences control both the tangent and the position of two
arclength-parametrized curves whose initial positions and tangents agree. -/
theorem aligned_frenet_comparison
    (γ₀ γ₁ T₀ T₁ : ℝ → ℂ) (κ₀ κ₁ : ℝ → ℝ) (L : ℝ)
    (hκ₀ : Continuous κ₀) (hκ₁ : Continuous κ₁)
    (hγ₀ : ∀ s, HasDerivAt γ₀ (T₀ s) s)
    (hγ₁ : ∀ s, HasDerivAt γ₁ (T₁ s) s)
    (hT₀ : ∀ s, HasDerivAt T₀ (I*(κ₀ s:ℂ)*T₀ s) s)
    (hT₁ : ∀ s, HasDerivAt T₁ (I*(κ₁ s:ℂ)*T₁ s) s)
    (hu₀ : ∀ s, ‖T₀ s‖ = 1) (hu₁ : ∀ s, ‖T₁ s‖ = 1)
    (hposition : γ₁ 0 = γ₀ 0) (htangent : T₁ 0 = T₀ 0) :
    ∀ s ∈ Icc (0:ℝ) L,
      ‖T₁ s-T₀ s‖ ≤ (∫ r in (0:ℝ)..s, |κ₁ r-κ₀ r|) ∧
      ‖γ₁ s-γ₀ s‖ ≤ s*(∫ r in (0:ℝ)..s, |κ₁ r-κ₀ r|) := by
  have hc₀ : Continuous T₀ := continuous_iff_continuousAt.mpr fun s => (hT₀ s).continuousAt
  have hc₁ : Continuous T₁ := continuous_iff_continuousAt.mpr fun s => (hT₁ s).continuousAt
  let R : ℝ → ℂ := fun s => conj (T₀ s)*T₁ s
  have hRcont : Continuous R := (Complex.continuous_conj.comp hc₀).mul hc₁
  have hRnorm (s : ℝ) : ‖R s‖ = 1 := by
    simp only [R,norm_mul,Complex.norm_conj,hu₀,hu₁,one_mul]
  have hself (s : ℝ) : conj (T₀ s)*T₀ s = 1 := by
    rw [Complex.conj_mul',hu₀]
    simp
  have hRzero : R 0 = 1 := by
    dsimp only [R]
    rw [htangent,hself]
  have hRderiv (s : ℝ) :
      HasDerivAt R (I*((κ₁ s-κ₀ s:ℝ):ℂ)*R s) s := by
    convert! (hT₀ s).star.mul (hT₁ s) using 1 <;>
      simp only [R,Complex.star_def,map_mul,Complex.conj_I,
        Complex.conj_ofReal,Complex.ofReal_sub] <;> ring
  have hRprime : Continuous (fun s : ℝ => I*((κ₁ s-κ₀ s:ℝ):ℂ)*R s) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp (hκ₁.sub hκ₀))).mul hRcont
  have hnormdifference (s : ℝ) : ‖T₁ s-T₀ s‖ = ‖R s-1‖ := by
    have heq : conj (T₀ s)*(T₁ s-T₀ s) = R s-1 := by
      rw [mul_sub,hself]
    calc
      ‖T₁ s-T₀ s‖ = ‖conj (T₀ s)*(T₁ s-T₀ s)‖ := by
        rw [norm_mul,Complex.norm_conj,hu₀,one_mul]
      _ = ‖R s-1‖ := congrArg norm heq
  have htbound (s : ℝ) (hs : 0 ≤ s) :
      ‖T₁ s-T₀ s‖ ≤ ∫ r in (0:ℝ)..s, |κ₁ r-κ₀ r| := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hRderiv r) (hRprime.intervalIntegrable 0 s)
    rw [hRzero] at hFTC
    calc
      ‖T₁ s-T₀ s‖ = ‖R s-1‖ := hnormdifference s
      _ = ‖∫ r in (0:ℝ)..s, I*((κ₁ r-κ₀ r:ℝ):ℂ)*R r‖ :=
        congrArg norm hFTC.symm
      _ ≤ ∫ r in (0:ℝ)..s, ‖I*((κ₁ r-κ₀ r:ℝ):ℂ)*R r‖ :=
        intervalIntegral.norm_integral_le_integral_norm hs
      _ = ∫ r in (0:ℝ)..s, |κ₁ r-κ₀ r| := by
        apply intervalIntegral.integral_congr
        intro r _
        simp only [norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
          hRnorm,one_mul,mul_one]
  intro s hs
  refine ⟨htbound s hs.1,?_⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => (hγ₁ r).sub (hγ₀ r)) ((hc₁.sub hc₀).intervalIntegrable 0 s)
  simp only [Pi.sub_apply] at hFTC
  rw [hposition,sub_self,sub_zero] at hFTC
  have hκint : IntervalIntegrable (fun r : ℝ => |κ₁ r-κ₀ r|) volume 0 s :=
    (hκ₁.sub hκ₀).abs.intervalIntegrable 0 s
  have hmono (r : ℝ) (hr : r ∈ Icc (0:ℝ) s) :
      (∫ x in (0:ℝ)..r, |κ₁ x-κ₀ x|) ≤ ∫ x in (0:ℝ)..s, |κ₁ x-κ₀ x| :=
    intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) hκint
  calc
    ‖γ₁ s-γ₀ s‖ = ‖∫ r in (0:ℝ)..s, T₁ r-T₀ r‖ := congrArg norm hFTC.symm
    _ ≤ ∫ r in (0:ℝ)..s, ‖T₁ r-T₀ r‖ :=
      intervalIntegral.norm_integral_le_integral_norm hs.1
    _ ≤ ∫ _r in (0:ℝ)..s, (∫ x in (0:ℝ)..s, |κ₁ x-κ₀ x|) := by
      apply intervalIntegral.integral_mono_on hs.1
        ((hc₁.sub hc₀).norm.intervalIntegrable 0 s) intervalIntegrable_const
      intro r hr
      exact (htbound r hr.1).trans (hmono r hr)
    _ = s*(∫ x in (0:ℝ)..s, |κ₁ x-κ₀ x|) := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero,smul_eq_mul]

end Lemniscate
