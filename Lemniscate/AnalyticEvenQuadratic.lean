import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.LinearCombination

/-! Only a quadratic bound is needed for the upper spectral-gap estimate.
An even analytic function vanishing at zero has no constant or linear term. -/
namespace Lemniscate
open Complex Filter Asymptotics
open scoped Topology

theorem analytic_even_quadratic_bound (μ : ℂ → ℂ) (hμ : AnalyticAt ℂ μ 0)
    (hμ0 : μ 0 = 0) (heven : ∀ᶠ z in 𝓝 (0:ℂ), μ (-z) = μ z) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 (0:ℂ), ‖μ z‖ ≤ C*‖z‖^2 := by
  have hd : HasDerivAt μ (deriv μ 0) 0 := hμ.differentiableAt.hasDerivAt
  have hdneg : HasDerivAt (fun z : ℂ => μ (-z)) (-deriv μ 0) 0 := by
    have hn : HasDerivAt (fun z : ℂ => -z) (-1) 0 := by
      convert! (hasDerivAt_id (0:ℂ)).neg using 1 <;> rfl
    have hc := HasDerivAt.comp_of_eq (h₂ := μ) (h := fun z : ℂ => -z) (x := 0)
      hd hn (by simp)
    simpa only [Function.comp_def,mul_neg,mul_one] using hc
  have hd0 : deriv μ 0 = 0 := by
    have heqfun : (fun z : ℂ => μ (-z)) =ᶠ[𝓝 (0:ℂ)] μ := heven
    have heq := (hdneg.congr_of_eventuallyEq heqfun.symm).unique hd
    linear_combination -(1/2:ℂ)*heq
  obtain ⟨p,hp⟩ := hμ
  have hfd : fderiv ℂ μ 0 = 0 := by
    rw [← toSpanSingleton_deriv,hd0]
    simp
  have hp1 : p 1 = 0 := by
    apply (continuousMultilinearCurryFin1 ℂ ℂ ℂ).injective
    rw [← hp.fderiv_eq,hfd,map_zero]
  have hpartial (z : ℂ) : p.partialSum 2 z = 0 := by
    simp only [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add]
    rw [hp.coeff_zero,hμ0,hp1]
    simp
  have hO : μ =O[𝓝 (0:ℂ)] (fun z : ℂ => ‖z‖^2) := by
    simpa only [zero_add,hpartial,sub_zero] using hp.isBigO_sub_partialSum_pow 2
  obtain ⟨C,hC,hbound⟩ := hO.exists_pos
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound.bound] with z hz
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖z‖)] using hz

end Lemniscate
