import Lemniscate.Algebra
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.FunProp

/-! Uniqueness for the complex-valued second-order equation f''=1-3*f^2.
On each compact time interval, the two solution trajectories lie in a compact
ball. The polynomial vector field is Lipschitz there; no numerical constant
or global bound on the trajectories is assumed. -/
namespace Lemniscate
open Complex Metric Set

theorem quadratic_second_order_unique (f f₁ g g₁ : ℝ → ℂ)
    (hf : ∀ t, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t, HasDerivAt f₁ (1-3*(f t)^2) t)
    (hg : ∀ t, HasDerivAt g (g₁ t) t)
    (hg₁ : ∀ t, HasDerivAt g₁ (1-3*(g t)^2) t)
    (h0 : f 0 = g 0) (h1 : f₁ 0 = g₁ 0) : f = g ∧ f₁ = g₁ := by
  let F : ℂ × ℂ → ℂ × ℂ := fun u => (u.2,1-3*u.1^2)
  let sf : ℝ → ℂ × ℂ := fun t => (f t,f₁ t)
  let sg : ℝ → ℂ × ℂ := fun t => (g t,g₁ t)
  have hF : ContDiff ℝ 1 F := by dsimp only [F]; fun_prop
  have hsf (t : ℝ) : HasDerivAt sf (F (sf t)) t := (hf t).prodMk (hf₁ t)
  have hsg (t : ℝ) : HasDerivAt sg (F (sg t)) t := (hg t).prodMk (hg₁ t)
  have hcf : Continuous sf := continuous_iff_continuousAt.mpr (fun t => (hsf t).continuousAt)
  have hcg : Continuous sg := continuous_iff_continuousAt.mpr (fun t => (hsg t).continuousAt)
  have hinit : sf 0 = sg 0 := Prod.ext h0 h1
  have heq : sf = sg := by
    funext t
    let A := min 0 t-1
    let B := max 0 t+1
    have hzero : (0:ℝ) ∈ Ioo A B := by
      constructor
      · dsimp only [A]; linarith only [min_le_left (0:ℝ) t]
      · dsimp only [B]; linarith only [le_max_left (0:ℝ) t]
    have ht : t ∈ Icc A B := by
      constructor
      · dsimp only [A]; linarith only [min_le_right (0:ℝ) t]
      · dsimp only [B]; linarith only [le_max_right (0:ℝ) t]
    have hcompact : IsCompact (sf '' Icc A B ∪ sg '' Icc A B) :=
      (isCompact_Icc.image hcf).union (isCompact_Icc.image hcg)
    obtain ⟨R,hR⟩ := hcompact.isBounded.exists_norm_le
    obtain ⟨K,hK⟩ := hF.contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_closedBall (0:ℂ × ℂ) R) (isCompact_closedBall (0:ℂ × ℂ) R)
    have hfs (u : ℝ) (hu : u ∈ Icc A B) : sf u ∈ closedBall (0:ℂ × ℂ) R := by
      rw [mem_closedBall,dist_zero_right]
      exact hR _ (Or.inl ⟨u,hu,rfl⟩)
    have hgs (u : ℝ) (hu : u ∈ Icc A B) : sg u ∈ closedBall (0:ℂ × ℂ) R := by
      rw [mem_closedBall,dist_zero_right]
      exact hR _ (Or.inr ⟨u,hu,rfl⟩)
    exact ODE_solution_unique_of_mem_Icc
      (v := fun _ => F) (s := fun _ => closedBall (0:ℂ × ℂ) R)
      (fun _ _ => hK) hzero hcf.continuousOn (fun u _ => hsf u)
      (fun u hu => hfs u (Ioo_subset_Icc_self hu))
      hcg.continuousOn (fun u _ => hsg u)
      (fun u hu => hgs u (Ioo_subset_Icc_self hu)) hinit ht
  exact ⟨funext fun t => congrArg Prod.fst (congrFun heq t),
    funext fun t => congrArg Prod.snd (congrFun heq t)⟩

end Lemniscate
