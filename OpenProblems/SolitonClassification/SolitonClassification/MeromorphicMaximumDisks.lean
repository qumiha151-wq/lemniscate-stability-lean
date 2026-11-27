import SolitonClassification.MeromorphicGoodRadii
import Mathlib.Analysis.Complex.Liouville

noncomputable section
open Complex Metric Set
namespace ClosedSimilarity.MeromorphicGrowth

/-- At arbitrarily high starting radii an entire function has a point of at least
the starting amplitude whose first four (indeed all) derivatives are controlled
by Cauchy's estimate with a reciprocal square-root radius. -/
theorem exists_cauchy_point {f : ℂ → ℂ} (hf : Differentiable ℂ f) (x : ℂ) :
    ∃z : ℂ, ∃h : ℝ, 1≤h ∧ ‖f x‖≤‖f z‖ ∧ h^2=1+‖f z‖ ∧
      ∀n : ℕ, ‖iteratedDeriv n f z‖ ≤ (n.factorial:ℝ)*4*h^(n+2) := by
  classical
  let B (r : ℝ) := closedBall (0:ℂ) (max 0 r)
  have maxP (r : ℝ) : ∃z∈B r,∀w∈B r,‖f w‖≤‖f z‖ := by
    obtain ⟨z,hz,hmax⟩ := (isCompact_closedBall (0:ℂ) (max 0 r)).exists_isMaxOn
      ⟨0,mem_closedBall_self (le_max_left _ _)⟩ hf.continuous.norm.continuousOn
    exact ⟨z,hz,fun _ hw=>hmax hw⟩
  choose point pin peak using maxP
  let H (r : ℝ) := Real.sqrt (1+‖f (point r)‖)
  have Hp (r : ℝ) : 0<H r := Real.sqrt_pos.mpr (by positivity)
  have H2 (r : ℝ) : H r^2=1+‖f (point r)‖ := Real.sq_sqrt (by positivity)
  have Hmono : Monotone H := by
    intro r u ru
    apply Real.sqrt_le_sqrt
    exact add_le_add_right (peak u _ ((closedBall_subset_closedBall (max_le_max_left 0 ru)) (pin r))) _
  obtain ⟨r,xr,gr⟩:=exists_doubling_radius H Hp Hmono ‖x‖
  let z:=point r
  let h:=H r
  have rr : 0≤r := (norm_nonneg x).trans xr
  have h1 : 1≤h := by dsimp [h];nlinarith only [Hp r,H2 r,norm_nonneg (f (point r))]
  have member : x∈B r := by simpa [B,max_eq_right rr] using xr
  refine ⟨z,h,h1,peak r x member,H2 r,?_⟩
  let R:=r+4/h
  have Rp : 0≤R := add_nonneg rr (div_nonneg (by norm_num) (Hp r).le)
  have bound (w : ℂ) (hw : w∈sphere z (1/h)) : ‖f w‖≤4*h^2 := by
    have zd : ‖z‖≤r := by simpa [B,max_eq_right rr,z] using pin r
    have ds : dist w z=1/h := hw
    have wm : w∈B R := by
      change w∈closedBall 0 (max 0 R)
      rw [mem_closedBall,dist_zero_right,max_eq_right Rp]
      have triangle := dist_triangle w z (0:ℂ)
      rw [ds,dist_zero_right,dist_zero_right] at triangle
      have small : 1/h≤4/h := by gcongr; norm_num
      exact triangle.trans ((add_le_add small zd).trans (le_of_eq (add_comm _ _)))
    have Hge : H R≤2*h := gr
    have sqle := mul_self_le_mul_self (Hp R).le Hge
    have pk := peak R w wm
    nlinarith only [sqle,H2 R,pk]
  intro n
  have est:=Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (one_div_pos.mpr (Hp r)) hf.diffContOnCl bound
  calc ‖iteratedDeriv n f z‖ ≤ n.factorial*(4*h^2)/(1/h)^n := est
       _ = (n.factorial:ℝ)*4*h^(n+2) := by rw [pow_add];simp only [one_div,inv_pow,div_inv_eq_mul];ring

end ClosedSimilarity.MeromorphicGrowth

