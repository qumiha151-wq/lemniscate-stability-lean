import SolitonClassification.Rotating.IntegerWindingTrueStep
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace SolitonClassification.Rotating.IntegerWinding
noncomputable section
open Set Metric UniversalMajorant
open scoped ContDiff

/-- Uniqueness for any pair of actual solutions on a compact interval.
The union of the two compact images provides a Lipschitz set even if the
supplied trajectories have no box or derivative-size bound. -/
theorem signed_solution_agreement {x y : ℝ → State} {σ T : ℝ}
    (hx : ∀s ∈ Icc 0 T, HasDerivAt x (σ • field (x s)) s)
    (hy : ∀s ∈ Icc 0 T, HasDerivAt y (σ • field (y s)) s)
    (h0 : x 0=y 0) : EqOn x y (Icc 0 T) := by
  let I := Icc (0:ℝ) T
  let K := x '' I ∪ y '' I
  have cx : ContinuousOn x I := fun t ht => (hx t ht).continuousAt.continuousWithinAt
  have cy : ContinuousOn y I := fun t ht => (hy t ht).continuousAt.continuousWithinAt
  have hk : IsCompact K := (isCompact_Icc.image_of_continuousOn cx).union
    (isCompact_Icc.image_of_continuousOn cy)
  have hfield : ContDiff ℝ 1 field := field_smooth.of_le (by decide)
  have hs : ContDiff ℝ 1 (fun z : State => σ • field z) := hfield.const_smul σ
  obtain ⟨C,hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hk
    hs.locallyLipschitz.locallyLipschitzOn
  exact ODE_solution_unique_of_mem_Icc_right (v:=fun _ z => σ • field z) (s:=fun _ => K) (K:=C)
    (fun _ _ => hC) cx (fun t ht => (hx t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => Or.inl (mem_image_of_mem _ (Ico_subset_Icc_self ht))) cy
    (fun t ht => (hy t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => Or.inr (mem_image_of_mem _ (Ico_subset_Icc_self ht))) h0

/-- The local Taylor certificate applies to every supplied original
trajectory with the stated initial state, including a restriction of a
longer integration. No tube assumption on that trajectory is needed. -/
theorem every_true_taylor_step {a : State} (ha : a ∈ nodeBox) {σ : ℝ} (hσ : |σ|≤1)
    {x : ℝ → State} (h0 : x 0=a)
    (hx : ∀s ∈ Icc 0 (universalStepCap:ℝ), HasDerivAt x (σ • field (x s)) s)
    {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖x t-polynomialPath (taylorPolynomial a 60) (σ*t)‖ ≤ (2:ℝ)/10^59 := by
  obtain ⟨y,hy0,hy,he⟩ := exists_true_taylor_step ha σ hσ
  have hd s (hs : s∈Icc 0 (universalStepCap:ℝ)) : HasDerivAt y (σ • field (y s)) s := by
    apply hy
    exact ⟨by linarith [hs.1], hs.2.trans_lt (by norm_num [universalStepCap])⟩
  rw [signed_solution_agreement hx hd (h0.trans hy0.symm) ht]
  exact he t ht

end
end SolitonClassification.Rotating.IntegerWinding

#print axioms SolitonClassification.Rotating.IntegerWinding.every_true_taylor_step
