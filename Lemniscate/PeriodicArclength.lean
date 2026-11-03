import Lemniscate.Algebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! A periodic positive speed bounded below by one defines a global increasing
coordinate, with a differentiable inverse and the expected period shift. -/
namespace Lemniscate
open MeasureTheory Filter
open scoped Topology

theorem periodic_integral_coordinate_exists (v : ℝ → ℝ) (hv : Continuous v)
    (hv1 : ∀ u, 1 ≤ v u) (P : ℝ) (hP : 0 < P) (hper : Function.Periodic v P) :
    ∃ e : ℝ ≃o ℝ,
      (∀ u, e u = ∫ t in (0:ℝ)..u, v t) ∧
      (∀ x, HasDerivAt e.symm (v (e.symm x))⁻¹ x) ∧
      0 < e P ∧
      ∀ x, e.symm (x+e P) = e.symm x+P := by
  let X : ℝ → ℝ := fun u => ∫ t in (0:ℝ)..u, v t
  have hD (u : ℝ) : HasDerivAt X (v u) u :=
    intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 u)
      hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt
  have hdif : Differentiable ℝ X := fun u => (hD u).differentiableAt
  have hX0 : X 0 = 0 := by simp [X]
  have hmono : StrictMono X := strictMono_of_hasDerivAt_pos hD
    (fun u => lt_of_lt_of_le zero_lt_one (hv1 u))
  have hgrow (a b : ℝ) (hab : a ≤ b) : b-a ≤ X b-X a := by
    simpa only [one_mul] using mul_sub_le_image_sub_of_le_deriv (C := (1:ℝ)) hdif
      (fun u => by rw [(hD u).deriv]; exact hv1 u) hab
  have hsurj : Function.Surjective X := by
    intro y
    have hlo : ∃ a, X a ≤ y := by
      refine ⟨min y 0,?_⟩
      have h := hgrow (min y 0) 0 (min_le_right y 0)
      rw [hX0] at h
      linarith only [h,min_le_left y 0]
    have hhi : ∃ b, y ≤ X b := by
      refine ⟨max y 0,?_⟩
      have h := hgrow 0 (max y 0) (le_max_right y 0)
      rw [hX0] at h
      linarith only [h,le_max_left y 0]
    exact mem_range_of_exists_le_of_exists_ge hdif.continuous hlo hhi
  let e : ℝ ≃o ℝ :=
    { Equiv.ofBijective X ⟨hmono.injective,hsurj⟩ with
      map_rel_iff' := hmono.le_iff_le }
  have he (u : ℝ) : e u = X u := rfl
  have hinv (x : ℝ) : HasDerivAt e.symm (v (e.symm x))⁻¹ x := by
    apply HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt (hD (e.symm x))
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (hv1 (e.symm x))))
    exact Eventually.of_forall e.apply_symm_apply
  have hshift (u : ℝ) : e (u+P) = e u+e P := by
    simpa only [he,X,zero_add] using
      hper.intervalIntegral_add_eq_add 0 u (fun a b => hv.intervalIntegrable a b)
  refine ⟨e,he,hinv,?_,?_⟩
  · have hp := hmono hP
    simpa only [hX0,he] using hp
  · intro x
    apply e.injective
    rw [e.apply_symm_apply,hshift,e.apply_symm_apply]

end Lemniscate
