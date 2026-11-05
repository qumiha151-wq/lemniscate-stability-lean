import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Field.Periodic

/-! The curvature-profile phase is attained on one period and can be
transferred to the initial curve parameter. No reference field is shifted.

-/
noncomputable section
namespace Lemniscate
open Set MeasureTheory
open scoped Topology

/-- The minimum curvature-profile error is attained on one period. Its
phase may be moved from the reference curvature to the initial curvature. -/
theorem periodic_curvature_phase_minimum
    (T : ℝ) (hT : 0 < T) (kγ kβ : ℝ → ℝ)
    (hγ : Continuous kγ) (hβ : Continuous kβ)
    (hγper : Function.Periodic kγ T) (hβper : Function.Periodic kβ T) :
    ∃ σ ∈ Icc (0:ℝ) T,
      (∀ θ : ℝ,
        (∫ s in (0:ℝ)..T, (kγ s-kβ (s+σ))^2) ≤
          (∫ s in (0:ℝ)..T, (kγ s-kβ (s+θ))^2)) ∧
      (∫ s in (0:ℝ)..T, (kγ s-kβ (s+σ))^2) =
        ∫ s in (0:ℝ)..T, (kγ (s-σ)-kβ s)^2 := by
  let J : ℝ → ℝ := fun σ => ∫ s in (0:ℝ)..T, (kγ s-kβ (s+σ))^2
  have hf : Continuous (Function.uncurry
      (fun σ s : ℝ => (kγ s-kβ (s+σ))^2)) :=
    ((hγ.comp continuous_snd).sub
      (hβ.comp (continuous_snd.add continuous_fst))).pow 2
  have hJ : Continuous J :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 T
  have hJper : Function.Periodic J T := by
    intro σ
    apply intervalIntegral.integral_congr
    intro s _
    change (kγ s-kβ (s+(σ+T)))^2 = (kγ s-kβ (s+σ))^2
    rw [← add_assoc,hβper (s+σ)]
  obtain ⟨σ,hσ,hmin⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).exists_isMinOn
    (nonempty_Icc.mpr hT.le) hJ.continuousOn
  have hmin' := isMinOn_iff.mp hmin
  refine ⟨σ,hσ,?_,?_⟩
  · intro θ
    obtain ⟨u,hu,hJu⟩ := hJper.exists_mem_Ico₀ hT θ
    exact (hmin' u ⟨hu.1,hu.2.le⟩).trans_eq hJu.symm
  · let f : ℝ → ℝ := fun s => (kγ (s-σ)-kβ s)^2
    have hfper : Function.Periodic f T := by
      intro s
      change (kγ ((s+T)-σ)-kβ (s+T))^2 = (kγ (s-σ)-kβ s)^2
      rw [show (s+T)-σ = (s-σ)+T from add_sub_right_comm s T σ,
        hγper (s-σ),hβper s]
    calc
      (∫ s in (0:ℝ)..T, (kγ s-kβ (s+σ))^2) =
          ∫ s in (0:ℝ)..T, f (s+σ) := by
        apply intervalIntegral.integral_congr
        intro s _
        simp only [f,add_sub_cancel_right]
      _ = ∫ s in σ..σ+T, f s := by
        simpa only [zero_add,add_comm T σ] using
          intervalIntegral.integral_comp_add_right (f := f) (a := 0) (b := T) σ
      _ = ∫ s in (0:ℝ)..T, f s := by
        simpa only [zero_add] using hfper.intervalIntegral_add_eq σ 0

end Lemniscate
