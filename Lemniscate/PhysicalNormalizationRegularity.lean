import Lemniscate.PhysicalTimeInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The exact scale and clocks preserve smoothness of a given physical
flow, including its spatial derivatives at the initial boundary. -/
noncomputable section
namespace Lemniscate
open Set
open scoped ContDiff

/-- The physical clock is smooth, and the normalized clock and exact
positive scale are smooth on the nonnegative physical time axis. -/
theorem physical_normalization_regularity
    (a : ℝ) (ha : 0<a) (ρ : ℝ → ℝ)
    (hρ : ∀ t : ℝ, 0≤t → ρ t=(a^4+30*t)^(1/4:ℝ)) :
    ContDiff ℝ ∞ (physicalTime a) ∧
      ContDiffOn ℝ ∞ (normalizedTime a) (Ici (0:ℝ)) ∧
      ContDiffOn ℝ ∞ ρ (Ici (0:ℝ)) := by
  have hT : ContDiff ℝ ∞ (physicalTime a) := by
    change ContDiff ℝ ∞ (fun σ : ℝ => a^4*(Real.exp (30*σ)-1)/30)
    fun_prop
  have hbase : ContDiff ℝ ∞ (timeBase a) := by
    change ContDiff ℝ ∞ (fun t : ℝ => 1+30*t/a^4)
    fun_prop
  have hclock : ContDiffOn ℝ ∞ (normalizedTime a) (Ici (0:ℝ)) := by
    have hlog : ContDiffOn ℝ ∞ (fun t : ℝ => Real.log (timeBase a t)) (Ici (0:ℝ)) :=
      hbase.contDiffOn.log (fun t ht => (timeBase_pos a t ha ht).ne')
    exact (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ => (1/30:ℝ)) (Ici (0:ℝ))).mul hlog
  have hpoly : ContDiffOn ℝ ∞ (fun t : ℝ => a^4+30*t) (Ici (0:ℝ)) := by fun_prop
  have hnz (t : ℝ) (ht : t∈Ici (0:ℝ)) : a^4+30*t≠0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (pow_pos ha 4) (mul_nonneg (by norm_num) ht))
  have hroot : ContDiffOn ℝ ∞ (fun t : ℝ => (a^4+30*t)^(1/4:ℝ)) (Ici (0:ℝ)) :=
    hpoly.rpow_const_of_ne hnz
  exact ⟨hT,hclock,hroot.congr (fun t ht => hρ t ht)⟩

end Lemniscate
