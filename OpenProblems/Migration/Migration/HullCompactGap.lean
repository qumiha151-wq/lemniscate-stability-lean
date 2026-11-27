import Mathlib.Analysis.Calculus.Deriv.Prod
import Migration.HullTrajectoryCompactness
import Migration.HullCriticalWindow

noncomputable section
open Set Filter
open scoped Topology
namespace MigrationGeometry.HullGap

theorem no_near_critical_sequence (sm : ContDiff ℝ 1 velocity)
    (Y : ℕ → ℝ → State) (K : ℝ) (e : ℕ → ℝ) (zero : Tendsto e atTop (𝓝 0))
    (dy : ∀ n t, HasDerivAt (Y n) (velocity (Y n t)) t)
    (bound : ∀ n t, ‖Y n t‖≤K)
    (rad : ∀ n t, ((Y n t 2)^2+(Y n t 3)^2)^2 ≤ 2+e n)
    (un : ∀ n t, (Y n t 5)^2+(Y n t 6)^2=1)
    (yh : ∀ n t, -e n≤Y n t 4)
    (ym : ∀ n t, Y n t 7≤Y n 0 7) : False := by
  obtain ⟨j,mono,g,uni,cg,dg⟩ := compact_trajectory velocity sm Y K dy bound
  have ez : Tendsto (fun n => e (j n)) atTop (𝓝 0) :=
    zero.comp mono.tendsto_atTop
  have pt (s : ℝ) (hs : s∈Icc 0 6) (i : Fin 8) :
      Tendsto (fun n => Y (j n) s i) atTop (𝓝 (g s i)) :=
    (continuous_apply i).continuousAt.tendsto.comp (uni.tendsto_at hs)
  apply critical_window_impossible g cg (fun t ht => hasDerivAt_pi.mp (dg t ht))
  · intro s hs
    have cap := le_of_tendsto_of_tendsto (((pt s hs 2).pow 2).add ((pt s hs 3).pow 2) |>.pow 2)
      (tendsto_const_nhds.add ez) (Eventually.of_forall fun n => rad (j n) s)
    rw [add_zero,← A_four,show A^4=(A^2)^2 by ring] at cap
    exact le_of_pow_le_pow_left₀ (by decide : 2≠0) (sq_nonneg A) cap
  · intro s hs
    exact tendsto_nhds_unique (((pt s hs 5).pow 2).add ((pt s hs 6).pow 2))
      (tendsto_const_nhds.congr fun n => (un (j n) s).symm)
  · intro s hs
    simpa using le_of_tendsto_of_tendsto ez.neg (pt s hs 4) (Eventually.of_forall fun n => yh (j n) s)
  · intro s hs
    exact le_of_tendsto_of_tendsto (pt s hs 7) (pt 0 (by constructor <;> norm_num) 7)
      (Eventually.of_forall fun n => ym (j n) s)

end MigrationGeometry.HullGap
#print axioms MigrationGeometry.HullGap.no_near_critical_sequence
