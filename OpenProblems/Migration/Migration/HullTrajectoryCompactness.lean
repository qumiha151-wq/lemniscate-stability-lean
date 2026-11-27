import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Migration.CenterInterior

noncomputable section
open Set Filter Metric
open scoped Topology
namespace MigrationGeometry.HullGap

/-- A bounded sequence of solutions of one finite-dimensional smooth field
    admits a convergent solution subsequence on the common observation window.
    A Grönwall estimate on the common state ball controls all clock times. -/
theorem compact_trajectory {n : ℕ} (F : (Fin n→ℝ) → Fin n→ℝ) (sm : ContDiff ℝ 1 F)
    (f : ℕ → ℝ → Fin n→ℝ) (K : ℝ)
    (df : ∀ j t, HasDerivAt (f j) (F (f j t)) t)
    (bound : ∀ j t, ‖f j t‖≤K) :
    ∃ j : ℕ→ℕ, StrictMono j ∧ ∃ g : ℝ → Fin n→ℝ,
      TendstoUniformlyOn (fun m => f (j m)) g atTop (Icc 0 6) ∧
      ContinuousOn g (Icc 0 6) ∧ ∀ t∈Ioo 0 6, HasDerivAt g (F (g t)) t := by
  classical
  let B := closedBall (0:Fin n→ℝ) K
  let I := Icc (0:ℝ) 6
  have cb : IsCompact B := isCompact_closedBall .. 
  have inside (i : ℕ) (t : ℝ) : f i t∈B := by simpa [B,mem_closedBall] using bound i t
  have cf (i : ℕ) : Continuous (f i) :=
    continuous_iff_continuousAt.mpr fun t => (df i t).continuousAt
  obtain ⟨k,lk⟩ := sm.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_closedBall ..) cb
  obtain ⟨a,_,j,mono,limit⟩ := cb.tendsto_subseq (fun i => inside i 0)
  have est (i j : ℕ) (t : ℝ) (ht : t∈I) :
      dist (f i t) (f j t)≤dist (f i 0) (f j 0)*Real.exp ((k:ℝ)*6) := by
    have p := dist_le_of_trajectories_ODE_of_mem (v:=fun _=>F) (s:=fun _=>B)
      (a:=0) (b:=6) (fun _ _ => lk) (cf i).continuousOn
      (fun s _ => (df i s).hasDerivWithinAt) (fun t _ => inside i t)
      (cf j).continuousOn (fun s _ => (df j s).hasDerivWithinAt) (fun t _ => inside j t)
      le_rfl t ht
    simpa only [sub_zero] using p.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith only [ht.2]) k.coe_nonneg)) dist_nonneg)
  have cauchy : UniformCauchySeqOn (fun m => f (j m)) atTop I := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε ep
    let C := Real.exp ((k:ℝ)*6)
    have cp : 0<C := Real.exp_pos _
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp limit.cauchySeq (ε/C) (div_pos ep cp)
    exact ⟨N,fun i hi l hl t ht => (est (j i) (j l) t ht).trans_lt
      ((lt_div_iff₀ cp).mp (hN i hi l hl))⟩
  choose g hg using fun t : I => cauchySeq_tendsto_of_complete (cauchy.cauchySeq t.property)
  let G := fun t : ℝ => if h : t∈I then g ⟨t,h⟩ else 0
  have pt (t : ℝ) (ht : t∈I) : Tendsto (fun m => f (j m) t) atTop (𝓝 (G t)) := by
    simpa [G,ht] using hg ⟨t,ht⟩
  have uni := cauchy.tendstoUniformlyOn_of_tendsto pt
  have gin (t : ℝ) (ht : t∈I) : G t∈B :=
    cb.isClosed.mem_of_tendsto (pt t ht) (Eventually.of_forall fun m => inside (j m) t)
  have vuni : TendstoUniformlyOn (fun m t => F (f (j m) t)) (F ∘ G) atTop I := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε ep
    have dp : 0<(k:ℝ)+1 := by positivity
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp uni (ε/((k:ℝ)+1)) (div_pos ep dp)] with m hm
    intro t ht
    have hle := lk.dist_le_mul _ (gin t ht) _ (inside (j m) t)
    exact hle.trans_lt (lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by linarith : (k:ℝ)≤k+1) dist_nonneg)
      ((lt_div_iff₀ dp).mp (hm t ht) |> fun k => by linarith only [k]))
  refine ⟨j,mono,G,uni,uni.continuousOn (Eventually.of_forall fun m => (cf (j m)).continuousOn).frequently,?_⟩
  intro t ht
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (vuni.mono Ioo_subset_Icc_self)
    (Eventually.of_forall fun i t _ => df (j i) t) (fun t ht => pt t (Ioo_subset_Icc_self ht)) ht

end MigrationGeometry.HullGap
#print axioms MigrationGeometry.HullGap.compact_trajectory
