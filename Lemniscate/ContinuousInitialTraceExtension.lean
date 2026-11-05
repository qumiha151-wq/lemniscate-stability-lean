import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UnitInterval

/-! Glue the existing positive-time path to the existing closed initial
interval through an injective value map. No higher norm is assumed small. -/
noncomputable section
namespace Lemniscate
open Set Filter
open scoped Topology

/-- Matching weak values identify the overlapping strong representatives.
The resulting path is continuous up to the initial endpoint and retains
the original positive-time representatives. -/
theorem continuous_initial_trace_extension
    {E F : Type*} [TopologicalSpace E]
    (L : E → F) (hL : Function.Injective L)
    (b : ℝ → F) (τ : ℝ) (hτ : 0 < τ)
    (w : C(Ioi (0:ℝ),E)) (W : C(unitInterval,E))
    (hp : ∀ t : Ioi (0:ℝ), L (w t) = b t)
    (hi : ∀ r : unitInterval, L (W r) = b (τ*(r:ℝ))) :
    ∃ v : ℝ → E,
      ContinuousOn v (Ici (0:ℝ)) ∧
      (∀ t ∈ Ici (0:ℝ), L (v t) = b t) ∧
      v 0 = W 0 ∧
      ∀ t (ht : 0<t), v t = w ⟨t,ht⟩ := by
  classical
  let v (t : ℝ) : E := if ht : 0<t then w ⟨t,ht⟩ else W 0
  let V (t : ℝ) : E := W (Set.projIcc (0:ℝ) 1 zero_le_one (t/τ))
  have hV : Continuous V :=
    W.continuous.comp (continuous_projIcc.comp (continuous_id.div_const τ))
  have hpositive (t : ℝ) (ht : 0<t) : v t = w ⟨t,ht⟩ := by
    simp only [v,dif_pos ht]
  have hzero : v 0 = W 0 := by
    dsimp only [v]
    rw [dif_neg (lt_irrefl (0:ℝ))]
  have hoverlap (t : ℝ) (ht : 0≤t) (htτ : t≤τ) : v t = V t := by
    by_cases ht0 : 0<t
    · have hr : t/τ ∈ Icc (0:ℝ) 1 :=
        ⟨div_nonneg ht hτ.le,(div_le_one hτ).mpr htτ⟩
      let r : unitInterval := ⟨t/τ,hr⟩
      have hclock : τ*(r:ℝ) = t := by
        dsimp only [r]
        exact mul_div_cancel₀ t hτ.ne'
      have heq : L (w ⟨t,ht0⟩) = L (W r) := by
        rw [hp,hi,hclock]
      rw [hpositive t ht0]
      have hh := hL heq
      change w ⟨t,ht0⟩ = W (Set.projIcc (0:ℝ) 1 zero_le_one (t/τ))
      rw [Set.projIcc_of_mem zero_le_one hr]
      exact hh
    · have htzero : t=0 := le_antisymm (not_lt.mp ht0) ht
      subst t
      rw [hzero]
      dsimp only [V]
      rw [zero_div,Set.projIcc_of_mem zero_le_one (show (0:ℝ)∈Icc 0 1 from ⟨le_rfl,zero_le_one⟩)]
      rfl
  have hpcont : ContinuousOn v (Ioi (0:ℝ)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : Ioi (0:ℝ) => v (t:ℝ))
    have heq : (fun t : Ioi (0:ℝ) => v (t:ℝ)) = w := by
      funext t
      exact hpositive t t.property
    rw [heq]
    exact w.continuous
  have hv : ContinuousOn v (Ici (0:ℝ)) := by
    intro t ht
    by_cases ht0 : 0<t
    · exact (hpcont.continuousAt (isOpen_Ioi.mem_nhds ht0)).continuousWithinAt
    · have htzero : t=0 := le_antisymm (not_lt.mp ht0) (mem_Ici.mp ht)
      subst t
      have heq : v =ᶠ[𝓝[Ici (0:ℝ)] 0] V := by
        filter_upwards [Icc_mem_nhdsGE hτ] with s hs
        exact hoverlap s hs.1 hs.2
      exact hV.continuousWithinAt.congr_of_eventuallyEq_of_mem heq (mem_Ici.mpr (le_refl (0:ℝ)))
  refine ⟨v,hv,?_,hzero,hpositive⟩
  intro t ht
  by_cases ht0 : 0<t
  · rw [hpositive t ht0]
    exact hp ⟨t,ht0⟩
  · have htzero : t=0 := le_antisymm (not_lt.mp ht0) (mem_Ici.mp ht)
    subst t
    rw [hzero]
    have hztime : ((0:unitInterval):ℝ) = 0 := rfl
    simpa only [hztime,mul_zero] using hi 0

end Lemniscate
