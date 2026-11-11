import CentroidEscape.Reversibility
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Global periodic solution from an exact closed ODE segment

This file constructs a globally defined periodic solution by reduction modulo
the positive period. It proves the differential equation at every real time,
including the joins, then derives global smoothness from ODE regularity.
The half-orbit and its exact shooting equalities remain explicit inputs.
-/

namespace CentroidEscape

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

def periodize (f : ℝ → State) {T : ℝ} (hT : 0 < T) (t : ℝ) : State :=
  f (toIcoMod hT 0 t)

lemma periodize_periodic (f : ℝ → State) {T : ℝ} (hT : 0 < T) :
    Function.Periodic (periodize f hT) T := by
  intro t
  simp [periodize, toIcoMod_add_right]

lemma periodize_sub_zsmul (f : ℝ → State) {T : ℝ} (hT : 0 < T) (t : ℝ) (n : ℤ) :
    periodize f hT (t - n • T) = periodize f hT t := by
  simp [periodize]

lemma periodize_eq {f : ℝ → State} {T : ℝ} (hT : 0 < T) (hend : f 0 = f T)
    {t : ℝ} (ht : t ∈ Icc 0 T) : periodize f hT t = f t := by
  by_cases heq : t = T
  · subst t
    change f (toIcoMod hT 0 T) = f T
    rw [show toIcoMod hT 0 T = 0 by
      simpa only [zero_add] using toIcoMod_apply_right hT 0]
    exact hend
  · have hlt : t < T := lt_of_le_of_ne ht.2 heq
    rw [periodize, (toIcoMod_eq_self hT).2 (by simpa using And.intro ht.1 hlt)]

/-- Differentiability at the joining point uses both endpoint derivatives. -/
lemma periodize_derivative_zero {f : ℝ → State} {T : ℝ} (hT : 0 < T)
    (hend : f 0 = f T)
    (h0 : HasDerivAt f (field (f 0)) 0)
    (h1 : HasDerivAt f (field (f T)) T) :
    HasDerivAt (periodize f hT) (field (periodize f hT 0)) 0 := by
  have heq0 : periodize f hT 0 = f 0 := periodize_eq hT hend ⟨le_rfl, hT.le⟩
  have hr : HasDerivWithinAt (periodize f hT) (field (f 0)) (Ici 0) 0 := by
    apply h0.hasDerivWithinAt.congr_of_eventuallyEq _ heq0
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with s hs hsT
    exact periodize_eq hT hend ⟨hs, hsT.le⟩
  have hshift : HasDerivAt (fun s : ℝ => f (s + T)) (field (f 0)) 0 := by
    have hd : HasDerivAt (fun s : ℝ => s + T) 1 0 := (hasDerivAt_id 0).add_const T
    have h1' : HasDerivAt f (field (f 0)) (0 + T) := by simpa [hend] using h1
    convert! h1'.scomp 0 hd using 1
    simp
  have hl : HasDerivWithinAt (periodize f hT) (field (f 0)) (Iic 0) 0 := by
    apply hshift.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show -T < (0:ℝ) by linarith)).filter_mono nhdsWithin_le_nhds]
        with s hs hsT
      rw [← periodize_periodic f hT s]
      exact periodize_eq hT hend ⟨by linarith, by linarith [Set.mem_Iic.mp hs]⟩
    · simpa [heq0] using hend
  have hh := hl.union hr
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at hh
  simpa [heq0] using hh

lemma periodize_derivative_Ico {f : ℝ → State} {T : ℝ} (hT : 0 < T)
    (hend : f 0 = f T)
    (hf : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt f (field (f t)) t)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivAt (periodize f hT) (field (periodize f hT t)) t := by
  by_cases ht0 : t = 0
  · subst t
    exact periodize_derivative_zero hT hend (hf 0 ⟨le_rfl, hT.le⟩) (hf T ⟨hT.le, le_rfl⟩)
  · have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have heq : periodize f hT =ᶠ[𝓝 t] f := by
      filter_upwards [eventually_gt_nhds hpos, eventually_lt_nhds ht.2] with s hs0 hsT
      exact periodize_eq hT hend ⟨hs0.le, hsT.le⟩
    have hd := (hf t ⟨ht.1, ht.2.le⟩).congr_of_eventuallyEq heq
    simpa [periodize_eq hT hend ⟨ht.1, ht.2.le⟩] using hd

theorem periodize_solves {f : ℝ → State} {T : ℝ} (hT : 0 < T)
    (hend : f 0 = f T)
    (hf : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt f (field (f t)) t) (t : ℝ) :
    HasDerivAt (periodize f hT) (field (periodize f hT t)) t := by
  let n := toIcoDiv hT 0 t
  have hm : t - n • T = toIcoMod hT 0 t := self_sub_toIcoDiv_zsmul hT 0 t
  have hmem : t - n • T ∈ Ico (0:ℝ) T := by
    rw [hm]
    exact toIcoMod_mem_Ico' hT t
  have hd := periodize_derivative_Ico hT hend hf hmem
  have hc : HasDerivAt (fun s : ℝ => s - n • T) 1 t := (hasDerivAt_id t).sub_const _
  have hh := hd.scomp t hc
  simpa only [Function.comp_def, one_smul, periodize_sub_zsmul] using hh

theorem periodize_smooth {f : ℝ → State} {T : ℝ} (hT : 0 < T)
    (hend : f 0 = f T)
    (hf : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt f (field (f t)) t) :
    ContDiff ℝ (⊤ : ℕ∞) (periodize f hT) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (periodize f hT) (Icc (t-1) (t+1)) := by
    apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := fun (_ : ℝ) z => field z) (u := univ)
    · exact ((field_smooth ⊤).comp contDiff_snd).contDiffOn
    · intro s hs
      exact (periodize_solves hT hend hf s).hasDerivWithinAt
    · intro s hs
      exact mem_univ _
  exact hd.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))

/-- Exact half-orbit data yield a global smooth periodic unit-speed state. -/
theorem exists_global_periodic_orbit {z : ℝ → State} {L : ℝ} (hL : 0 < L)
    (hz : ∀ t ∈ Icc (0:ℝ) L, HasDerivAt z (field (z t)) t)
    (h0 : reverseState (z 0) = z 0) (hLfix : reverseState (z L) = z L)
    (hu : z 0 2 = 0) (hw : z 0 3 = 1) :
    ∃ q : ℝ → State,
      Function.Periodic q (2*L) ∧ ContDiff ℝ (⊤ : ℕ∞) q ∧
      (∀ t, HasDerivAt q (field (q t)) t) ∧
      (∀ t ∈ Icc (0:ℝ) L, q t = z t) ∧
      (∀ t, tangentSquare (q t) = 1) := by
  have hT : 0 < 2*L := by linarith
  have he : doubled z L 0 = doubled z L (2*L) := by
    rw [doubled_at_zero hL.le, doubled_at_end hL h0]
  have hf : ∀ t ∈ Icc (0:ℝ) (2*L),
      HasDerivAt (doubled z L) (field (doubled z L t)) t :=
    fun t ht => doubled_solves hz hLfix ht
  refine ⟨periodize (doubled z L) hT, periodize_periodic _ hT,
    periodize_smooth hT he hf, periodize_solves hT he hf, ?_, ?_⟩
  · intro t ht
    rw [periodize_eq hT he ⟨ht.1, by linarith [ht.2]⟩]
    simp [doubled, ht.2]
  · intro t
    unfold periodize
    exact doubled_unit_tangent hL.le hz hLfix hu hw
      (Ico_subset_Icc_self (toIcoMod_mem_Ico' hT t))

end
end CentroidEscape

#print axioms CentroidEscape.exists_global_periodic_orbit

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Centroid periodic-orbit audit passed for {checked} declarations."
