import LengthGrowth.ActualFlow.InflectionVelocitySeparation
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section
open Set Function
namespace LengthGrowth.ActualFlow.TurningEnvelope

variable {X K : Type*} [TopologicalSpace X] [TopologicalSpace K] [CompactSpace K]

def rateValues (Z : Set (X×K)) (v : X×K→ℝ) (t : X) : Set ℝ :=
  insert 0 ((fun p => v (t,p)) '' {p | (t,p)∈Z})

def closedGraphRate (Z : Set (X×K)) (v : X×K→ℝ) (t : X) := sSup (rateValues Z v t)

theorem compact_rateValues {Z : Set (X×K)} (z : IsClosed Z) {v : X×K→ℝ} (c : Continuous v) (t : X) :
    IsCompact (rateValues Z v t) := by
  have emb : Continuous (fun p : K => (t,p)) := continuous_const.prodMk continuous_id
  have closed : IsClosed {p | (t,p)∈Z} := z.preimage emb
  exact (closed.isCompact.image (c.comp emb)).insert 0

theorem closedGraphRate_nonneg {Z : Set (X×K)} (z : IsClosed Z) {v : X×K→ℝ} (c : Continuous v) (t : X) :
    0≤closedGraphRate Z v t := le_csSup (compact_rateValues z c t).bddAbove (mem_insert ..)

theorem le_closedGraphRate {Z : Set (X×K)} (z : IsClosed Z) {v : X×K→ℝ} (c : Continuous v) {t : X} {p : K}
    (h : (t,p)∈Z) : v (t,p)≤closedGraphRate Z v t :=
  le_csSup (compact_rateValues z c t).bddAbove (mem_insert_of_mem _ (mem_image_of_mem _ h))

theorem upperSemicontinuous_closedGraphRate {Z : Set (X×K)} (z : IsClosed Z) {v : X×K→ℝ} (c : Continuous v) :
    UpperSemicontinuous (closedGraphRate Z v) := by
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro q
  by_cases small : q≤0
  · rw [show (closedGraphRate Z v) ⁻¹' Ici q = univ by
          ext t
          exact ⟨fun _=>mem_univ _,fun _=>small.trans (closedGraphRate_nonneg z c t)⟩]
    exact isClosed_univ
  · have eq : (closedGraphRate Z v) ⁻¹' Ici q=Prod.fst '' (Z ∩ (v ⁻¹' Ici q)) := by
      ext t
      constructor
      · intro h
        have sat := (compact_rateValues z c t).sSup_mem (show (rateValues Z v t).Nonempty from ⟨0,mem_insert ..⟩)
        rcases sat with zero|val
        · exact (small (h.trans_eq zero)).elim
        · obtain ⟨p,hp,att⟩:=val
          exact ⟨(t,p),⟨hp,h.trans_eq att.symm⟩,rfl⟩
      · rintro ⟨⟨w,p⟩,⟨hp,hq⟩,rfl⟩
        exact hq.trans (le_closedGraphRate z c hp)
    rw [eq]
    exact isClosedMap_fst_of_compactSpace _ (z.inter (isClosed_Ici.preimage c))

end LengthGrowth.ActualFlow.TurningEnvelope
#print axioms LengthGrowth.ActualFlow.TurningEnvelope.upperSemicontinuous_closedGraphRate
