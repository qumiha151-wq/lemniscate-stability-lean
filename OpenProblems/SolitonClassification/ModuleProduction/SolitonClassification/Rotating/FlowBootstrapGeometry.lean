module

public import SolitonClassification.Rotating.FlowMetricCoordinates
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! Geometry used before any actual-flow tube assumption. The generic
first-threshold argument is copied/adapted from the independent proof in
work/centroid_formal/MetricBootstrap.lean (exists_first_threshold), with
no import from that project or use of its field-specific estimates. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

def outerTubeMargin (a : State) (d : ℝ) : Prop :=
  |a 0|+d≤17/2 ∧ |a 1|+d≤9/2 ∧ |a 2|+d≤17/2 ∧
    |a 3|+d≤17/2 ∧ |a 4|+d≤1/50

theorem outerTube_of_margin {a b : State} {d : ℝ}
    (ha : outerTubeMargin a d) (hab : ‖b-a‖≤d) : b∈outerTube := by
  have hb (i : Fin 6) : |b i|≤|a i|+d := by
    have hi := (coordinate_bound (b-a) i).trans hab
    have hs := abs_add_le (b i-a i) (a i)
    rw [sub_add_cancel] at hs
    change |b i-a i|≤d at hi
    linarith
  exact ⟨(hb 0).trans ha.1,(hb 1).trans ha.2.1,(hb 2).trans ha.2.2.1,
    (hb 3).trans ha.2.2.2.1,(hb 4).trans ha.2.2.2.2⟩

theorem field_quadratic_remainder_identity (a b : State) :
    field b-field a-fderiv ℝ field a (b-a)=
      bilinear ((2/3:ℝ) • a+(1/3:ℝ) • b) (b-a) (b-a) := by
  rw [field_fderiv_apply]
  ext i
  fin_cases i <;> simp [field,linear,bilinear,smul_eq_mul] <;> ring

theorem field_quadratic_remainder_bound {a b : State}
    (ha : a∈outerTube) (hb : b∈outerTube) :
    ‖field b-field a-fderiv ℝ field a (b-a)‖≤2*‖b-a‖^2 := by
  have hc : (2/3:ℝ) • a+(1/3:ℝ) • b∈outerTube :=
    outerTube_convex ha hb (by norm_num) (by norm_num) (by norm_num)
  rw [field_quadratic_remainder_identity]
  exact (bilinear_bound hc (b-a) (b-a)).trans_eq (by ring)

theorem bootstrap_exists_first_threshold {W : ℝ → ℝ} {l r c : ℝ}
    (hc : ContinuousOn W (Icc l r)) (hbad : ∃t∈Icc l r,c≤W t) :
    ∃s∈Icc l r,c≤W s ∧ ∀t∈Ico l s,W t<c := by
  let S : Set ℝ := Icc l r ∩ W ⁻¹' Ici c
  have hclosed : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed (fun _ h => h.1)
  have hne : S.Nonempty := by
    rcases hbad with ⟨t,ht,hc⟩
    exact ⟨t,ht,hc⟩
  obtain ⟨s,hs,hmin⟩ := hcompact.exists_isMinOn hne continuousOn_id
  refine ⟨s,hs.1,hs.2,?_⟩
  intro t ht
  by_contra hnot
  have htS : t∈S := ⟨⟨ht.1,ht.2.le.trans hs.1.2⟩,le_of_not_gt hnot⟩
  have hst : s≤t := hmin htS
  linarith [ht.2]

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating state-bootstrap geometry audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating state-bootstrap geometry audit passed for {count} declarations."

end
