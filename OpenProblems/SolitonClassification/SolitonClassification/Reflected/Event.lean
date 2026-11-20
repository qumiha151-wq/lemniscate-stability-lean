import SolitonClassification.Reflected.Trace
import Mathlib.Topology.Order.IntermediateValue

namespace SolitonClassification.Reflected
open Set

/-- A continuous family of uniformly transverse first-component crossings
defines an event time. Signs of the second component are needed only on
the two endpoint trajectories. -/
theorem event_rectangle {b₀ b₁ m τ d : ℝ} (hb : b₀≤b₁) (hm : 0<m) (hd : 0<d)
    (V Q : ℝ×ℝ → ℝ)
    (hv : ContinuousOn V (Icc b₀ b₁ ×ˢ Icc (τ-d) (τ+d)))
    (hq : ContinuousOn Q (Icc b₀ b₁ ×ˢ Icc (τ-d) (τ+d)))
    (hinc : ∀b∈Icc b₀ b₁, ∀x∈Icc (τ-d) (τ+d), ∀y∈Icc (τ-d) (τ+d),
      x≤y → m*(y-x)≤V (b,y)-V (b,x))
    (hmid : ∀b∈Icc b₀ b₁, |V (b,τ)|≤m*d)
    (hleft : ∀t∈Icc (τ-d) (τ+d), V (b₀,t)=0 → Q (b₀,t)≤0)
    (hright : ∀t∈Icc (τ-d) (τ+d), V (b₁,t)=0 → 0≤Q (b₁,t)) :
    ∃b∈Icc b₀ b₁, ∃t∈Icc (τ-d) (τ+d), V (b,t)=0 ∧ Q (b,t)=0 := by
  let B := Icc b₀ b₁
  let I := Icc (τ-d) (τ+d)
  have hl : τ-d∈I := ⟨le_rfl,by linarith⟩
  have hr : τ+d∈I := ⟨by linarith,le_rfl⟩
  have hc : τ∈I := ⟨by linarith,by linarith⟩
  have hex (b:ℝ) (hb':b∈B) : ∃t∈I, V (b,t)=0 := by
    have hcont : ContinuousOn (fun t => V (b,t)) I :=
      hv.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hb',ht⟩)
    apply intermediate_value_Icc hl.2 hcont
    have h1:=hinc b hb' _ hl _ hc hc.1
    have h2:=hinc b hb' _ hc _ hr hc.2
    have h3:=abs_le.mp (hmid b hb')
    constructor <;> nlinarith
  classical
  let T : ℝ → ℝ := fun b => if hh:b∈B then (hex b hh).choose else τ
  have hT (b:ℝ) (hb':b∈B) : T b∈I ∧ V (b,T b)=0 := by
    simpa only [T,dif_pos hb'] using (hex b hb').choose_spec
  have hdiff (b c:ℝ) (hb':b∈B) (hc':c∈B) : m*|T c-T b|≤|V (c,T b)| := by
    by_cases h:T b≤T c
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      have h1:=hinc c hc' _ (hT b hb').1 _ (hT c hc').1 h
      rw [(hT c hc').2,zero_sub] at h1
      exact h1.trans (neg_le_abs _)
    · have h' : T c≤T b := le_of_not_ge h
      rw [abs_of_nonpos (sub_nonpos.mpr h')]
      have h1:=hinc c hc' _ (hT c hc').1 _ (hT b hb').1 h'
      rw [(hT c hc').2,sub_zero] at h1
      linarith [le_abs_self (V (c,T b))]
  have hct : ContinuousOn T B := by
    intro b hb'
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hslice : ContinuousOn (fun c => V (c,T b)) B :=
      hv.comp (continuousOn_id.prodMk continuousOn_const) (fun _ h => ⟨h,(hT b hb').1⟩)
    obtain ⟨δ,hδ,he⟩ := Metric.continuousWithinAt_iff.mp (hslice b hb') (m*ε) (mul_pos hm hε)
    refine ⟨δ,hδ,fun c hc' hdist => ?_⟩
    have hn:=he hc' hdist
    simp only [Real.dist_eq,(hT b hb').2,sub_zero] at hn
    rw [Real.dist_eq]
    nlinarith [hdiff b c hb' hc']
  have hQ : ContinuousOn (fun b => Q (b,T b)) B :=
    hq.comp (continuousOn_id.prodMk hct) (fun b h => ⟨h,(hT b h).1⟩)
  have h0 : b₀∈B := ⟨le_rfl,hb⟩
  have h1 : b₁∈B := ⟨hb,le_rfl⟩
  obtain ⟨b,hb',hz⟩ := intermediate_value_Icc hb hQ
    (show 0∈Icc (Q (b₀,T b₀)) (Q (b₁,T b₁)) from
      ⟨hleft _ (hT b₀ h0).1 (hT b₀ h0).2,hright _ (hT b₁ h1).1 (hT b₁ h1).2⟩)
  exact ⟨b,hb',T b,(hT b hb').1,(hT b hb').2,hz⟩

end SolitonClassification.Reflected
#print axioms SolitonClassification.Reflected.event_rectangle
