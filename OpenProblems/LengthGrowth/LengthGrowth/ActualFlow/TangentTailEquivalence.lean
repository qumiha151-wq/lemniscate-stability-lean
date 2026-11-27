import LengthGrowth.ActualFlow.TangentQuarterGrowth
import LengthGrowth.ActualFlow.TangentUpperTail
namespace LengthGrowth.ActualFlow.ForwardImmersion
noncomputable section
variable (c : ForwardImmersion)

/-- The one-sided small-tail criterion is equivalent to the uniform vanishing of
both critical Fourier tails over the entire given smooth flow. -/
theorem tangent_tail_characterization (hf : c.IsNormalFEF) :
    (c.HasQuarterLengthBound ↔
      ∀ε:ℝ,0<ε → ∃W:ℝ,1≤W ∧ ∀t,∀ht:0≤t,∀side:Bool,c.tangentTail ht W side<ε) ∧
    (c.HasQuarterLengthBound ↔
      ∃W A t₀:ℝ,∀t,∀ht : 0<t,t₀<t → A<c.normalizedProduct t →
        ∃side : Bool,c.tangentTail ht.le W side<3/2048) := by
  have uniform (h : c.HasQuarterLengthBound) (ε : ℝ) (ep : 0<ε) :
      ∃W:ℝ,1≤W ∧ ∀t,∀ht:0≤t,∀side:Bool,c.tangentTail ht W side<ε := by
    obtain ⟨K,bound⟩:=(c.quarter_length_iff_bounded_energyLength hf).mp h
    have kn : 0≤K := (mul_nonneg (c.energy_nonneg 0) (c.length_nonneg 0)).trans (bound 0 le_rfl)
    let W:=1+2*K/ε
    have w1 : 1≤W := by dsimp only [W];linarith only [div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) kn) ep.le]
    have wp : 0<W := zero_lt_one.trans_le w1
    refine ⟨W,w1,?_⟩
    intro t ht side
    apply (c.one_tail_upper ht w1 side).trans_lt
    apply (div_lt_iff₀ wp).mpr
    have id : ε*W=ε+2*K := by dsimp only [W];field_simp [ep.ne']
    rw [id]
    change 2*(c.energy t*c.length t)<_
    linarith only [bound t ht,ep]
  have select (u : ∀ε:ℝ,0<ε → ∃W:ℝ,1≤W ∧ ∀t,∀ht:0≤t,∀side:Bool,c.tangentTail ht W side<ε) :
      ∃W A t₀:ℝ,∀t,∀ht : 0<t,t₀<t → A<c.normalizedProduct t →
        ∃side : Bool,c.tangentTail ht.le W side<3/2048 := by
    obtain ⟨W,_,all⟩:=u (3/2048) (by norm_num)
    exact ⟨W,0,0,fun t ht _ _=>⟨true,all t ht.le true⟩⟩
  have close (s : ∃W A t₀:ℝ,∀t,∀ht : 0<t,t₀<t → A<c.normalizedProduct t →
        ∃side : Bool,c.tangentTail ht.le W side<3/2048) : c.HasQuarterLengthBound := by
    obtain ⟨W,A,t₀,h⟩:=s
    exact c.quarter_growth_of_one_small_tangent_tail hf h
  exact ⟨⟨uniform,fun u=>close (select u)⟩,⟨fun h=>select (uniform h),close⟩⟩
end
end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.tangent_tail_characterization
