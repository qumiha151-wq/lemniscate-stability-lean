import LengthGrowth.ActualFlow.TangentTail
import LengthGrowth.ActualFlow.TangentFlowRecord
namespace LengthGrowth.ActualFlow.ForwardImmersion
noncomputable section
open Set Real MeasureTheory TangentSpectrum
variable (c : ForwardImmersion)

/-- The spectral tail of the actual normalized arclength unit tangent at time t. -/
def tangentTail {t : ℝ} (ht : 0≤t) (W : ℝ) (positive : Bool) :=
  tail W positive (c.regularPositionAt ht).closedFrenetCurve.unitT

/-- At one arbitrarily late record on an unbounded product trajectory, both
frequency half-lines simultaneously carry a fixed H^(1/4) squared mass beyond
any prescribed angular frequency. -/
theorem two_tangent_tails_escape_of_failure (hf : c.IsNormalFEF) (fail : ¬c.HasQuarterLengthBound)
    (W A t₀ : ℝ) : ∃t,∃ht : 0<t, t₀<t ∧ A<c.normalizedProduct t ∧
    (∀s∈Icc 0 t,c.normalizedProduct s≤c.normalizedProduct t) ∧
    ∀positive : Bool,3/2048≤c.tangentTail ht.le W positive := by
  let S:=materialSignedCurvature (c.position 0) c.period
  let B:=max (128*W) (64*|S|)
  have bp : 0≤B := (mul_nonneg (by norm_num) (abs_nonneg S)).trans (le_max_right _ _)
  obtain ⟨t,late,ht,large,rec,_⟩:=c.high_record_cubic_half_of_failure hf fail (max A (B^3)) t₀
  let U:=c.normalizedProduct t
  have up : 0<U:=mul_pos (c.energy_pos ht.le) (c.length_pos ht.le)
  let X:=U^(1/3:ℝ)
  have xp : 0<X:=Real.rpow_pos_of_pos up _
  have xs : X^3=U := by
    dsimp only [X]
    rw [←Real.rpow_natCast,←Real.rpow_mul up.le]
    norm_num
  have bl : B<X := by
    by_contra! h
    have hp:=pow_le_pow_left₀ xp.le h 3
    rw [xs] at hp
    exact (not_le_of_gt ((le_max_right A (B^3)).trans_lt large)) hp
  have cutoff : W≤X/128 := by linarith only [(le_max_left (128*W) (64*|S|)).trans_lt bl]
  have small : |S|≤X/64 := by linarith only [(le_max_right (128*W) (64*|S|)).trans_lt bl]
  obtain ⟨sg,two,M,four,cap⟩:=c.signed_fourier_at_record hf ht xp xs rec
  let a:=(c.regularPositionAt ht.le).closedFrenetCurve
  have cc : Continuous a.unitT := continuous_iff_continuousAt.mpr fun u=>(a.unitT_der u).continuousAt
  have norm (u : ℝ) : ‖a.unitT u‖=1 := a.tangent_unit _
  have zero : HasSum (TangentSpectrum.energy a.unitT) 1 := by simpa only [norm,one_pow,intervalIntegral.integral_const,sub_zero,one_smul] using (parseval a.unitT cc)
  exact ⟨t,ht,late,(le_max_left _ _).trans_lt large,rec,fun pos=>tail_escape xp cutoff small zero sg two four cap pos⟩

/-- A uniform small high-frequency tail of either sign implies the quarter
length bound. The chosen sign may even vary with time. -/
theorem quarter_growth_of_one_small_tangent_tail (hf : c.IsNormalFEF) {W A t₀ : ℝ}
    (small : ∀t,∀ht : 0<t,t₀<t → A<c.normalizedProduct t →
      ∃positive : Bool,c.tangentTail ht.le W positive<3/2048) : c.HasQuarterLengthBound := by
  by_contra fail
  obtain ⟨t,ht,late,large,_,both⟩:=c.two_tangent_tails_escape_of_failure hf fail W A t₀
  obtain ⟨side,h⟩:=small t ht late large
  exact (not_lt_of_ge (both side)) h
end
end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.two_tangent_tails_escape_of_failure
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_growth_of_one_small_tangent_tail
