import SolitonClassification.CentreCriticalLayer

noncomputable section
open Set
namespace ClosedSimilarity.OuterStress

/-- A segmentwise bound with no initial impact assumption. In particular its
    admissible layer threshold is independent of an intermediate stress radius. -/
theorem segment_amplitude_drop (M α : ℝ) (pa : 0<α) :
    ∃ L≥1, ∀ {δ S T : ℝ} {r U w a b : ℝ → ℝ}, S≤T →
      (∀x ∈ Icc S T, Rates δ x r U w a b ∧ r x^2≤2 ∧ |a x|≤M ∧ |b x|≤M ∧
        α≤a x ∧ L*δ≤r x^3) →
      15*(r T)^2/16 + (α/3)*(T-S) ≤ 17*(r S)^2/16 := by
  obtain ⟨D,hD,bd⟩ := outer_budget M
  have Dpos : 0<D := by linarith
  let L := max (16*D) (3*D/α)
  have hL : 1≤L := (by linarith : 1≤16*D).trans (le_max_left ..)
  refine ⟨L,hL,?_⟩
  intro δ S T r U w a b st data
  let H := amplitude δ r U w a b
  have xS : S∈Icc S T := left_mem_Icc.mpr st
  have xT : T∈Icc S T := right_mem_Icc.mpr st
  have δp := (data S xS).1.delta_pos
  have est (x : ℝ) (hx : x∈Icc S T) : 15*r x^2/16≤H x ∧ H x≤17*r x^2/16 ∧
      deriv H x≤-α/3 := by
    obtain ⟨rates,cap,al,ac,align,above⟩ := data x hx
    obtain ⟨_,h,mag,_⟩ := bd rates cap al ac
    have p := rates.pos
    have A := (mul_le_mul_of_nonneg_right (le_max_left (16*D) (3*D/α)) δp.le).trans above
    have B := (mul_le_mul_of_nonneg_right (le_max_right (16*D) (3*D/α)) δp.le).trans above
    have by16 : D*δ/r x ≤ r x^2/16 := (div_le_iff₀ p).mpr (by linarith)
    have by3 : D*δ/r x^3 ≤ α/3 := (div_le_iff₀ (pow_pos p _)).mpr (by
      rw [div_mul_eq_mul_div] at B
      linarith [(div_le_iff₀ pa).mp B])
    change |H x-r x^2|≤_ at mag
    change |deriv H x+2*a x/3|≤_ at h
    exact ⟨by linarith [(abs_le.mp mag).1],by linarith [(abs_le.mp mag).2],
      by linarith [(abs_le.mp h).2]⟩
  let f := fun x => H x + (α/3)*x
  have df (x : ℝ) (hx : x∈Icc S T) : HasDerivAt f (deriv H x+α/3) x := by
    have d := (amplitude_rate (data x hx).1).differentiableAt
    convert! d.hasDerivAt.add ((hasDerivAt_id x).const_mul (α/3)) using 1
    ring
  have dec : AntitoneOn f (Icc S T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun x hx => (df x hx).continuousAt.continuousWithinAt)
      (fun x hx => (df x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(df x (interior_subset hx)).deriv]
    linarith [(est x (interior_subset hx)).2.2]
  have order := dec xS xT st
  change H T+(α/3)*T ≤ H S+(α/3)*S at order
  linarith [(est T xT).1,(est S xS).2.1]

end ClosedSimilarity.OuterStress
#print axioms ClosedSimilarity.OuterStress.segment_amplitude_drop
