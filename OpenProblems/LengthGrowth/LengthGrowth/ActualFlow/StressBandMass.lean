import LengthGrowth.ActualFlow.PhysicalStressMass

noncomputable section
open MeasureTheory Set

namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- Sampling mass of finitely many bands, with squared curvature-scale weight. -/
def stressBandMass {ι : Type*} (I : Finset ι) (H : ι → ℝ) (S : ι → Set ℝ) : ℝ :=
  ∑ i ∈ I, ∫s in 0..c.period, (S i).indicator (fun _ => H i^2) s

/-- A disjoint measurable family with lower stress thresholds may be estimated
simultaneously, with a bound independent of the number or spacing of the bands. -/
theorem stressBandMass_le_stressMass {ι : Type*} (I : Finset ι) (H : ι → ℝ) (S : ι → Set ℝ)
    (hm : ∀ i ∈ I, MeasurableSet (S i))
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (hs : ∀ i ∈ I, ∀ s ∈ S i, H i^2 ≤ ‖c.stress s‖) :
    c.stressBandMass I H S ≤ c.stressMass := by
  classical
  let f (i : ι) := (S i).indicator (fun _ => H i^2)
  have hi (i) (h : i ∈ I) : IntervalIntegrable (f i) volume 0 c.period := by
    apply intervalIntegrable_iff.mpr
    exact (intervalIntegrable_iff.mp (intervalIntegrable_const (a:=0) (b:=c.period)
      (c:=H i^2) (μ:=volume))).indicator (hm i h)
  have sumint : IntervalIntegrable (fun s => ∑ i ∈ I, f i s) volume 0 c.period := by
    apply intervalIntegrable_iff.mpr
    exact integrable_finsetSum I (fun i h => intervalIntegrable_iff.mp (hi i h))
  unfold stressBandMass stressMass
  change (∑ i ∈ I, ∫s in 0..c.period, f i s) ≤ _
  rw [←intervalIntegral.integral_finsetSum hi]
  apply intervalIntegral.integral_mono_on c.period_pos.le sumint (c.stress_continuous.norm.intervalIntegrable _ _)
  intro s _
  by_cases e : ∃ i ∈ I, s ∈ S i
  · obtain ⟨i,hiI,hsi⟩ := e
    rw [Finset.sum_eq_single_of_mem i hiI]
    · simpa [f, hsi] using hs i hiI s hsi
    · intro j hj hji
      have hsj : s ∉ S j := fun h => Set.disjoint_left.mp (hd j hj i hiI hji) h hsi
      simp [f, hsj]
  · rw [Finset.sum_eq_zero (fun i hiI => by
      have hsi : s ∉ S i := fun h => e ⟨i, hiI, h⟩
      simp [f, hsi])]
    exact norm_nonneg _

end LengthGrowth.ClosedFrenetCurve

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

theorem physicalStressBandMass_excess_cube {ι : Type*} {t : ℝ} (ht : 0 ≤ t)
    (I : Finset ι) (H : ι → ℝ) (S : ι → Set ℝ)
    (hm : ∀ i ∈ I, MeasurableSet (S i))
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (hs : ∀ i ∈ I, ∀ s ∈ S i,
      H i^2 ≤ ‖(c.regularPositionAt ht).closedFrenetCurve.stress s‖) :
    let p := (c.regularPositionAt ht).closedFrenetCurve
    4*(max 0 (p.stressBandMass I H S-3*c.energy t))^3 ≤ 27*(c.length t)^2*c.dissipation t := by
  let p := (c.regularPositionAt ht).closedFrenetCurve
  have h := p.stressBandMass_le_stressMass I H S hm hd hs
  apply le_trans _ (c.physicalStressMass_excess_cube ht)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply pow_le_pow_left₀ (le_max_left ..)
  exact max_le_max_left _ (sub_le_sub_right h _)

end LengthGrowth.ActualFlow.ForwardImmersion

#print axioms LengthGrowth.ClosedFrenetCurve.stressBandMass_le_stressMass
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.physicalStressBandMass_excess_cube
