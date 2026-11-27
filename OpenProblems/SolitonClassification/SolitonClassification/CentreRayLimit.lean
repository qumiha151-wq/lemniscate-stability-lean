import SolitonClassification.CentreRayOrientation

noncomputable section
open Set MeasureTheory
namespace ClosedSimilarity.OuterStress.Data
variable {δ : ℝ}

def laboratoryAngle (z : Data δ) (s : ℝ) := ∫u in 0..s, z.K u/δ

theorem laboratoryAngle_rate (z : Data δ) (s : ℝ) :
    HasDerivAt z.laboratoryAngle (z.K s/δ) s := by
  have c : Continuous (fun u => z.K u/δ) :=
    (continuous_iff_continuousAt.mpr (fun u => (z.dK u).continuousAt)).div_const _
  exact intervalIntegral.integral_hasDerivAt_right (c.intervalIntegrable 0 s)
    c.aestronglyMeasurable.stronglyMeasurableAtFilter c.continuousAt

/-- On every high-marker centre shot, all outer positions from slow time 1/2 up
to the certified critical layer lie in an arbitrarily thin neighbourhood of
the positive laboratory vertical half-line at height at least 1/2400. -/
theorem central_shot_positive_ray :
    ∃ L₀≥1, ∃ C≥1, ∀ L≥L₀, ∀ ε>0, ∃ d>0, ∀ {δ : ℝ} (z : Data δ), 0<δ → δ≤d →
      z.K 0=0 → z.V 0=1 → z.p 0=0 → z.q 0=0 →
      ∃ T∈Icc (1/2:ℝ) 10000, z.root T^3=L*δ ∧ CriticalStrip z L C T ∧
        ∀ t∈Icc (1/2:ℝ) T, |z.labX z.laboratoryAngle t|≤ε ∧
        1/2400-ε≤z.labY z.laboratoryAngle t := by
  obtain ⟨L₁,h₁,C,hC,layer⟩ := reaches_critical_layer
  obtain ⟨L₂,_,orient⟩ := critical_flight_orientation
  refine ⟨max L₁ L₂,h₁.trans (le_max_left ..),C,hC,?_⟩
  intro L hl ε he
  let η := min (1/2:ℝ) (Real.sqrt (ε/7650))
  have hpη : 0<η := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have cap : η≤1/2 := min_le_left .. 
  have etaBudget : 3825*η^2≤ε/2 := by
    have b := pow_le_pow_left₀ hpη.le (min_le_right (1/2:ℝ) (Real.sqrt (ε/7650))) 2
    rw [Real.sq_sqrt (by positivity : (0:ℝ)≤ε/7650)] at b
    linarith
  obtain ⟨B,hB,dir⟩ := orient C η hpη cap
  have lp : 0<L := by linarith [h₁.trans ((le_max_left ..).trans hl)]
  have bp : 0<B := by linarith
  let d := min (1/(32*L)) (min (1/(2*B)) (ε/(2*B)))
  have dp : 0<d := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨d,dp,?_⟩
  intro δ z hd small hk hv hp hq
  obtain ⟨T,hT,crit,strip⟩ := layer L ((le_max_left ..).trans hl) z hd
    (small.trans (min_le_left ..)) hk hv hp hq
  refine ⟨T,hT,crit,strip,?_⟩
  intro t ht
  have d1 := (le_div_iff₀ (by positivity : 0<2*B)).mp
    (small.trans ((min_le_right ..).trans (min_le_left ..)) : δ≤1/(2*B))
  have d2 := (le_div_iff₀ (by positivity : 0<2*B)).mp
    (small.trans ((min_le_right ..).trans (min_le_right ..)) : δ≤ε/(2*B))
  have h := dir z z.laboratoryAngle hd ((le_max_right ..).trans hl) hk hv hp hq
    (by simp [laboratoryAngle]) ⟨ht.1,ht.2.trans hT.2⟩
    (fun x hx => strip x ⟨hx.1,hx.2.trans ht.2⟩) (fun x _ => z.laboratoryAngle_rate x) (by linarith)
  exact ⟨by linarith [h.1],by linarith [h.2]⟩

end ClosedSimilarity.OuterStress.Data
#print axioms ClosedSimilarity.OuterStress.Data.central_shot_positive_ray

