import LengthGrowth.ActualFlow.AmbientDiskIntegral
import LengthGrowth.ActualFlow.GrowthEquivalence

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

private theorem cost_pointwise {m : ℝ} (hm : 0<m) {k k' F : ℝ} (hk : |k| ≤ m) :
    m^3 * (2* |k| * |k'| + |k|^3) ≤
      3*m^4*k^2 + F^2 + m^2*(k'^2 + k*(F-k^3/2)) := by
  have hsq : k^2 ≤ m^2 := (sq_abs k) ▸ pow_le_pow_left₀ (abs_nonneg k) hk 2
  have q1 := sq_nonneg (m^2 * |k| - m * |k'|)
  have q2 := sq_nonneg (F + m^2*k/2)
  have q3 := mul_nonneg (mul_nonneg (pow_nonneg hm.le 3) (sq_nonneg |k|)) (sub_nonneg.mpr hk)
  have q4 := mul_nonneg (mul_nonneg (sq_nonneg m) (sq_nonneg k)) (sub_nonneg.mpr hsq)
  have q5 := mul_nonneg (pow_nonneg hm.le 4) (sq_nonneg k)
  have he : 3*m^4*k^2 + F^2 + m^2*(k'^2 + k*(F-k^3/2)) -
      m^3*(2* |k| * |k'| + |k|^3) = (m^2 * |k| - m * |k'|)^2 + (F+m^2*k/2)^2 +
      m^3 * |k|^2 * (m-|k|) + m^2*k^2*(m^2-k^2)/2 + m^4*k^2/4 := by
    ring_nf
    simp only [sq_abs]
    ring
  linarith

theorem diskEnergy_le_of_small_force {m : ℝ} (hm : 0<m) (hk : ∀ s, |c.curvature s| ≤ m)
    (hd : c.dissipation ≤ m^4*c.energy) (p : ℂ) {R : ℝ} (hR : 0<R) :
    c.diskEnergy p R ≤ 14 * Real.pi * R * m * c.energy := by
  let J := fun s => c.curvature₁ s^2 + c.curvature s * c.curvature₂ s
  have hJ : Continuous J := (c.curvature₁_continuous.pow 2).add (c.curvature_continuous.mul c.curvature₂_continuous)
  have hder (s : ℝ) : HasDerivAt (fun u => c.curvature u * c.curvature₁ u) (J s) s := by
    convert! (c.curvature_deriv s).mul (c.curvature₁_deriv s) using 1
    dsimp [J]; ring
  have h0 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period) (fun s _ => hder s) (hJ.intervalIntegrable _ _)
  have hp : c.curvature c.period = c.curvature 0 := by simpa using c.curvature_periodic 0
  have hp' : c.curvature₁ c.period = c.curvature₁ 0 := by simpa using c.curvature₁_periodic 0
  rw [hp,hp',sub_self] at h0
  have h1 : Continuous (fun s => 3*m^4*c.curvature s^2) := (c.curvature_continuous.pow 2).const_mul (3*m^4)
  have h2 : Continuous (fun s => c.force s^2) := c.force_continuous.pow 2
  have h3 : Continuous (fun s => m^2*J s) := hJ.const_mul (m^2)
  have h12 : Continuous (fun s => 3*m^4*c.curvature s^2+c.force s^2) := h1.add h2
  have hi := intervalIntegral.integral_mono_on (μ := volume) c.period_pos.le
    ((c.cost_cont.const_mul (m^3)).intervalIntegrable 0 c.period)
    (((h1.add h2).add h3).intervalIntegrable 0 c.period) (fun s _ => by
      change m^3 * c.cost s ≤ 3*m^4*c.curvature s^2 + c.force s^2 + m^2*J s
      simpa only [cost,force,J,add_sub_cancel_right] using
        (cost_pointwise (k':=c.curvature₁ s) (F:=c.force s) hm (hk s)))
  change (∫ s in 0..c.period, m^3*c.cost s) ≤
    ∫ s in 0..c.period, 3*m^4*c.curvature s^2 + c.force s^2 + m^2*J s at hi
  rw [intervalIntegral.integral_add (h12.intervalIntegrable _ _) (h3.intervalIntegrable _ _),
    intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, h0, mul_zero, add_zero] at hi
  have hE : (∫ s in 0..c.period, c.curvature s^2) = 2*c.energy := by unfold energy; ring
  rw [hE] at hi
  change _ ≤ _ + c.dissipation at hi
  have hc : (∫ s in 0..c.period, c.cost s) ≤ 7*m*c.energy := by
    apply (mul_le_mul_iff_of_pos_left (pow_pos hm 3)).mp
    nlinarith only [hi,hd]
  have hr := c.diskEnergy_le_cost p hR
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*(R*Real.pi) by positivity)
  linarith only [hr,hh,show 2*(R*Real.pi)*(7*m*c.energy)=14*Real.pi*R*m*c.energy by ring]

theorem disk_concentration_coercive {R θ : ℝ} (hR : 0<R) (hθ : 0<θ) :
    ∃ d : ℝ, 0<d ∧ ∀ c : ClosedFrenetCurve,
      (∃ p, θ*c.energy ≤ c.diskEnergy p (R/c.energy)) → d*c.energy^5 ≤ c.dissipation := by
  let a := θ/(28*Real.pi*R)
  have ha : 0<a := by dsimp [a]; positivity
  refine ⟨min (a^4) (a^6/16777216), lt_min (pow_pos ha _) (by positivity), ?_⟩
  intro b hb
  obtain ⟨p,hp⟩ := hb
  by_contra! hd
  have he := b.energy_pos
  have h4 := hd.le.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg he.le 5))
  have h6 := hd.le.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg he.le 5))
  have hk (s : ℝ) : |b.curvature s| ≤ a*b.energy := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (6:ℕ) ≠ 0) (by positivity : 0 ≤ a*b.energy)
    have hb := b.energy_dissipation_controls_curvature s
    have hh := mul_le_mul_of_nonneg_left h6 he.le
    nlinarith only [hb,hh]
  have hD : b.dissipation ≤ (a*b.energy)^4 * b.energy := by nlinarith only [h4]
  have hh := b.diskEnergy_le_of_small_force (mul_pos ha he) hk hD p (div_pos hR he)
  have heq : 14*Real.pi*(R/b.energy)*(a*b.energy)*b.energy = θ*b.energy/2 := by
    dsimp [a]; field_simp [Real.pi_ne_zero,hR.ne',he.ne']; ring
  rw [heq] at hh
  nlinarith only [hp,hh,mul_pos hθ he]

end LengthGrowth.ClosedFrenetCurve

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- The integral is over all disk visits by the canonical unit-speed representative
of the actual slice. Its curvature and energy are transported from the material curve. -/
def HasAmbientEnergyConcentration : Prop :=
  ∃ R θ : ℝ, 0<R ∧ 0<θ ∧ ∀ (t : ℝ) (ht : 0≤t), ∃ p,
    θ*c.energy t ≤ (c.regularPositionAt ht).closedFrenetCurve.diskEnergy p (R/c.energy t)

theorem quarter_length_of_ambient_concentration (hflow : c.IsNormalFEF)
    (h : c.HasAmbientEnergyConcentration) : c.HasQuarterLengthBound := by
  obtain ⟨R,θ,hR,hθ,hcon⟩ := h
  obtain ⟨d,hd,hco⟩ := ClosedFrenetCurve.disk_concentration_coercive hR hθ
  have hcoerc (t : ℝ) (ht : 0≤t) : d*c.energy t^5 ≤ c.dissipation t := by
    let a := c.regularPositionAt ht
    have he : a.closedFrenetCurve.energy = c.energy t := a.closedFrenetCurve_energy
    have hD : a.closedFrenetCurve.dissipation = c.dissipation t := a.closedFrenetCurve_dissipation
    rw [←he,←hD]
    apply hco
    simpa only [he] using hcon t ht
  let B := FreeElasticScalar.fourthRoot (1/(4*d))
  have hbase : 0 < 1/(4*d) := by positivity
  have hB := FreeElasticScalar.fourthRoot_pos hbase
  have heq : 1 ≤ 4*d*B^4 := by
    dsimp [B]; rw [FreeElasticScalar.fourthRoot_pow_four hbase.le]; field_simp [hd.ne']; norm_num
  have hL := c.length_pos (t:=0) le_rfl
  refine ⟨c.length 0+4*B, by dsimp [B]; positivity, fun t ht => ?_⟩
  have hw := FreeElasticScalar.coercive_quarter_length_bound c.length c.energy c.lengthRate
    c.dissipation d B hd hB heq c.length_continuousOn c.energy_continuousOn
    (fun x hx => c.energy_pos hx) (fun x hx => c.length_hasDerivAt_normal hflow hx)
    (fun x hx => c.energy_hasDerivAt_normal hflow hx) (fun x hx => c.lengthRate_sq_le hx.le)
    (fun x hx => hcoerc x hx.le) t ht
  have hq : 1 ≤ FreeElasticScalar.fourthRoot (1+t) := by
    simpa [FreeElasticScalar.fourthRoot] using FreeElasticScalar.fourthRoot_mono (show (1:ℝ) ≤ 1+t by linarith)
  have hm := FreeElasticScalar.fourthRoot_mono (show t≤1+t by linarith)
  have hz := mul_nonneg (Real.sqrt_nonneg t) (c.energy_pos ht).le
  nlinarith [mul_le_mul_of_nonneg_left hq hL.le,
    mul_le_mul_of_nonneg_left hm hB.le]

theorem ambient_concentration_of_bounded_energyLength (h : c.HasBoundedEnergyLength) :
    c.HasAmbientEnergyConcentration := by
  obtain ⟨K,hK⟩ := h
  let R := max 1 K
  have hR : 0<R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨R,1,hR,zero_lt_one,fun t ht => ?_⟩
  let b := (c.regularPositionAt ht).closedFrenetCurve
  have he : b.energy = c.energy t := (c.regularPositionAt ht).closedFrenetCurve_energy
  have hp : b.period ≤ R/c.energy t := by
    apply (le_div_iff₀ (c.energy_pos ht)).mpr
    change c.length t * c.energy t ≤ R
    rw [mul_comm]
    exact (hK t ht).trans (le_max_right _ _)
  refine ⟨b.curve 0, ?_⟩
  change 1 * c.energy t ≤ b.diskEnergy (b.curve 0) _
  rw [one_mul, b.diskEnergy_eq_energy_of_period_le hp, he]

theorem quarter_length_iff_ambient_concentration (hflow : c.IsNormalFEF) :
    c.HasQuarterLengthBound ↔ c.HasAmbientEnergyConcentration :=
  ⟨fun h => c.ambient_concentration_of_bounded_energyLength
    (c.bounded_energyLength_of_quarter_length hflow h), c.quarter_length_of_ambient_concentration hflow⟩

end LengthGrowth.ActualFlow.ForwardImmersion
