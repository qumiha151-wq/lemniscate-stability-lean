import LengthGrowth.ActualFlow.RecordSweptAreaDuration
import LengthGrowth.ActualFlow.TrigonometricPhysicalRate

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.Multicover.Trigonometric

private theorem square_average_error {g f : Fn} {C : ℝ}
    (close : ∀s, |g s-f s|≤1/1000) (bound : ∀s,|f s|≤C) :
    |average (g^2)-average (f^2)|≤(1/1000)*(2*C+1/1000) := by
  rw [←map_sub]
  apply average_abs_le
  intro s
  change |(g s)^2-(f s)^2|≤_
  have b : |g s+f s|≤2*C+1/1000 := by
    have tri:=abs_add_le (g s-f s) (f s+f s)
    rw [show g s-f s+(f s+f s)=g s+f s by ring] at tri
    linarith only [tri,abs_add_le (f s) (f s),bound s,close s]
  rw [show (g s)^2-(f s)^2=(g s-f s)*(g s+f s) by ring,abs_mul]
  exact mul_le_mul (close s) b (abs_nonneg _) (by norm_num)

/-- A uniform neighborhood of the trigonometric fields has an order-one
RMS-normalized force moment, independently of the number of cells. -/
theorem trigonometric_force_fraction {n:ℕ} (hn:0<n) {w h:Fn}
    (wc:∀s, |w s-trigWave n s|≤1/1000) (hc:∀s, |h s-trigForce n s|≤1/1000) :
    0<average (w^2) ∧ (1/8:ℝ)≤2*average (h^2)/(average (w^2))^3 := by
  have wb:=square_average_error wc (trigWave_bound n)
  have hb:=square_average_error hc (trigForce_bound n)
  rw [show average ((trigWave n)^2)=4097/2048 by
    rw [average_eq,wave_square hn,mul_div_cancel_right₀ _ period_pos.ne']] at wb
  rw [show average ((trigForce n)^2)=60523245573/68719476736 by
    rw [average_eq,force_square hn,mul_div_cancel_right₀ _ period_pos.ne']] at hb
  have wp : 0<average (w^2) := by linarith only [(abs_le.mp wb).1]
  have up : average (w^2)≤21/10 := by linarith only [(abs_le.mp wb).2]
  have lo : (4/5:ℝ)≤average (h^2) := by linarith only [(abs_le.mp hb).1]
  refine ⟨wp,(le_div_iff₀ (pow_pos wp 3)).mpr ?_⟩
  nlinarith only [lo,pow_le_pow_left₀ wp.le up 3]

theorem prescribed_trigonometric_force_fraction {n:ℕ} (hn:0<n) {m a A:ℝ}
    (ha:|a|≤3) (large:1000000*(1+|m|)≤A) (near:|(n:ℝ)-A|≤1) :
    (1/8:ℝ)≤2*average ((scaledForce n m a A)^2)/(average ((scaledCurvature n m a A)^2))^3 := by
  obtain ⟨tiny,w,h⟩:=scaled_errors (n:=n) ha large near
  exact (trigonometric_force_fraction hn (fun s=>by linarith only [w s,tiny])
    (fun s=>by linarith only [h s,tiny])).2

end LengthGrowth.Multicover.Trigonometric

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c:ForwardImmersion)

/-- At a late record with a macroscopic area sweep and a non-negligible
terminal force, the logarithmic energy-loss rate grows at least linearly in EL. -/
theorem sweptArea_record_log_energy_slope (hf:c.IsNormalFEF) {s t q d b:ℝ}
    (hs:0≤s) (st:s≤t) (dd:0≤d) (bb:0≤b) (qq:1≤q)
    (rec:∀u∈Icc s t,c.normalizedProduct u≤c.normalizedProduct t)
    (level:q*c.length s=c.length t)
    (sweep:d*c.length t^2≤∫u in s..t,c.sweptAreaRate u)
    (force:b*(2*c.energy t/c.length t)^2≤c.dissipation t/c.energy t) :
    4*b*d^2*c.normalizedProduct t≤(q-1)*(t*c.dissipation t/c.energy t) := by
  have time:=c.sweptArea_record_rms_duration hf hs st dd rec level sweep
  have cost:=mul_le_mul_of_nonneg_left time bb
  have coarse:=mul_le_mul_of_nonneg_right force
    (mul_nonneg (sub_nonneg.mpr qq) (sub_nonneg.mpr st))
  have rest:=mul_nonneg (mul_nonneg (sub_nonneg.mpr qq) hs)
    (div_nonneg (c.dissipation_nonneg t) (c.energy_pos (hs.trans st)).le)
  rw [mul_div_assoc]
  nlinarith only [cost,coarse,rest]

end LengthGrowth.ActualFlow.ForwardImmersion

#print axioms LengthGrowth.Multicover.Trigonometric.prescribed_trigonometric_force_fraction
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.sweptArea_record_log_energy_slope
