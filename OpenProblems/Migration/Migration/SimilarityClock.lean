import Migration.CurveKinematics
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Set
namespace MigrationGeometry.SimilarityClock

/-- Logarithmic dilation after elapsed physical time from a reference slice. -/
def clock (a t : ℝ) : ℝ := Real.log (1 + 4*a*t) / 4

/-- Elapsed physical time at a prescribed logarithmic dilation. -/
def elapsed (a u : ℝ) : ℝ := (Real.exp (4*u)-1)/(4*a)

theorem clock_nonneg {a t : ℝ} (ha : 0<a) (ht : 0≤t) : 0≤clock a t := by
  exact div_nonneg (Real.log_nonneg (by nlinarith [mul_nonneg ha.le ht])) (by norm_num)

theorem clock_lt {a s t : ℝ} (ha : 0<a) (hs : 0≤s) (hst : s<t) :
    clock a s < clock a t := by
  apply div_lt_div_of_pos_right _ (by norm_num)
  apply Real.strictMonoOn_log
  · exact show 0<1+4*a*s by positivity
  · have := hs.trans_lt hst
    exact show 0<1+4*a*t by positivity
  · nlinarith [mul_pos ha (sub_pos.mpr hst)]

theorem elapsed_nonneg {a u : ℝ} (ha : 0<a) (hu : 0≤u) : 0≤elapsed a u := by
  apply div_nonneg _ (by positivity)
  exact sub_nonneg.mpr (Real.one_le_exp (by linarith))

theorem elapsed_lt {a u v : ℝ} (ha : 0<a) (huv : u<v) : elapsed a u < elapsed a v := by
  apply div_lt_div_of_pos_right _ (by positivity)
  exact sub_lt_sub_right (Real.exp_lt_exp.mpr (by linarith)) _

theorem clock_elapsed {a : ℝ} (ha : 0<a) (u : ℝ) : clock a (elapsed a u)=u := by
  have e : 1+4*a*elapsed a u = Real.exp (4*u) := by
    unfold elapsed
    field_simp
    ring
  rw [clock,e,Real.log_exp]
  ring

/-- The similarity rate equations in physical time, with the reference
scale one and reference rotation angle zero. -/
structure Rates (a b : ℝ) (radius angle : ℝ → ℝ) : Prop where
  radius_zero : radius 0 = 1
  angle_zero : angle 0 = 0
  positive : ∀t, 0≤t → 0<radius t
  radius_cont : ContinuousOn radius (Ici 0)
  angle_cont : ContinuousOn angle (Ici 0)
  radius_rate : ∀t, 0<t → HasDerivAt radius (a/(radius t)^3) t
  angle_rate : ∀t, 0<t → HasDerivAt angle (b*a/(radius t)^4) t

private theorem value_of_zero_rate {f : ℝ → ℝ} (hc : ContinuousOn f (Ici 0))
    (hd : ∀x, 0<x → HasDerivAt f 0 x) {t : ℝ} (ht : 0≤t) : f t=f 0 := by
  rcases ht.eq_or_lt with h|h
  · simp [← h]
  obtain ⟨x,_,hx⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) h
    (hc.mono (fun _ hz => hz.1)) (fun x hx => hd x hx.1)
  have := (div_eq_zero_iff.mp hx.symm).resolve_right (sub_ne_zero.mpr h.ne')
  exact sub_eq_zero.mp this

theorem Rates.solution {a b : ℝ} {radius angle : ℝ → ℝ} (h : Rates a b radius angle)
    {t : ℝ} (ht : 0≤t) : radius t=Real.exp (clock a t) ∧ angle t=b*clock a t := by
  have scaleDer : ∀x, 0<x →
      HasDerivAt (fun v => radius v ^ 4 - 4*a*v) 0 x := by
    intro x hx
    have hh := ((h.radius_rate x hx).pow 4).sub ((hasDerivAt_id x).const_mul (4*a))
    convert hh using 1 <;> try rfl
    all_goals try norm_num
    all_goals try field_simp [(h.positive x hx.le).ne']
    all_goals ring
  have scale := value_of_zero_rate (f := fun v => radius v ^ 4 - 4*a*v)
    ((h.radius_cont.pow 4).sub (continuousOn_const.mul continuousOn_id)) scaleDer ht
  simp only [h.radius_zero,one_pow,mul_zero,sub_zero] at scale
  have fourth : radius t ^ 4=1+4*a*t := by linarith
  have logeq : Real.log (radius t)=clock a t := by
    rw [clock,←fourth,Real.log_pow]
    push_cast
    ring
  have turnDer : ∀x, 0<x →
      HasDerivAt (fun v => angle v - b*Real.log (radius v)) 0 x := by
    intro x hx
    have hh := (h.angle_rate x hx).sub
      (((h.radius_rate x hx).log (h.positive x hx.le).ne').const_mul b)
    convert hh using 1 <;> try rfl
    all_goals try field_simp [(h.positive x hx.le).ne']
    all_goals ring
  have turn := value_of_zero_rate (f := fun v => angle v - b*Real.log (radius v))
    (h.angle_cont.sub (continuousOn_const.mul (h.radius_cont.log (fun x hx => (h.positive x hx).ne'))))
    turnDer ht
  simp only [h.radius_zero,h.angle_zero,Real.log_one,mul_zero,sub_zero] at turn
  exact ⟨by rw [←logeq,Real.exp_log (h.positive t ht)],by linarith [logeq ▸ turn]⟩

#print axioms Rates.solution
end MigrationGeometry.SimilarityClock
