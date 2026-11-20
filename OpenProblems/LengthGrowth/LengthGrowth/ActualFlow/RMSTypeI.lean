import LengthGrowth.ActualFlow.GrowthEquivalence
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

/-- The quadratic functional used for an RMS curvature Type-I bound. -/
def rmsWeighted (a t : ℝ) : ℝ := a*c.length t^2+t*c.energy t^2

private theorem weighted_derivative (hf : c.IsNormalFEF) {a t : ℝ} (ht : 0<t) :
    HasDerivAt (c.rmsWeighted a)
      (2*a*c.length t*c.lengthRate t+c.energy t^2-2*t*c.energy t*c.dissipation t) t := by
  have h := (((c.length_hasDerivAt_normal hf ht).pow 2).const_mul a).add
    ((hasDerivAt_id t).mul ((c.energy_hasDerivAt_normal hf ht).pow 2))
  convert! h using 1
  simp [Pi.pow_apply]
  ring

/-- A sharp weighted differential estimate on each material slice. -/
theorem rms_weighted_rate (hf : c.IsNormalFEF) {a t : ℝ} (ht : 0<t)
    (cap : (1-2*a)*(t*c.energy t^2) ≤ a^2*c.length t^2) :
    t*deriv (c.rmsWeighted a) t ≤ 2*a*c.rmsWeighted a t := by
  rw [(c.weighted_derivative hf ht).deriv,rmsWeighted]
  nlinarith only [cap,sq_nonneg (a*c.length t-t*c.lengthRate t),
    mul_le_mul_of_nonneg_left (c.lengthRate_sq_le ht.le) (sq_nonneg t)]

theorem rms_weighted_antitone (hf : c.IsNormalFEF) {a T : ℝ} (hT : 0<T)
    (cap : ∀t≥T,(1-2*a)*(t*c.energy t^2)≤a^2*c.length t^2) :
    AntitoneOn (fun t : ℝ => c.rmsWeighted a t * t^(-2*a)) (Ici T) := by
  have sub : Ici T ⊆ Ici (0:ℝ) := fun _ hx => hT.le.trans hx
  have hc : ContinuousOn (c.rmsWeighted a) (Ici T) :=
    (continuousOn_const.mul ((c.length_continuousOn.mono sub).pow 2)).add
      (continuousOn_id.mul ((c.energy_continuousOn.mono sub).pow 2))
  have hp {t : ℝ} (ht : T<t) := hT.trans ht
  have dw {t : ℝ} (ht : T<t) := (c.weighted_derivative (a:=a) hf (hp ht)).mul
    (Real.hasDerivAt_rpow_const (p := -2*a) (Or.inl (hp ht).ne'))
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (hc.mul
    (continuousOn_id.rpow_const (fun t ht => Or.inl (hT.trans_le ht).ne')))
  · rw [interior_Ici]
    intro t ht
    exact (dw ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    change deriv (c.rmsWeighted a * fun x : ℝ => x^(-2*a)) t ≤ 0
    rw [(dw ht).deriv]
    have rate := c.rms_weighted_rate hf (hp ht) (cap t ht.le)
    rw [(c.weighted_derivative hf (hp ht)).deriv] at rate
    rw [Real.rpow_sub (hp ht),Real.rpow_one]
    have z := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr rate)
      (div_nonneg (Real.rpow_nonneg (hp ht).le (-2*a)) (hp ht).le)
    convert! z using 1
    field_simp [(hp ht).ne']
    ring

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.rms_weighted_antitone
