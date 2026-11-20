import LengthGrowth.ActualFlow.GrowthEnvelope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- Two geometric slice estimates suffice for the sharp fourth-power comparison.
The radius in this intermediary need not be continuous in time. -/
theorem large_radius_time_of_slice_bounds (hf : c.IsNormalFEF) {C : ℝ} (hp : 0<C)
    (hC : C<2) (T : ℝ) (R : ℝ→ℝ)
    (slices : ∀t>0,c.energy t≤2*c.dissipation t*(R t)^4 ∧ 1≤c.energy t*R t) :
    ∃t, 0<t ∧ T<t ∧ C*t<(R t)^4 := by
  by_contra! fail
  let S:=max 1 (T+1)
  have sp : 0<S := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have late : T<S := lt_of_lt_of_le (by linarith : T<T+1) (le_max_right ..)
  let b:=(2-C)/C^2
  have bp : 0<b := div_pos (sub_pos.mpr hC) (pow_pos hp 2)
  let W:=fun t : ℝ => t*c.energy t^4+b*Real.log t
  have derivW {t : ℝ} (ht : 0<t) : HasDerivAt W
      (c.energy t^4-4*t*c.dissipation t*c.energy t^3+b/t) t := by
    have g:=((hasDerivAt_id t).mul ((c.energy_hasDerivAt_normal hf ht).pow 4)).add
      ((Real.hasDerivAt_log ht.ne').const_mul b)
    convert! g using 1
    simp [Pi.pow_apply,div_eq_mul_inv]
    ring
  have desc : AntitoneOn W (Ici S) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro t ht
      exact (derivW (sp.trans_le ht)).continuousAt.continuousWithinAt
    · rw [interior_Ici]
      intro t ht
      exact (derivW (sp.trans ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      have ht0:=sp.trans ht
      have e:=c.energy_pos ht0.le
      have d:=c.dissipation_nonneg t
      obtain ⟨vir,lower⟩:=slices t ht0
      have rad:=fail t ht0 (late.trans ht)
      have v : c.energy t≤2*C*t*c.dissipation t := by
        nlinarith only [vir,mul_le_mul_of_nonneg_left rad (by positivity : 0≤2*c.dissipation t)]
      have l4:=pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) lower 4
      rw [one_pow,mul_pow] at l4
      have floor : 1≤C*t*c.energy t^4 := by
        nlinarith only [l4,mul_le_mul_of_nonneg_left rad (pow_nonneg e.le 4)]
      rw [(derivW ht0).deriv]
      dsimp only [b]
      field_simp [hp.ne',ht0.ne']
      nlinarith only [mul_le_mul_of_nonneg_left v
          (by positivity : 0≤2*C*t*c.energy t^3),
        mul_le_mul_of_nonneg_left floor (sub_nonneg.mpr hC.le)]
  let u:=max S (Real.exp ((W S+1)/b))
  have su : S≤u := le_max_left .. 
  have q:=desc (mem_Ici.mpr (le_refl S)) (mem_Ici.mpr su) su
  have lg:=Real.log_le_log (Real.exp_pos ((W S+1)/b)) (le_max_right S (Real.exp ((W S+1)/b)))
  rw [Real.log_exp] at lg
  have bad:=(div_le_iff₀ bp).mp lg
  change u*c.energy u^4+b*Real.log u≤W S at q
  change W S+1≤Real.log u*b at bad
  nlinarith only [bad,q,mul_nonneg (sp.le.trans su) (pow_nonneg (c.energy_nonneg u) 4)]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.large_radius_time_of_slice_bounds
