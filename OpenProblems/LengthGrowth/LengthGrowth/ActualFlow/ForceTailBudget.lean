import LengthGrowth.ActualFlow.ForceAngularSpeed
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- Explicit spatial estimate supplied by the full weak dissipation variation. -/
def HasForceRateBound : Prop :=
  ∀ t : ℝ, 0<t → deriv c.dissipation t+c.forceSecondMass t≤
    (2500000*(c.energy t*c.dissipation t)^(2/3:ℝ)+
      32*c.energy t^(1/4:ℝ)*c.dissipation t^(3/4:ℝ))*c.dissipation t

theorem forceSecondMass_nonneg (t : ℝ) : 0≤c.forceSecondMass t :=
  intervalIntegral.integral_nonneg_of_forall c.period_pos.le
    (fun _ => mul_nonneg (sq_nonneg _) (norm_nonneg _))

private theorem rate_to_quarter_root {e D E V Y : ℝ} (he : E≤e) (ep : 0<E) (dp : 0<D)
    (yp : 0≤Y) (rate : V+Y≤(2500000*(E*D)^(2/3:ℝ)+32*E^(1/4:ℝ)*D^(3/4:ℝ))*D) :
    V≤(2500000*e^(2/3:ℝ)+32*e^(1/4:ℝ))*(1+D)^(3/4:ℝ)*D := by
  have e2 := Real.rpow_le_rpow ep.le he (by norm_num : (0:ℝ)≤2/3)
  have e4 := Real.rpow_le_rpow ep.le he (by norm_num : (0:ℝ)≤1/4)
  have d2 : D^(2/3:ℝ)≤(1+D)^(3/4:ℝ) :=
    (Real.rpow_le_rpow dp.le (by linarith : D≤1+D) (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  have d4 := Real.rpow_le_rpow dp.le (by linarith : D≤1+D) (by norm_num : (0:ℝ)≤3/4)
  rw [Real.mul_rpow ep.le dp.le] at rate
  have a := mul_le_mul e2 d2 (Real.rpow_nonneg dp.le _) (Real.rpow_nonneg (ep.le.trans he) _)
  have b := mul_le_mul e4 d4 (Real.rpow_nonneg dp.le _) (Real.rpow_nonneg (ep.le.trans he) _)
  exact (le_add_of_nonneg_right yp).trans (rate.trans (mul_le_mul_of_nonneg_right (by nlinarith only [a,b]) dp.le))

/-- On every positive tail the dissipation is bounded. No assumed bound on its
initial time derivative or any normalized force derivatives is needed. -/
theorem force_dissipation_tail_bound (hf : c.IsNormalFEF) (rate : c.HasForceRateBound)
    {s : ℝ} (hs : 0<s) : ∃ M≥1, ∀ t≥s, c.dissipation t≤M := by
  let D := c.dissipation
  let E := c.energy
  let C := 2500000*(E s)^(2/3:ℝ)+32*(E s)^(1/4:ℝ)
  let h := fun t => (1+D t)^(1/4:ℝ)+(C/4)*E t
  have Cpos : 0≤C := by dsimp [C]; positivity [c.energy_pos hs.le]
  have dp (t : ℝ) (st : s≤t) : 0<D t := c.force_dissipation_pos (hs.le.trans st)
  have dh (t : ℝ) (st : s≤t) : HasDerivAt h
      ((1/4)*(1+D t)^(-(3/4):ℝ)*deriv D t-C/4*D t) t := by
    have ht := hs.trans_le st
    have d := ((c.dissipation_differentiable_positive ht).hasDerivAt.const_add 1).rpow_const
      (p:=1/4) (Or.inl (by linarith [dp t st] : 1+D t≠0))
    convert! d.add ((c.energy_hasDerivAt_normal hf ht).const_mul (C/4)) using 1
    dsimp only [D]
    ring_nf
  have mono : AntitoneOn h (Ici s) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici s)
      (fun t ht => (dh t ht).continuousAt.continuousWithinAt)
      (fun t ht => (dh t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    have st : s≤t := interior_subset ht
    rw [(dh t st).deriv]
    have upper := rate_to_quarter_root (c.energy_le_of_le hf hs.le st)
      (c.energy_pos (hs.le.trans st)) (dp t st) (c.forceSecondMass_nonneg t) (rate t (hs.trans_le st))
    change deriv D t≤C*(1+D t)^(3/4:ℝ)*D t at upper
    have mult := mul_le_mul_of_nonneg_left upper (Real.rpow_nonneg
      (by linarith [dp t st] : 0≤1+D t) (-(3/4):ℝ))
    have cancel : (1+D t)^(-(3/4):ℝ)*(1+D t)^(3/4:ℝ)=1 := by
      rw [←Real.rpow_add (by linarith [dp t st]),neg_add_cancel,Real.rpow_zero]
    nlinarith only [mult,congrArg (fun a : ℝ => C*D t*a) cancel]
  let K := max 1 ((h s)^4)
  refine ⟨K,le_max_left ..,?_⟩
  intro t st
  have ord := mono (show s∈Ici s by exact le_refl s) st st
  have addp := mul_nonneg (div_nonneg Cpos (by norm_num : (0:ℝ)≤4)) (c.energy_pos (hs.le.trans st)).le
  have rootcap : (1+D t)^(1/4:ℝ)≤h s := by change (1+D t)^(1/4:ℝ)+C/4*E t≤h s at ord; linarith
  have base : 0≤1+D t := by linarith [dp t st]
  have p4 := pow_le_pow_left₀ (Real.rpow_nonneg base _) rootcap 4
  have id : ((1+D t)^(1/4:ℝ))^4=1+D t := by
    rw [←Real.rpow_natCast,←Real.rpow_mul base]
    norm_num
  rw [id] at p4
  exact (by linarith only [p4] : D t≤h s^4).trans (le_max_right ..)

private theorem absorb_rate {e E M D V Y : ℝ} (ep : 0<E) (dp : 0<D) (he : E≤e) (hm : D≤M)
    (rate : V+Y≤(2500000*(E*D)^(2/3:ℝ)+32*E^(1/4:ℝ)*D^(3/4:ℝ))*D) :
    V+Y≤(2500000*e^(2/3:ℝ)+32*e^(1/4:ℝ)*M^(1/12:ℝ))*D^(5/3:ℝ) := by
  rw [Real.mul_rpow ep.le dp.le] at rate
  have e2 := Real.rpow_le_rpow ep.le he (by norm_num : (0:ℝ)≤2/3)
  have e4 := Real.rpow_le_rpow ep.le he (by norm_num : (0:ℝ)≤1/4)
  have d1 := Real.rpow_le_rpow dp.le hm (by norm_num : (0:ℝ)≤1/12)
  have first : D^(2/3:ℝ)*D=D^(5/3:ℝ) := by rw [←Real.rpow_add_one dp.ne']; norm_num
  have second : D^(3/4:ℝ)*D=D^(1/12:ℝ)*D^(5/3:ℝ) := by
    rw [←Real.rpow_add_one dp.ne',←Real.rpow_add dp]; norm_num
  have prod := mul_le_mul e4 d1 (Real.rpow_nonneg dp.le _) (Real.rpow_nonneg (ep.le.trans he) _)
  apply rate.trans
  calc
    _ = 2500000*E^(2/3:ℝ)*(D^(2/3:ℝ)*D)+32*E^(1/4:ℝ)*(D^(3/4:ℝ)*D) := by ring
    _ ≤ _ := by
      rw [first,second]
      nlinarith only [mul_le_mul_of_nonneg_right e2 (Real.rpow_nonneg dp.le (5/3:ℝ)),
        mul_le_mul_of_nonneg_right prod (Real.rpow_nonneg dp.le (5/3:ℝ))]

theorem force_weighted_tail_budget (hf : c.IsNormalFEF) (rate : c.HasForceRateBound)
    {s : ℝ} (hs : 0<s) : ∃ B : ℝ, ∀ t≥s,
      (∫ x in s..t, c.dissipation x^(-(2/3):ℝ)*c.forceSecondMass x)≤B := by
  obtain ⟨M,hM,cap⟩ := c.force_dissipation_tail_bound hf rate hs
  let C := 2500000*(c.energy s)^(2/3:ℝ)+32*(c.energy s)^(1/4:ℝ)*M^(1/12:ℝ)
  have cp : 0≤C := by dsimp [C]; positivity [c.energy_pos hs.le]
  refine ⟨3*(c.dissipation s)^(1/3:ℝ)+C*c.energy s,?_⟩
  intro t st
  have h := c.force_weighted_budget (C:=C) hf hs st (fun x hx => absorb_rate
    (c.energy_pos (hs.le.trans hx.1.le)) (c.force_dissipation_pos (hs.le.trans hx.1.le))
    (c.energy_le_of_le hf hs.le hx.1.le) (cap x hx.1.le) (rate x (hs.trans hx.1)))
  linarith only [h,Real.rpow_nonneg (c.dissipation_nonneg t) (1/3:ℝ),
    mul_nonneg cp (c.energy_pos (hs.le.trans st)).le]

theorem force_weighted_tail_integrable (hf : c.IsNormalFEF) (rate : c.HasForceRateBound)
    {s : ℝ} (hs : 0<s) :
    IntegrableOn (fun x => c.dissipation x^(-(2/3):ℝ)*c.forceSecondMass x) (Ioi s) := by
  obtain ⟨B,cap⟩ := c.force_weighted_tail_budget hf rate hs
  let f := fun x => c.dissipation x^(-(2/3):ℝ)*c.forceSecondMass x
  have cont : ContinuousOn f (Ici s) := ((c.dissipation_continuousOn.mono
    (fun _ hx => hs.le.trans hx)).rpow_const (fun x hx => Or.inl (c.force_dissipation_pos (hs.le.trans hx)).ne')).mul
    (c.forceSecondMass_continuousOn.mono (fun _ hx => hs.trans_le hx))
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (b:=fun x : ℝ => x) (l:=atTop) B s _
    tendsto_id
  · filter_upwards [eventually_ge_atTop s] with t st
    have eq := intervalIntegral.integral_congr (μ:=volume) (a:=s) (b:=t) (f:=fun x => ‖f x‖) (g:=f) (fun x _ => by
      change ‖c.dissipation x^(-(2/3):ℝ)*c.forceSecondMass x‖ = _
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (c.dissipation_nonneg x) _) (c.forceSecondMass_nonneg x))])
    exact eq.trans_le (cap t st)
  · intro x
    exact (cont.mono (fun _ hx => hx.1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem force_dissipation_tail_integrable (hf : c.IsNormalFEF) {s : ℝ} (hs : 0<s) :
    IntegrableOn c.dissipation (Ioi s) := by
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (b:=fun x : ℝ => x) (l:=atTop)
    (c.energy s) s _ tendsto_id
  · filter_upwards [eventually_ge_atTop s] with t st
    have eq := intervalIntegral.integral_congr (μ:=volume) (a:=s) (b:=t)
      (f:=fun x => ‖c.dissipation x‖) (g:=c.dissipation) (fun x _ => by
        exact Real.norm_of_nonneg (c.dissipation_nonneg x))
    rw [eq]
    linarith only [c.energy_add_integral_dissipation hf hs.le st,c.energy_pos (hs.le.trans st)]
  · intro x
    exact (c.dissipation_continuousOn.mono (show Icc s x⊆Ici 0 from fun _ hx => hs.le.trans hx.1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.force_dissipation_tail_bound
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.force_weighted_tail_integrable
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.force_dissipation_tail_integrable
