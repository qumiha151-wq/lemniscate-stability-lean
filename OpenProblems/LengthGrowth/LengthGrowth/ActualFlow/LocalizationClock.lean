import LengthGrowth.ActualFlow.MaterialWeightedRate
import LengthGrowth.ActualFlow.RelativeEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow

def localizationScale (t : ℝ) : ℝ := t ^ (1/3:ℝ)

theorem localizationScale_cube {t : ℝ} (ht : 0≤t) : localizationScale t^3=t := by
  rw [localizationScale,←Real.rpow_natCast,←Real.rpow_mul ht]
  norm_num

theorem localizationScale_grows : Tendsto localizationScale atTop atTop :=
  tendsto_rpow_atTop (by norm_num)

namespace ForwardImmersion
variable (c : ForwardImmersion)

/-- A continuous majorant for the squared peak curvature. Time is clamped
below one only to give a globally continuous primitive in the proof. -/
def localizationDensity (t : ℝ) : ℝ :=
  (16777216*c.energy (max 1 t)*c.dissipation (max 1 t))^(1/3:ℝ)

def localizationClock (t : ℝ) : ℝ := ∫ x in 1..t,c.localizationDensity x

theorem localizationDensity_continuous : Continuous c.localizationDensity := by
  have cm : Continuous (fun x : ℝ => max 1 x) := continuous_const.max continuous_id
  have sub (x : ℝ) : max 1 x∈Ici (0:ℝ) := (by norm_num : (0:ℝ)≤1).trans (le_max_left _ _)
  exact (((c.energy_continuousOn.comp_continuous cm sub).const_mul 16777216).mul
    (c.dissipation_continuousOn.comp_continuous cm sub)).rpow_const (fun _ => Or.inr (by norm_num))

theorem localizationDensity_nonneg (t : ℝ) : 0≤c.localizationDensity t := by
  have ep := c.energy_pos (show 0≤max 1 t by have := le_max_left (1:ℝ) t; linarith)
  exact Real.rpow_nonneg (by have := c.dissipation_nonneg (max 1 t); positivity) _

theorem localizationDensity_cube {t : ℝ} (ht : 1≤t) :
    c.localizationDensity t^3=16777216*c.energy t*c.dissipation t := by
  unfold localizationDensity
  rw [max_eq_right ht]
  apply localizationScale_cube
  have ep := c.energy_pos (show 0≤t by linarith)
  have dp := c.dissipation_nonneg t
  positivity

theorem curvature_sq_le_localizationDensity {t : ℝ} (ht : 1≤t) (u : ℝ) :
    curvature (c.position t) u^2≤c.localizationDensity t := by
  have h := c.interior.stress_coercivity (show t∈Ioi (0:ℝ) from (by change 0<t; linarith)) u
  change (1/16777216:ℝ)*|curvature (c.position t) u|^6 ≤ c.energy t*c.dissipation t at h
  have sixth : (curvature (c.position t) u^2)^3≤(c.localizationDensity t)^3 := by
    rw [c.localizationDensity_cube ht]
    rw [show |curvature (c.position t) u|^6=(curvature (c.position t) u^2)^3 by
      rw [show (6:ℕ)=2*3 by norm_num,pow_mul,sq_abs]] at h
    linarith only [h]
  exact (pow_le_pow_iff_left₀ (sq_nonneg _) (c.localizationDensity_nonneg t) (by norm_num : (3:ℕ)≠0)).mp sixth

theorem localizationClock_hasDerivAt (t : ℝ) :
    HasDerivAt c.localizationClock (c.localizationDensity t) t :=
  intervalIntegral.integral_hasDerivAt_right (c.localizationDensity_continuous.intervalIntegrable 1 t)
    c.localizationDensity_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    c.localizationDensity_continuous.continuousAt

private theorem clock_restart (hf : c.IsNormalFEF) {s t b : ℝ} (hs : 1≤s) (hst : s≤t) (hb : 0<b) :
    c.localizationClock t ≤ c.localizationClock s + b*(t-s)+
      ((16777216*c.energy 1)/b^2)*(c.energy s-c.energy t) := by
  let A := 16777216*c.energy 1
  have hc := c.localizationDensity_continuous
  have s0 : 0≤s := by linarith
  have hD : IntervalIntegrable c.dissipation volume s t := (c.dissipation_continuousOn.mono (show Icc s t ⊆ Ici (0:ℝ) from
    fun _ hx => s0.trans hx.1)).intervalIntegrable_of_Icc hst
  have ch : ∀x∈Icc s t, c.localizationDensity x≤b+A/b^2*c.dissipation x := by
    intro x hx
    have x1 := hs.trans hx.1
    have dn := c.dissipation_nonneg x
    have age := c.energy_le_of_le hf (by norm_num : (0:ℝ)≤1) x1
    have cube : c.localizationDensity x^3 ≤ A*c.dissipation x := by
      rw [c.localizationDensity_cube x1]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left age (by norm_num)) dn
    have r := c.localizationDensity_nonneg x
    have bd : c.localizationDensity x * b^2 ≤ b*b^2+c.localizationDensity x^3 := by
      rcases le_total (c.localizationDensity x) b with h|h
      · nlinarith only [mul_le_mul_of_nonneg_right h (sq_nonneg b),pow_nonneg r 3]
      · have p := pow_le_pow_left₀ hb.le h 2
        nlinarith only [mul_le_mul_of_nonneg_left p r, pow_nonneg hb.le 3]
    calc
      _ ≤ (b*b^2+A*c.dissipation x)/b^2 := (le_div_iff₀ (by positivity)).mpr (by linarith only [bd,cube])
      _ = _ := by field_simp
  have cmp := intervalIntegral.integral_mono_on (μ:=volume) hst (hc.intervalIntegrable _ _)
    (intervalIntegrable_const.add (hD.const_mul (A/b^2))) ch
  simp only [intervalIntegral.integral_add intervalIntegrable_const
    (hD.const_mul (A/b^2)),intervalIntegral.integral_const,smul_eq_mul,
    intervalIntegral.integral_const_mul] at cmp
  have law := c.energy_add_integral_dissipation hf s0 hst
  have add : (∫x in 1..s,c.localizationDensity x)+(∫x in s..t,c.localizationDensity x)=
      ∫x in 1..t,c.localizationDensity x :=
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 1 s) (hc.intervalIntegrable s t)
  dsimp [localizationClock]
  rw [←add]
  dsimp only [A] at cmp
  linarith only [cmp,congrArg (fun z => (16777216*c.energy 1/b^2)*z) law]

theorem localizationClock_subquadratic (hf : c.IsNormalFEF) :
    Tendsto (fun t => c.localizationClock t/(localizationScale t)^2) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := 16777216*c.energy 1
  have ap : 0<A := by have := c.energy_pos (by norm_num : (0:ℝ)≤1); dsimp [A]; positivity
  let δ := (ε/4)^3/A
  have dp : 0<δ := by dsimp [δ]; positivity
  let S := c.energy '' Ici 1
  have sne : S.Nonempty := ⟨c.energy 1,1,mem_Ici.mpr le_rfl,rfl⟩
  have sb : BddBelow S := ⟨0,by rintro _ ⟨x,hx,rfl⟩; exact (c.energy_pos (by change 1≤x at hx; linarith)).le⟩
  obtain ⟨_,⟨s,hs,rfl⟩,near⟩ := exists_lt_of_csInf_lt sne (show sInf S<sInf S+δ by linarith)
  change 1≤s at hs
  have bbig : Tendsto (fun t => (localizationScale t)^2) atTop atTop :=
    (tendsto_pow_atTop (n:=2) (by norm_num)).comp localizationScale_grows
  have init := bbig.eventually_gt_atTop (4*c.localizationClock s/ε)
  filter_upwards [init,eventually_ge_atTop s] with t large hst
  let r := localizationScale t
  have tp : 0<t := by linarith
  have rp : 0<r := Real.rpow_pos_of_pos tp _
  have rt : r^3=t := localizationScale_cube tp.le
  have loss : c.energy s-c.energy t≤δ := by
    have low := csInf_le sb (show c.energy t∈S from ⟨t,hs.trans hst,rfl⟩)
    linarith
  let b := (ε/4)/r
  have bp : 0<b := by dsimp [b]; positivity
  have rr := c.clock_restart hf hs hst bp
  change c.localizationClock t≤c.localizationClock s+b*(t-s)+A/b^2*(c.energy s-c.energy t) at rr
  have budget := mul_le_mul_of_nonneg_left loss (show 0≤A/b^2 by positivity)
  have ls : A/b^2*δ=(ε/4)*r^2 := by dsimp [δ,b]; field_simp
  rw [ls] at budget
  have bt : b*t=(ε/4)*r^2 := by rw [←rt]; dsimp [b]; field_simp
  have fi : 4*c.localizationClock s<r^2*ε := (div_lt_iff₀ hε).mp large
  have nn : 0≤c.localizationClock t := intervalIntegral.integral_nonneg_of_forall (hs.trans hst) c.localizationDensity_nonneg
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg nn (sq_nonneg _))]
  apply (div_lt_iff₀ (by positivity : 0<r^2)).mpr
  nlinarith only [rr,budget,bt,fi,mul_nonneg bp.le (show 0≤s by linarith),mul_pos hε (sq_pos_of_pos rp)]

end ForwardImmersion
end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.localizationClock_subquadratic
