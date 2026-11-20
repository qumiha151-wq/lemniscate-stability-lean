import LengthGrowth.ActualFlow.SharpVirial
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

def enclosingRadii : Set ℝ :=
  {r | ∃z : ℂ, ∀s∈Icc 0 c.period, ‖c.curve s-z‖≤r}

/-- The infimum over all radii of disks containing one full period. -/
def circumradius : ℝ := sInf c.enclosingRadii

theorem disk_controls (z : ℂ) {r : ℝ} (cover : ∀s∈Icc 0 c.period, ‖c.curve s-z‖≤r) :
    c.energy≤2*c.dissipation*r^4 ∧ 1≤c.energy*r := by
  let p:=fun s => inner ℝ (c.normal s) (c.curve s-z)
  have hc : Continuous c.curve := continuous_iff_continuousAt.mpr (fun s => (c.curve_deriv s).continuousAt)
  have hn : Continuous c.normal := continuous_iff_continuousAt.mpr (fun s => (c.normal_deriv s).continuousAt)
  have hp : Continuous p := hn.inner (hc.sub continuous_const)
  have kt:=c.curvature_continuous.mul hp
  have hD (s : ℝ) : HasDerivAt (fun x => inner ℝ (c.tangent x) (c.curve x-z))
      (c.curvature s*p s+1) s := by
    apply ((c.tangent_deriv s).inner ℝ ((c.curve_deriv s).sub_const z)).congr_deriv
    rw [←Complex.real_smul,real_inner_smul_left,real_inner_self_eq_norm_sq,c.tangent_unit]
    simp [p,normal,add_comm]
  have per:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun s _ => hD s) ((kt.add continuous_const).intervalIntegrable _ _)
  have tt := c.tangent_periodic 0
  have xx := c.curve_periodic 0
  rw [zero_add] at tt xx
  rw [tt,xx,sub_self,intervalIntegral.integral_add (f:=fun s => c.curvature s*p s)
    (g:=fun _ => (1:ℝ)) (kt.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _),intervalIntegral.integral_const] at per
  have kvir : (∫s in 0..c.period,c.curvature s*p s) = -c.period := by
    simpa [sub_zero,smul_eq_mul] using (eq_neg_of_add_eq_zero_left per)
  have fvir:=c.centered_dilation_virial z
  have kk:=interval_integral_mul_sq_le c.curvature_continuous hp c.period_pos.le
  have ff:=interval_integral_mul_sq_le c.force_continuous hp c.period_pos.le
  change (∫s in 0..c.period,c.force s*p s)^2 ≤ c.dissipation*(∫s in 0..c.period,p s^2) at ff
  rw [fvir,neg_sq] at ff
  rw [kvir,neg_sq] at kk
  have ek : (∫s in 0..c.period,c.curvature s^2)=2*c.energy := by
    unfold energy
    ring
  rw [ek] at kk
  have ps : (∫s in 0..c.period,p s^2) ≤ c.period*r^2 := by
    calc
      _ ≤ ∫s in 0..c.period,r^2 := by
        apply intervalIntegral.integral_mono_on c.period_pos.le ((hp.pow 2).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        intro s hs
        have a:=abs_real_inner_le_norm (c.normal s) (c.curve s-z)
        rw [c.normal_unit,one_mul] at a
        change p s^2≤r^2
        rw [←sq_abs (p s)]
        exact pow_le_pow_left₀ (abs_nonneg _) (a.trans (cover s hs)) 2
      _ = _ := by simp [smul_eq_mul]
  have dn : 0≤c.dissipation := intervalIntegral.integral_nonneg_of_forall c.period_pos.le (fun s => sq_nonneg _)
  have lp:=c.period_pos
  have ep:=c.energy_pos
  have len : c.period≤2*c.energy*r^2 := by
    apply (mul_le_mul_iff_left₀ lp).mp
    nlinarith only [kk,mul_le_mul_of_nonneg_left ps (by positivity : 0≤2*c.energy)]
  have rate : c.energy≤2*c.dissipation*r^4 := by
    apply (mul_le_mul_iff_left₀ ep).mp
    nlinarith only [ff,mul_le_mul_of_nonneg_left ps dn,
      mul_le_mul_of_nonneg_left len (mul_nonneg dn (sq_nonneg r))]
  have rp : 0≤r := (norm_nonneg _).trans (cover 0 ⟨le_rfl,lp.le⟩)
  have es:=c.sharp_energy_length
  have high : 1≤(c.energy*r)^2 := by
    nlinarith only [es,Real.pi_gt_three,mul_le_mul_of_nonneg_left len ep.le,
      sq_nonneg (Real.pi-1)]
  refine ⟨rate,?_⟩
  by_contra! bad
  nlinarith only [high,mul_pos (sub_pos.mpr bad)
    (show 0<1+c.energy*r by positivity)]

theorem circumradius_controls : c.energy≤2*c.dissipation*c.circumradius^4 ∧
    1≤c.energy*c.circumradius := by
  have hc : Continuous c.curve := continuous_iff_continuousAt.mpr (fun s => (c.curve_deriv s).continuousAt)
  obtain ⟨v,_,mx⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr c.period_pos.le)
    hc.norm.continuousOn
  have ne : c.enclosingRadii.Nonempty := ⟨‖c.curve v‖,0,fun s hs => by simpa using mx hs⟩
  have bd : BddBelow c.enclosingRadii := ⟨0,fun r ⟨z,hz⟩ =>
    (norm_nonneg _).trans (hz 0 ⟨le_rfl,c.period_pos.le⟩)⟩
  have closed : IsClosed {r : ℝ | c.energy ≤ 2*c.dissipation*r^4 ∧ 1≤c.energy*r} :=
    (isClosed_le continuous_const (continuous_const.mul (continuous_id.pow 4))).inter
      (isClosed_le continuous_const (continuous_const.mul continuous_id))
  have sub : c.enclosingRadii ⊆ {r : ℝ | c.energy≤2*c.dissipation*r^4 ∧ 1≤c.energy*r} :=
    fun _ ⟨z,cover⟩ => c.disk_controls z cover
  exact (closed.closure_subset_iff.mpr sub) (csInf_mem_closure ne bd)

end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.circumradius_controls
