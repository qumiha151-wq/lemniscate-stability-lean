import Migration.MaterialAngleAtSupport
import Migration.EndpointEnergyTransit
import Migration.EndpointMass
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private theorem width_half_length (H : ℂ→L[ℝ] ℝ) (op : ‖H‖≤1) {t : ℝ} (ht : t∈I)
    {u v : ℝ} (hu : u∈Icc 0 c.period) (hv : v∈Icc 0 c.period) :
    2*|H (c.position t v)-H (c.position t u)|≤∫s in (0:ℝ)..c.period,speed (c.position t) s := by
  have ord {a b : ℝ} (x : 0≤a) (y : a≤b) (z : b≤c.period) :=
    c.two_arcs_pay_height_primitive H op (fun _=>1) continuous_const (fun _=>zero_le_one)
      id (fun r=>hasDerivAt_id r) ht x y z
  rcases le_total u v with h|h
  · simpa only [id_eq,cutoffMass,one_mul] using ord hu.1 h hv.2
  · simpa only [id_eq,cutoffMass,one_mul,abs_sub_comm (H (c.position t u))] using ord hv.1 h hu.2

/-- The positive half-plane moment cost in the actual material parameter.
The center label, tangent angle, arclength coordinate, and energy all come
from the input curve. -/
theorem true_far_moment {t : ℝ} (ht : t∈I) (e : ℂ) (he : ‖e‖=1)
    (a : ℝ) (side : ∀u,a ≤ inner ℝ e (c.position t u)) :
    8/(3*(c.bending t)^2) ≤ ∫u in (0:ℝ)..c.period,
      (inner ℝ e (c.position t u)-a) * |inner ℝ e (normal (c.position t) u)| * speed (c.position t) u := by
  let p : PeriodicRegularPosition := ⟨c.period,c.period_pos,c.position t,
    c.position_slice_smooth ht,c.periodic t ht,c.immersion t ht⟩
  let H := innerSL ℝ e
  let E := c.bending t
  have ep : 0<E := c.bending_pos_of_width ht
  have op : ‖H‖≤1 := by dsimp [H]; rw [innerSL_apply_norm,he]
  obtain ⟨lo,hi,⟨range,⟨b,hb,low⟩,⟨j,hj,high⟩⟩,en⟩ := c.directional_width_range ht e he
  have wd : 2/E≤hi-lo := (div_le_iff₀ ep).mpr (by change 2≤(hi-lo)*c.bending t; linarith only [en])
  have wp : 0≤hi-lo := (div_nonneg (by norm_num) ep.le).trans wd
  have len := c.width_half_length H op ht hb hj
  change 2*|H (p.position j)-H (p.position b)|≤p.length at len
  change H (p.position j)=hi at high
  change H (p.position b)=lo at low
  rw [high,low,abs_of_nonneg wp] at len
  have maxall (u : ℝ) : H (p.position u)≤H (p.position j) := by
    obtain ⟨v,hv,eq⟩ := p.periodic.exists_mem_Ico₀ p.period_pos u
    rw [high,eq]; exact (range v ⟨hv.1,hv.2.le⟩).2
  have extr : IsLocalMax (fun u=>H (p.position u)) j := Eventually.of_forall maxall
  have hd : HasDerivAt (fun u=>H (p.position u)) (speed p.position j*H (tangent p.position j)) j := by
    apply (H.hasFDerivAt.comp_hasDerivAt j (position_hasDerivAt p.smooth p.regular j)).congr_deriv
    rw [map_smul,smul_eq_mul]
  have hor : H (tangent p.position j)=0 :=
    (mul_eq_zero.mp (extr.hasDerivAt_eq_zero hd)).resolve_left (speed_pos p.regular j).ne'
  have norm : |H (normal p.position j)|=1 := by
    have eq := unit_projection_identity he (tangent p.position j)
    change (H (tangent p.position j))^2+(H (normal p.position j))^2=‖tangent p.position j‖^2 at eq
    rw [hor,tangent_unit p.regular] at eq
    nlinarith only [sq_abs (H (normal p.position j)),eq,abs_nonneg (H (normal p.position j))]
  let h := fun s=>H (p.position (p.label j s))-a
  have dh (s : ℝ) := (p.height_der H j s).sub_const a
  have unit (s : ℝ) : |H (tangent p.position (p.label j s))|≤1 := by
    simpa only [Real.norm_eq_abs,tangent_unit p.regular,mul_one] using
      (H.le_opNorm (tangent p.position (p.label j s))).trans (by rw [tangent_unit p.regular,mul_one]; exact op)
  have far : hi-lo≤h 0 := by
    dsimp only [h]; rw [p.label_zero,high]
    have lb : a≤lo := low ▸ side b
    linarith
  have pk := curvature_periodic p.smooth p.regular p.periodic
  have ck := (curvature_smooth p.smooth p.regular).continuous
  have ke := p.shifted_integral j (fun u=>(curvature p.position u)^2) (ck.pow 2)
    (fun s=>congrArg (fun z : ℝ=>z^2) (pk s))
  have budget : (∫s in -(p.length/2)..(p.length/2),(p.kAt j s)^2)≤2*E := by
    rw [show (∫s in -(p.length/2)..(p.length/2),(p.kAt j s)^2)=_ from ke]
    dsimp only [E,bending,p]; linarith
  have cap := MigrationGeometry.AngularExcursion.halfplane_moment (L:=p.length/2) (E:=E) (W:=hi-lo) (h:=h)
    ep (by linarith only [len,wd]) wd (p.angleAt_der j) (p.kAt_cont j) (by simp [PeriodicRegularPosition.angleAt])
    dh unit (fun s=>sub_nonneg.mpr (side (p.label j s))) far budget
  let F := fun u=>(H (p.position u)-a)*|H (normal p.position u)|
  have cn := (normal_smooth p.smooth p.regular).continuous
  have cont : Continuous F := ((H.continuous.comp p.smooth.continuous).sub continuous_const).mul
    (H.continuous.comp cn).abs
  have per : Function.Periodic F p.period := by
    intro s; dsimp only [F]; rw [p.periodic s,normal_periodic p.smooth p.periodic s]
  have eqF (s : ℝ) : F (p.label j s)=h s*|Real.cos (p.angleAt j s)| := by
    dsimp only [F,h]
    rw [p.normal_angle H j hor s,abs_mul,norm,one_mul]
  have chg := p.shifted_integral j F cont per
  simp_rw [eqF] at chg
  rw [chg] at cap
  change _≤∫u in (0:ℝ)..p.period,F u*speed p.position u
  apply le_trans _ cap
  change 8/(3*E^2)≤2*(hi-lo)/E-4/(3*E^2)
  have z := (div_le_iff₀ ep).mp wd
  field_simp [ep.ne']; nlinarith only [z]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
