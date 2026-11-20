import Migration.NearRoundEnergy
import Migration.DirectionalWidth

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private theorem disk_integral_sq {P R : ℝ} {g f h : ℝ → ℝ}
    (hP : 0≤P) (hR : 0≤R) (cg : Continuous g) (cf : Continuous f) (ch : Continuous h)
    (gp : ∀u, 0≤g u) (cover : ∀u ∈ Icc 0 P, |h u|≤R) :
    (∫ u in 0..P, g u*f u*h u)^2 ≤
      R^2*(∫ u in 0..P, g u)*(∫ u in 0..P, f u^2*g u) := by
  have hw := weighted_abs_force (v := fun _ => 1) hP continuous_const cf cg gp
  simp only [abs_one,one_pow,one_mul] at hw
  have h1 := (intervalIntegral.abs_integral_le_integral_abs
    (μ := volume) (f := fun u => g u*f u*h u) hP)
  have h2 : (∫ u in 0..P, |g u*f u*h u|) ≤ ∫ u in 0..P, R*(|f u| * g u) := by
    apply intervalIntegral.integral_mono_on hP (((cg.mul cf).mul ch).abs.intervalIntegrable _ _)
      (((cf.abs.mul cg).const_mul R).intervalIntegrable _ _)
    intro u hu
    change |g u*f u*h u| ≤ R*(|f u| * g u)
    rw [abs_mul,abs_mul,abs_of_nonneg (gp u)]
    nlinarith [mul_le_mul_of_nonneg_left (cover u hu) (mul_nonneg (gp u) (abs_nonneg (f u)))]
  rw [intervalIntegral.integral_const_mul] at h2
  have h3 := (h1.trans h2).trans (mul_le_mul_of_nonneg_left hw hR)
  have sq := pow_le_pow_left₀ (abs_nonneg _) h3 2
  rw [sq_abs,mul_pow,mul_pow,
    Real.sq_sqrt (intervalIntegral.integral_nonneg_of_forall hP gp),
    Real.sq_sqrt (intervalIntegral.integral_nonneg_of_forall hP
      (fun u => mul_nonneg (sq_nonneg (f u)) (gp u)))] at sq
  linarith

private theorem material_length_virial {t : ℝ} (ht : t∈I) (z : ℂ) :
    (∫ u in 0..c.period, speed (c.position t) u * curvature (c.position t) u *
      inner ℝ (normal (c.position t) u) (c.position t u-z)) = -c.coreLength t := by
  let γ := c.position t
  let Q := fun u => inner ℝ (tangent γ u) (γ u-z)
  let w := fun u => speed γ u * curvature γ u * inner ℝ (normal γ u) (γ u-z)
  have hs := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have cg := (speed_smooth hs hr).continuous
  have cw : Continuous w := ((cg.mul (curvature_smooth hs hr).continuous).mul
    ((normal_smooth hs hr).continuous.inner (hs.continuous.sub continuous_const)))
  have hd (u : ℝ) : HasDerivAt Q (w u+speed γ u) u := by
    have hh := (tangent_hasDerivAt hs hr u).inner ℝ ((position_hasDerivAt hs hr u).sub_const z)
    apply hh.congr_deriv
    change inner ℝ (tangent γ u) (speed γ u • tangent γ u) +
      inner ℝ ((((speed γ u*curvature γ u : ℝ) : ℂ))*normal γ u) (γ u-z) = _
    rw [←Complex.real_smul,real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
      tangent_unit hr]
    simp [w,add_comm]
  have it := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun u _ => hd u) ((cw.add cg).intervalIntegrable _ _)
  have per := c.periodic t ht
  have pt : Function.Periodic (tangent γ) c.period := tangent_periodic hs per
  have ends : Q c.period=Q 0 := by
    change inner ℝ (tangent γ c.period) (c.position t c.period-z)=_
    rw [show tangent γ c.period=tangent γ 0 by simpa using pt 0,
      show c.position t c.period=c.position t 0 by simpa using per 0]
  rw [ends,sub_self,intervalIntegral.integral_add (cw.intervalIntegrable _ _)
    (cg.intervalIntegrable _ _)] at it
  change (∫ u in 0..c.period, w u) = -(∫ u in 0..c.period, speed γ u)
  linarith

/-- A disk surrounding this one slice forces a minimum instantaneous
dissipation. Its center is completely arbitrary. -/
theorem containing_disk_dissipation {t R : ℝ} (ht : t∈I) (hR : 0<R) (z : ℂ)
    (cover : ∀u∈Icc 0 c.period, ‖c.position t u-z‖ ≤ R) :
    1 ≤ 2*R^5*c.localDissipation Complex.reCLM (fun _ => 1) t := by
  let γ := c.position t
  let D := c.localDissipation Complex.reCLM (fun _ => 1) t
  let E := c.bending t
  let L := c.coreLength t
  let h := fun u => inner ℝ (normal γ u) (γ u-z)
  have hs := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have gp u := (speed_pos hr u).le
  have cg := (speed_smooth hs hr).continuous
  have ch : Continuous h := (normal_smooth hs hr).continuous.inner (hs.continuous.sub continuous_const)
  have hb (u : ℝ) (hu : u∈Icc 0 c.period) : |h u|≤R := by
    apply (abs_real_inner_le_norm _ _).trans
    rw [show ‖normal γ u‖=1 from normal_unit hr u,one_mul]
    exact cover u hu
  have v := disk_integral_sq c.period_pos.le hR.le cg (force_smooth hs hr).continuous ch gp hb
  have k := disk_integral_sq c.period_pos.le hR.le cg (curvature_smooth hs hr).continuous ch gp hb
  have hv := c.material_virial ht z
  have hk := c.material_length_virial ht z
  change (∫ u in 0..c.period, speed γ u*force γ u*h u) = -E at hv
  change (∫ u in 0..c.period, speed γ u*curvature γ u*h u) = -L at hk
  rw [hv,neg_sq] at v
  rw [hk,neg_sq] at k
  have hd : (∫ u in 0..c.period, force γ u^2*speed γ u)=D := by simp [D,γ,localDissipation]
  have he : (∫ u in 0..c.period, curvature γ u^2*speed γ u)=2*E := by dsimp [E,bending,γ]; ring
  rw [hd] at v
  rw [he] at k
  change E^2≤R^2*L*D at v
  change L^2≤R^2*L*(2*E) at k
  have hL : 0<L := c.coreLength_pos ht
  have hE : 0<E := c.bending_pos_of_width ht
  have Len : L ≤ 2*E*R^2 := by
    by_contra! bad
    nlinarith only [k,mul_pos hL (sub_pos.mpr bad)]
  have Dp : 0≤D := by
    rw [←hd]
    exact intervalIntegral.integral_nonneg_of_forall c.period_pos.le (fun u => mul_nonneg (sq_nonneg _) (gp u))
  have Ed : E≤2*R^4*D := by
    by_contra! bad
    nlinarith only [v,mul_le_mul_of_nonneg_right Len (mul_nonneg (sq_nonneg R) Dp),
      mul_pos hE (sub_pos.mpr bad)]
  obtain ⟨lo,hi,range,wide⟩ := c.directional_width_range ht (1:ℂ) (by simp)
  obtain ⟨_,⟨u,hu,eu⟩,⟨v,hv,ev⟩⟩ := range
  have dist_bound (s : ℝ) (hs : s∈Icc 0 c.period) :
      |inner ℝ (1:ℂ) (c.position t s-z)|≤R :=
    (abs_real_inner_le_norm _ _).trans (by simpa using cover s hs)
  have b1 := (abs_le.mp (dist_bound u hu)).1
  have b2 := (abs_le.mp (dist_bound v hv)).2
  rw [inner_sub_right] at b1 b2
  change inner ℝ (1:ℂ) (c.position t u)=lo at eu
  change inner ℝ (1:ℂ) (c.position t v)=hi at ev
  have width : hi-lo≤2*R := by linarith
  change 2≤E*(hi-lo) at wide
  change 1≤2*R^5*D
  nlinarith only [wide,mul_le_mul_of_nonneg_left width hE.le,
    mul_le_mul_of_nonneg_right Ed hR.le]

/-- A radius cap on every slice costs an explicit amount of energy per
unit of physical time, even if the containing disk moves arbitrarily. -/
theorem containing_disk_window (hf : c.IsNormalFEF) {s t R : ℝ}
    (hst : s≤t) (hslab : Icc s t ⊆ I) (hR : 0<R)
    (cap : ∀v∈Icc s t, ∃z : ℂ, ∀u∈Icc 0 c.period, ‖c.position v u-z‖≤R) :
    t-s ≤ 2*R^5*(c.bending s-c.bending t) := by
  let D := c.localDissipation Complex.reCLM (fun _ => 1)
  have hi : IntervalIntegrable D volume s t :=
    ((c.localDissipation_continuousOn Complex.reCLM continuous_const).mono hslab).intervalIntegrable_of_Icc hst
  have hb : (∫ v in s..t, (1:ℝ)) ≤ ∫ v in s..t, (2*R^5)*D v := by
    apply intervalIntegral.integral_mono_on hst intervalIntegrable_const (hi.const_mul _)
    intro v hv
    obtain ⟨z,hz⟩ := cap v hv
    exact c.containing_disk_dissipation (hslab hv) hR z hz
  rw [intervalIntegral.integral_const,intervalIntegral.integral_const_mul,
    show (∫ v in s..t, D v)=c.bending s-c.bending t from
      c.full_dissipation_eq_bending_drop hf Complex.reCLM hst hslab] at hb
  simpa using hb

/-- On arbitrarily late slices, no disk of the prescribed radius contains
the curve. No assumption on the centre or asymptotic shape is made. -/
theorem escapes_all_fixed_radii (hf : c.IsNormalFEF) (dom : Ioi (0:ℝ) ⊆ I)
    (T : ℝ) {R : ℝ} (hR : 0<R) :
    ∃t : ℝ, T<t ∧ 0<t ∧ ∀z : ℂ, ∃u∈Icc 0 c.period, R < ‖c.position t u-z‖ := by
  by_contra! bound
  let s := max T 0+1
  let t := s+2*R^5*c.bending s+1
  have hs : 0<s := by dsimp [s]; linarith [le_max_right T 0]
  have late : T<s := by dsimp [s]; linarith [le_max_left T 0]
  have hst : s≤t := by dsimp [t]; linarith [mul_nonneg (by positivity : 0≤2*R^5) (c.bending_nonneg s)]
  have h := c.containing_disk_window hf hst (fun _ hv => dom (hs.trans_le hv.1)) hR
    (fun v hv => bound v (late.trans_le hv.1) (hs.trans_le hv.1))
  dsimp [t] at h
  linarith [mul_nonneg (by positivity : 0≤2*R^5) (c.bending_nonneg t)]

#print axioms containing_disk_window
#print axioms escapes_all_fixed_radii

end MigrationGeometry.Flow.SmoothPeriodicImmersion
