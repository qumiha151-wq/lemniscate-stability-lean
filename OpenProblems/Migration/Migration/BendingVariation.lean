import Migration.TwoEndpointCost
import Mathlib.Tactic.LinearCombination

/-! Spatial bending-energy variation and normal energy balance for the
position-defined flow. The spatial and mixed-derivative proofs reuse
IntrinsicCurve, SpatialPeriodicity, PeriodicIntegration, SpatialFirstVariation,
FamilyPeriodicity, FamilyDerivatives, CompactParameterIntegral and CurveFirstVariation. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ComplexConjugate Topology Interval
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow
section
variable {γ : ℝ → ℂ}
theorem arcDerivative_tangent (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    arcDerivative γ (tangent γ) u = curvature γ u • normal γ u := by
  rw [arcDerivative, (tangent_hasDerivAt hγ hreg u).deriv]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
  field_simp [(speed_pos hreg u).ne']

theorem arcDerivative_normal (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    arcDerivative γ (normal γ) u = -(curvature γ u) • tangent γ u := by
  rw [arcDerivative, (normal_hasDerivAt hγ hreg u).deriv]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_neg]
  field_simp [(speed_pos hreg u).ne']

theorem curvature_eq_inner_arcDerivative (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    curvature γ u = inner ℝ (arcDerivative γ (tangent γ) u) (normal γ u) := by
  rw [arcDerivative_tangent hγ hreg, real_inner_smul_left,
    real_inner_self_eq_norm_sq, normal_unit hreg]
  simp

theorem curvature_hasDerivAt (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) : HasDerivAt (curvature γ)
      (speed γ u * curvatureGradient γ u) u :=
  hasDerivAt_speed_smul_arcDerivative hreg
    ((curvature_smooth hγ hreg).differentiable (by simp)) u

theorem curvatureGradient_hasDerivAt (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) : HasDerivAt (curvatureGradient γ)
      (speed γ u * curvatureSecond γ u) u :=
  hasDerivAt_speed_smul_arcDerivative hreg
    ((curvatureGradient_smooth hγ hreg).differentiable (by simp)) u

/-- The actual material derivative of stress includes the actual speed. -/
theorem stress_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (u : ℝ) : HasDerivAt (stress γ)
      (((speed γ u * force γ u : ℝ) : ℂ) * normal γ u) u := by
  have hk := (curvature_hasDerivAt hγ hreg u).ofReal_comp
  have hk₁ := (curvatureGradient_hasDerivAt hγ hreg u).ofReal_comp
  have hd := HasDerivAt.add
    (HasDerivAt.mul (HasDerivAt.div_const (HasDerivAt.mul hk hk) 2)
      (tangent_hasDerivAt hγ hreg u))
    (HasDerivAt.mul hk₁ (normal_hasDerivAt hγ hreg u))
  convert! hd using 1
  · funext s
    simp [stress, pow_two]
  · simp only [force, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Pi.mul_apply]
    ring

/-- The intrinsic arclength stress identity, with no supplied Frenet data. -/
theorem arcDerivative_stress (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (u : ℝ) : arcDerivative γ (stress γ) u = (force γ u : ℂ) * normal γ u := by
  rw [arcDerivative, (stress_hasDerivAt hγ hreg u).deriv]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
  field_simp [(speed_pos hreg u).ne']

theorem stress_smooth (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0) :
    ContDiff ℝ ∞ (stress γ) := by
  exact ((((Complex.ofRealCLM.contDiff.comp (curvature_smooth hγ hreg)).pow 2).div_const 2).mul
    (tangent_smooth hγ hreg)).add
    ((Complex.ofRealCLM.contDiff.comp (curvatureGradient_smooth hγ hreg)).mul
      (normal_smooth hγ hreg))
end

theorem actual_deriv_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {P : ℝ} (hp : Function.Periodic f P) (hf : Differentiable ℝ f) :
    Function.Periodic (deriv f) P := by
  intro u
  have hd := (hf (u+P)).hasDerivAt.scomp u ((hasDerivAt_id u).add_const P)
  have he : (fun s => f (s+P)) = f := funext hp
  simp only [one_smul] at hd
  change HasDerivAt (fun s => f (s+P)) (deriv f (u+P)) u at hd
  rw [he] at hd
  exact hd.unique (hf u).hasDerivAt

variable {γ : ℝ → ℂ} {P : ℝ}

theorem speed_periodic (hγ : ContDiff ℝ ∞ γ) (hp : Function.Periodic γ P) :
    Function.Periodic (speed γ) P := by
  have hd := actual_deriv_periodic hp (hγ.differentiable (by simp))
  intro u
  simp only [speed, hd u]

theorem arcDerivative_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hγ : ContDiff ℝ ∞ γ) (hp : Function.Periodic γ P)
    {f : ℝ → E} (hf : Differentiable ℝ f) (hfp : Function.Periodic f P) :
    Function.Periodic (arcDerivative γ f) P := by
  have hg := speed_periodic hγ hp
  have hd := actual_deriv_periodic hfp hf
  intro u
  simp only [arcDerivative, hg u, hd u]

theorem tangent_periodic (hγ : ContDiff ℝ ∞ γ) (hp : Function.Periodic γ P) :
    Function.Periodic (tangent γ) P :=
  arcDerivative_periodic hγ hp (hγ.differentiable (by simp)) hp

theorem normal_periodic (hγ : ContDiff ℝ ∞ γ) (hp : Function.Periodic γ P) :
    Function.Periodic (normal γ) P := by
  have ht := tangent_periodic hγ hp
  intro u
  simp only [normal, ht u]

theorem curvature_periodic (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (hp : Function.Periodic γ P) : Function.Periodic (curvature γ) P := by
  have ht := tangent_periodic hγ hp
  have hdt := actual_deriv_periodic ht ((tangent_smooth hγ hreg).differentiable (by simp))
  have hg := speed_periodic hγ hp
  intro u
  simp only [curvature, ht u, hdt u, hg u]

theorem curvatureGradient_periodic (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (hp : Function.Periodic γ P) :
    Function.Periodic (curvatureGradient γ) P :=
  arcDerivative_periodic hγ hp ((curvature_smooth hγ hreg).differentiable (by simp))
    (curvature_periodic hγ hreg hp)

theorem curvatureSecond_periodic (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (hp : Function.Periodic γ P) :
    Function.Periodic (curvatureSecond γ) P :=
  arcDerivative_periodic hγ hp ((curvatureGradient_smooth hγ hreg).differentiable (by simp))
    (curvatureGradient_periodic hγ hreg hp)

theorem force_periodic (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (hp : Function.Periodic γ P) : Function.Periodic (force γ) P := by
  have hk := curvature_periodic hγ hreg hp
  have hk₂ := curvatureSecond_periodic hγ hreg hp
  intro u
  simp only [force, hk u, hk₂ u]

theorem stress_periodic (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (hp : Function.Periodic γ P) : Function.Periodic (stress γ) P := by
  have ht := tangent_periodic hγ hp
  have hn := normal_periodic hγ hp
  have hk := curvature_periodic hγ hreg hp
  have hk₁ := curvatureGradient_periodic hγ hreg hp
  intro u
  simp only [stress, ht u, hn u, hk u, hk₁ u]



section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem periodic_inner_integration_by_parts {f g : ℝ → E} {P : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f P) (hgp : Function.Periodic g P) :
    (∫ u in 0..P, inner ℝ (f u) (deriv g u)) =
      -(∫ u in 0..P, inner ℝ (deriv f u) (g u)) := by
  have hf' := (contDiff_infty_iff_deriv.mp hf).2.continuous
  have hg' := (contDiff_infty_iff_deriv.mp hg).2.continuous
  have hi₁ : IntervalIntegrable (fun u => inner ℝ (deriv f u) (g u)) volume 0 P :=
    (hf'.inner hg.continuous).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun u => inner ℝ (f u) (deriv g u)) volume 0 P :=
    (hf.continuous.inner hg').intervalIntegrable _ _
  have hd (u : ℝ) : HasDerivAt (fun x => inner ℝ (f x) (g x))
      (inner ℝ (deriv f u) (g u) + inner ℝ (f u) (deriv g u)) u :=
    by simpa only [add_comm] using
      ((hf.differentiable (by simp) u).hasDerivAt).inner ℝ
        ((hg.differentiable (by simp) u).hasDerivAt)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hd u) (hi₁.add hi₂)
  have hfe : f P = f 0 := by simpa using hfp 0
  have hge : g P = g 0 := by simpa using hgp 0
  rw [hfe, hge, sub_self, intervalIntegral.integral_add hi₁ hi₂] at h
  linarith

theorem periodic_mul_integration_by_parts {f g : ℝ → ℝ} {P : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f P) (hgp : Function.Periodic g P) :
    (∫ u in 0..P, f u * deriv g u) = -(∫ u in 0..P, deriv f u * g u) := by
  simpa only [Real.inner_apply] using
    periodic_inner_integration_by_parts hf hg hfp hgp
end

section
variable {γ V : ℝ → ℂ} {P : ℝ}

theorem stress_spatial_first_variation
    (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (hp : Function.Periodic γ P) (hV : ContDiff ℝ ∞ V)
    (hVp : Function.Periodic V P) :
    -(∫ u in 0..P, inner ℝ (stress γ u) (deriv V u)) =
      ∫ u in 0..P, speed γ u * force γ u * inner ℝ (normal γ u) (V u) := by
  rw [periodic_inner_integration_by_parts (stress_smooth hγ hreg) hV
    (stress_periodic hγ hreg hp) hVp, neg_neg]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [(stress_hasDerivAt hγ hreg u).deriv, ← Complex.real_smul, real_inner_smul_left]

theorem stress_inner_actual_velocity_derivative
    (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    inner ℝ (stress γ u) (deriv V u) =
      deriv (curvature γ) u * inner ℝ (arcDerivative γ V u) (normal γ u) +
      curvature γ u ^ 2 / 2 * inner ℝ (deriv V u) (tangent γ u) := by
  have hs : stress γ u = (curvature γ u ^ 2 / 2) • tangent γ u +
      curvatureGradient γ u • normal γ u := by
    simp only [stress, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_ofNat]
  rw [hs, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    (curvature_hasDerivAt hγ hreg u).deriv, arcDerivative, real_inner_smul_left]
  rw [real_inner_comm (tangent γ u) (deriv V u),
    real_inner_comm (normal γ u) (deriv V u)]
  field_simp [(speed_pos hreg u).ne']
  ring

theorem energy_spatial_first_variation
    (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (hp : Function.Periodic γ P) (hV : ContDiff ℝ ∞ V)
    (hVp : Function.Periodic V P) :
    (∫ u in 0..P, curvature γ u *
        deriv (fun x => inner ℝ (arcDerivative γ V x) (normal γ x)) u -
        curvature γ u ^ 2 / 2 * inner ℝ (deriv V u) (tangent γ u)) =
      ∫ u in 0..P, speed γ u * force γ u * inner ℝ (normal γ u) (V u) := by
  let b : ℝ → ℝ := fun u => inner ℝ (arcDerivative γ V u) (normal γ u)
  have hb : ContDiff ℝ ∞ b :=
    (arcDerivative_smooth hγ hreg hV).inner ℝ (normal_smooth hγ hreg)
  have hbp : Function.Periodic b P := by
    have hd := arcDerivative_periodic hγ hp (hV.differentiable (by simp)) hVp
    have hn := normal_periodic hγ hp
    intro u
    dsimp [b]
    rw [hd u, hn u]
  have hk := curvature_smooth hγ hreg
  have hkd := (contDiff_infty_iff_deriv.mp hk).2.continuous
  have hbd := (contDiff_infty_iff_deriv.mp hb).2.continuous
  have hVd := (contDiff_infty_iff_deriv.mp hV).2.continuous
  have hT := (tangent_smooth hγ hreg).continuous
  have hi₁ : IntervalIntegrable (fun u => curvature γ u * deriv b u) volume 0 P :=
    (hk.continuous.mul hbd).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable
      (fun u => curvature γ u ^ 2 / 2 * inner ℝ (deriv V u) (tangent γ u)) volume 0 P :=
    (((hk.continuous.pow 2).div_const 2).mul (hVd.inner hT)).intervalIntegrable _ _
  have hi₃ : IntervalIntegrable (fun u => deriv (curvature γ) u * b u) volume 0 P :=
    (hkd.mul hb.continuous).intervalIntegrable _ _
  change (∫ u in 0..P, curvature γ u * deriv b u -
    curvature γ u ^ 2 / 2 * inner ℝ (deriv V u) (tangent γ u)) = _
  rw [intervalIntegral.integral_sub hi₁ hi₂,
    periodic_mul_integration_by_parts hk hb (curvature_periodic hγ hreg hp) hbp]
  calc
    _ = -(∫ u in 0..P, deriv (curvature γ) u * b u +
        curvature γ u ^ 2 / 2 * inner ℝ (deriv V u) (tangent γ u)) := by
      rw [intervalIntegral.integral_add hi₃ hi₂]
      ring
    _ = -(∫ u in 0..P, inner ℝ (stress γ u) (deriv V u)) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      exact (stress_inner_actual_velocity_derivative hγ hreg u).symm
    _ = _ := stress_spatial_first_variation hγ hreg hp hV hVp
end

theorem time_derivative_periodic_of_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Γ : ℝ → ℝ → E} {t P : ℝ}
    (hp : ∀ᶠ τ in 𝓝 t, Function.Periodic (Γ τ) P) :
    Function.Periodic (fun u => deriv (fun τ => Γ τ u) t) P := by
  intro u
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hp] with τ hτ
  exact hτ u

theorem time_derivative_periodic_of_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Set ℝ} {Γ : ℝ → ℝ → E} {t P : ℝ}
    (hI : IsOpen I) (hp : ∀ τ ∈ I, Function.Periodic (Γ τ) P) (ht : t ∈ I) :
    Function.Periodic (fun u => deriv (fun τ => Γ τ u) t) P := by
  apply time_derivative_periodic_of_eventually
  filter_upwards [hI.mem_nhds ht] with τ hτ
  exact hp τ hτ

namespace SmoothPeriodicImmersion

variable {I : Set ℝ} (c : SmoothPeriodicImmersion I) {t : ℝ}

theorem velocity_periodic (ht : t ∈ I) :
    Function.Periodic (c.velocity t) c.period :=
  time_derivative_periodic_of_open c.time_open c.periodic ht
end SmoothPeriodicImmersion

theorem complex_unit_frame_decomposition {T : ℂ} (hT : ‖T‖ = 1) (z : ℂ) :
    z = (inner ℝ z T) • T + (inner ℝ z (Complex.I * T)) • (Complex.I * T) := by
  have hu : T * conj T = 1 := by
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq, hT]
  have hc : (inner ℝ z T : ℂ) + (inner ℝ z (Complex.I * T) : ℂ) * Complex.I =
      conj T * z := by
    apply Complex.ext <;>
      simp only [Complex.inner, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
        Complex.conj_im, Complex.I_re, Complex.I_im] <;> ring
  simp only [Complex.real_smul]
  calc
    z = (conj T * z) * T := by calc
      _ = (T * conj T) * z := by rw [hu, one_mul]
      _ = _ := by ring
    _ = ((inner ℝ z T : ℂ) + (inner ℝ z (Complex.I * T) : ℂ) * Complex.I) * T :=
      congrArg (fun w : ℂ => w * T) hc.symm
    _ = _ := by ring

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem velocityGradientNormal_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => c.velocityGradientNormal z.1 z.2) (I ×ˢ (univ : Set ℝ)) :=
  (c.arcDerivative_joint_smooth c.velocity_joint_smooth).inner ℝ c.normal_joint_smooth

theorem velocity_space_decomposition {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    deriv (c.velocity t) u = speed (c.position t) u •
      (c.velocityGradientTangent t u • tangent (c.position t) u +
        c.velocityGradientNormal t u • normal (c.position t) u) := by
  have h := complex_unit_frame_decomposition (tangent_unit (c.immersion t ht) u)
    (arcDerivative (c.position t) (c.velocity t) u)
  change arcDerivative (c.position t) (c.velocity t) u =
    c.velocityGradientTangent t u • tangent (c.position t) u +
      c.velocityGradientNormal t u • normal (c.position t) u at h
  rw [← h, speed_smul_arcDerivative (c.immersion t ht)]

theorem tangent_time_hasDerivAt {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    HasDerivAt (fun x => tangent (c.position x) u)
      ((c.velocityGradientNormal t u : ℂ) * normal (c.position t) u) t := by
  have hg := c.speed_time_hasDerivAt ht u
  have hT := joint_smooth_time_hasDerivAt c.time_open
    (f := fun x => tangent (c.position x)) c.tangent_joint_smooth ht u
  have hp := hg.smul hT
  have heq : (fun x => deriv (c.position x) u) =ᶠ[𝓝 t]
      (fun x => speed (c.position x) u • tangent (c.position x) u) := by
    filter_upwards [c.time_open.mem_nhds ht] with x hx
    exact (position_hasDerivAt (c.position_slice_smooth hx) (c.immersion x hx) u).deriv
  have he := (hp.congr_of_eventuallyEq heq).unique (c.position_space_time_hasDerivAt ht u)
  rw [c.velocity_space_decomposition ht u] at he
  simp only [Complex.real_smul, Complex.ofReal_mul] at he
  have hdt : deriv (fun x => tangent (c.position x) u) t =
      (c.velocityGradientNormal t u : ℂ) * normal (c.position t) u := by
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (speed_pos (c.immersion t ht) u).ne')
    linear_combination he
  simpa only [hdt] using hT

/-- Rotation of the actual tangent gives the normal time derivative. -/
theorem normal_time_hasDerivAt {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    HasDerivAt (fun x => normal (c.position x) u)
      (-(c.velocityGradientNormal t u : ℂ) * tangent (c.position t) u) t := by
  have h := (c.tangent_time_hasDerivAt ht u).const_mul Complex.I
  have he : Complex.I * ((c.velocityGradientNormal t u : ℂ) * normal (c.position t) u) =
      -(c.velocityGradientNormal t u : ℂ) * tangent (c.position t) u := by
    dsimp [normal]
    calc
      _ = (Complex.I * Complex.I) *
        ((c.velocityGradientNormal t u : ℂ) * tangent (c.position t) u) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [he] at h
  exact h

/-- The actual curvature and metric derivatives satisfy the differentiated
Frenet identity. Its proof uses actual Schwarz symmetry for the tangent. -/
theorem curvature_metric_time_identity {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    speed (c.position t) u * deriv (fun x => curvature (c.position x) u) t +
      curvature (c.position t) u * deriv (fun x => speed (c.position x) u) t =
        deriv (c.velocityGradientNormal t) u := by
  have hg := joint_smooth_time_hasDerivAt c.time_open
    (f := fun x => speed (c.position x)) c.speed_joint_smooth ht u
  have hk := joint_smooth_time_hasDerivAt c.time_open
    (f := fun x => curvature (c.position x)) c.curvature_joint_smooth ht u
  have hN := c.normal_time_hasDerivAt ht u
  have hprod := ((hg.mul hk).ofReal_comp).mul hN
  have heq : (fun x => deriv (tangent (c.position x)) u) =ᶠ[𝓝 t]
      (fun x => ((speed (c.position x) u * curvature (c.position x) u : ℝ) : ℂ) *
        normal (c.position x) u) := by
    filter_upwards [c.time_open.mem_nhds ht] with x hx
    exact (tangent_hasDerivAt (c.position_slice_smooth hx) (c.immersion x hx) u).deriv
  have hst := hprod.congr_of_eventuallyEq heq
  have hb := ((joint_smooth_space_slice c.velocityGradientNormal_joint_smooth ht).differentiable
    (by simp) u).hasDerivAt
  have hNs := normal_hasDerivAt (c.position_slice_smooth ht) (c.immersion t ht) u
  have hts := hb.ofReal_comp.mul hNs
  have htime_eq : (fun y => deriv (fun x => tangent (c.position x) y) t) =
      (fun y => (c.velocityGradientNormal t y : ℂ) * normal (c.position t) y) := by
    funext y
    exact (c.tangent_time_hasDerivAt ht y).deriv
  have he :
      (((deriv (fun x => speed (c.position x) u) t * curvature (c.position t) u +
          speed (c.position t) u * deriv (fun x => curvature (c.position x) u) t : ℝ) : ℂ) *
        normal (c.position t) u +
        ((speed (c.position t) u * curvature (c.position t) u : ℝ) : ℂ) *
          (-(c.velocityGradientNormal t u : ℂ) * tangent (c.position t) u)) =
      ((deriv (c.velocityGradientNormal t) u : ℝ) : ℂ) * normal (c.position t) u +
        (c.velocityGradientNormal t u : ℂ) *
          (-((speed (c.position t) u * curvature (c.position t) u : ℝ) : ℂ) *
            tangent (c.position t) u) := by
    calc
      _ = deriv (fun x => deriv (tangent (c.position x)) u) t := hst.deriv.symm
      _ = deriv (fun y => deriv (fun x => tangent (c.position x) y) t) u :=
        actual_time_space_deriv_commute (f := fun x => tangent (c.position x))
          c.time_open c.tangent_joint_smooth ht u
      _ = _ := by rw [htime_eq]; exact hts.deriv
  have hn : normal (c.position t) u ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [normal_unit (c.immersion t ht)]
    norm_num
  have hz : (((speed (c.position t) u * deriv (fun x => curvature (c.position x) u) t +
      curvature (c.position t) u * deriv (fun x => speed (c.position x) u) t -
        deriv (c.velocityGradientNormal t) u : ℝ) : ℂ)) * normal (c.position t) u = 0 := by
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul] at he ⊢
    linear_combination he
  have hr := Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hn)
  linarith

/-- Rate form of the actual metric-curvature relation, convenient for the
first variation of the density kappa^2 g / 2. -/
theorem curvature_metric_rate_identity {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    speed (c.position t) u * deriv (fun x => curvature (c.position x) u) t +
      curvature (c.position t) u * (speed (c.position t) u * c.velocityGradientTangent t u) =
        deriv (c.velocityGradientNormal t) u := by
  simpa only [(c.speed_time_hasDerivAt ht u).deriv] using c.curvature_metric_time_identity ht u


end SmoothPeriodicImmersion

theorem hasDerivAt_intervalIntegral_of_jointC1 {I : Set ℝ}
    {F : ℝ → ℝ → ℝ} {a b t : ℝ} (hI : IsOpen I)
    (hF : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    (ht : t ∈ I) :
    HasDerivAt (fun x => ∫ u in a..b, F x u)
      (∫ u in a..b, deriv (fun x => F x u) t) t := by
  let D : ℝ → ℝ → ℝ := fun x u =>
    (fderiv ℝ (fun z : ℝ × ℝ => F z.1 z.2) (x, u)) (1, 0)
  have hD : ContinuousOn (fun z : ℝ × ℝ => D z.1 z.2)
      (I ×ˢ (univ : Set ℝ)) :=
    (hF.continuousOn_fderiv_of_isOpen (hI.prod isOpen_univ) le_rfl).clm_apply
      continuousOn_const
  have hd (x : ℝ) (hx : x ∈ I) (u : ℝ) :
      HasDerivAt (fun y => F y u) (D x u) x := by
    have hfd : DifferentiableAt ℝ (fun z : ℝ × ℝ => F z.1 z.2) (x, u) :=
      (hF.differentiableOn (by norm_num) (x, u) ⟨hx, mem_univ u⟩).differentiableAt
        ((hI.prod isOpen_univ).mem_nhds ⟨hx, mem_univ u⟩)
    have hp : HasDerivAt (fun y : ℝ => (y, u)) (1, 0) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x u)
    exact hfd.hasFDerivAt.comp_hasDerivAt x hp
  have hsub : I ×ˢ uIcc a b ⊆ I ×ˢ (univ : Set ℝ) :=
    fun _ hz => ⟨hz.1, mem_univ _⟩
  have hi := hasDerivAt_intervalIntegral_of_continuousOn hI
    (hF.continuousOn.mono hsub) (hD.mono hsub) (fun x hx u _ => hd x hx u) ht
  convert hi using 1
  apply intervalIntegral.integral_congr
  intro u _
  exact (hd t ht u).deriv

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def energy (t : ℝ) : ℝ := (1/2 : ℝ)*∫ u in 0..c.period, curvature (c.position t) u ^ 2 * speed (c.position t) u

theorem energy_hasDerivAt_actualTimeDerivative {t : ℝ} (ht : t ∈ I) :
    HasDerivAt c.energy ((1 / 2 : ℝ) *
      ∫ u in 0..c.period, deriv (fun x => curvature (c.position x) u ^ 2 *
        speed (c.position x) u) t) t :=
  (hasDerivAt_intervalIntegral_of_jointC1 (a := 0) (b := c.period) c.time_open
    (((c.curvature_joint_smooth.pow 2).mul c.speed_joint_smooth).of_le (by simp)) ht).const_mul _

theorem energy_hasDerivAt_firstVariation {t : ℝ} (ht : t ∈ I) :
    HasDerivAt c.energy
      (∫ u in 0..c.period, speed (c.position t) u * force (c.position t) u *
        inner ℝ (normal (c.position t) u) (c.velocity t u)) t := by
  have h := c.energy_hasDerivAt_actualTimeDerivative ht
  have he : ((1 / 2 : ℝ) * ∫ u in 0..c.period,
      deriv (fun x => curvature (c.position x) u ^ 2 * speed (c.position x) u) t) =
      ∫ u in 0..c.period, curvature (c.position t) u * deriv (c.velocityGradientNormal t) u -
        curvature (c.position t) u ^ 2 / 2 *
          inner ℝ (deriv (c.velocity t) u) (tangent (c.position t) u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    have hk := joint_smooth_time_hasDerivAt c.time_open
      (f := fun x => curvature (c.position x)) c.curvature_joint_smooth ht u
    have hd := (hk.pow 2).mul (c.speed_time_hasDerivAt ht u)
    change HasDerivAt
      (fun x => curvature (c.position x) u ^ 2 * speed (c.position x) u) _ t at hd
    norm_num only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] at hd
    rw [hd.deriv, ← c.speed_mul_velocityGradientTangent ht u]
    have hm := c.curvature_metric_rate_identity ht u
    linear_combination (curvature (c.position t) u) * hm
  rw [he] at h
  have hs := energy_spatial_first_variation (c.position_slice_smooth ht)
    (c.immersion t ht) (c.periodic t ht) (c.velocity_slice_smooth ht) (c.velocity_periodic ht)
  change (∫ u in 0..c.period, curvature (c.position t) u * deriv (c.velocityGradientNormal t) u -
    curvature (c.position t) u ^ 2 / 2 *
      inner ℝ (deriv (c.velocity t) u) (tangent (c.position t) u)) = _ at hs
  rw [hs] at h
  exact h
end SmoothPeriodicImmersion

end MigrationGeometry.Flow
