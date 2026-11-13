import LengthGrowth.ActualFlow.FamilyRegularity
import LengthGrowth.ActualFlow.MixedPartials
import Mathlib.Tactic.LinearCombination

/-! Actual time variation of a position-defined arbitrary-speed immersion.
Mixed partials are proved from joint smoothness; no evolution identities
or independent frame data are hypotheses. -/

noncomputable section
open Set Filter
open scoped ContDiff ComplexConjugate Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow

theorem actual_time_space_deriv_commute {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Set ℝ} {f : ℝ → ℝ → E}
    (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    deriv (fun x => deriv (f x) u) t =
      deriv (fun y => deriv (fun x => f x y) t) u := by
  let F : ℝ × ℝ → E := fun z => f z.1 z.2
  have hS : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hdf (z : ℝ × ℝ) (hz : z ∈ I ×ˢ (univ : Set ℝ)) : DifferentiableAt ℝ F z :=
    (hf.differentiableOn (by simp) z hz).differentiableAt (hS.mem_nhds hz)
  have hsp : ContDiffOn ℝ ∞ (partialSpace F) (I ×ˢ (univ : Set ℝ)) :=
    (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
  have htp : ContDiffOn ℝ ∞ (partialTime F) (I ×ˢ (univ : Set ℝ)) :=
    (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
  have hz : (t, u) ∈ I ×ˢ (univ : Set ℝ) := ⟨ht, mem_univ u⟩
  calc
    _ = deriv (fun x => partialSpace F (x, u)) t := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hI.mem_nhds ht] with x hx
      exact deriv_space_eq_partialSpace (hdf (x, u) ⟨hx, mem_univ u⟩)
    _ = partialTime (partialSpace F) (t, u) :=
      deriv_time_eq_partialTime
        ((hsp.differentiableOn (by simp) (t, u) hz).differentiableAt (hS.mem_nhds hz))
    _ = partialSpace (partialTime F) (t, u) :=
      actual_partials_commute ((hf (t, u) hz).contDiffAt (hS.mem_nhds hz) |>.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    _ = deriv (fun y => partialTime F (t, y)) u :=
      (deriv_space_eq_partialSpace
        ((htp.differentiableOn (by simp) (t, u) hz).differentiableAt (hS.mem_nhds hz))).symm
    _ = _ := by
      congr 1
      funext y
      exact (deriv_time_eq_partialTime (hdf (t, y) ⟨ht, mem_univ y⟩)).symm

/-- Elementary decomposition in the actual complex unit frame. -/
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

theorem position_space_time_hasDerivAt {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    HasDerivAt (fun x => deriv (c.position x) u) (deriv (c.velocity t) u) t := by
  have h := joint_smooth_time_hasDerivAt c.time_open
    (f := fun x => deriv (c.position x))
    (joint_smooth_deriv_space c.time_open c.joint_smooth) ht u
  rw [actual_time_space_deriv_commute c.time_open c.joint_smooth ht u] at h
  exact h

theorem speed_mul_velocityGradientTangent {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    speed (c.position t) u * c.velocityGradientTangent t u =
      inner ℝ (deriv (c.velocity t) u) (tangent (c.position t) u) := by
  simp only [velocityGradientTangent, arcDerivative, real_inner_smul_left]
  rw [← mul_assoc, mul_inv_cancel₀ (speed_pos (c.immersion t ht) u).ne', one_mul]

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

/-- The metric time derivative is derived from the norm of the actual position derivative. -/
theorem speed_time_hasDerivAt {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    HasDerivAt (fun x => speed (c.position x) u)
      (speed (c.position t) u * c.velocityGradientTangent t u) t := by
  have hg := joint_smooth_time_hasDerivAt c.time_open
    (f := fun x => speed (c.position x)) c.speed_joint_smooth ht u
  have hsq := (c.position_space_time_hasDerivAt ht u).norm_sq
  have he := (hg.pow 2).unique hsq
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at he
  have hp := (position_hasDerivAt (c.position_slice_smooth ht) (c.immersion t ht) u).deriv
  have hne := (speed_pos (c.immersion t ht) u).ne'
  have hgt : deriv (fun x => speed (c.position x) u) t =
      inner ℝ (tangent (c.position t) u) (deriv (c.velocity t) u) := by
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hne)
    calc
      _ = 2 * inner ℝ (deriv (c.position t) u) (deriv (c.velocity t) u) := he
      _ = _ := by rw [hp, real_inner_smul_left]; ring
  rw [hgt, real_inner_comm, ← c.speed_mul_velocityGradientTangent ht u] at hg
  exact hg

/-- Actual time derivative of the normalized tangent. -/
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

/-- Explicit actual curvature derivative for arbitrary smooth velocity. -/
theorem curvature_time_hasDerivAt {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    HasDerivAt (fun x => curvature (c.position x) u)
      (deriv (c.velocityGradientNormal t) u / speed (c.position t) u -
        curvature (c.position t) u * c.velocityGradientTangent t u) t := by
  have hk := joint_smooth_time_hasDerivAt c.time_open
    (f := fun x => curvature (c.position x)) c.curvature_joint_smooth ht u
  have he := c.curvature_metric_rate_identity ht u
  have hne := (speed_pos (c.immersion t ht) u).ne'
  have hv : deriv (fun x => curvature (c.position x) u) t =
      deriv (c.velocityGradientNormal t) u / speed (c.position t) u -
        curvature (c.position t) u * c.velocityGradientTangent t u := by
    apply (eq_sub_iff_add_eq).2
    apply (eq_div_iff hne).2
    nlinarith [he]
  simpa only [hv] using hk

end SmoothPeriodicImmersion
end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Family derivatives audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Family derivatives audit passed: {checked} declarations; standard axioms only."
