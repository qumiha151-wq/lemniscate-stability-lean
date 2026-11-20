import LengthGrowth.ActualFlow.ForwardDissipation

/-! Signed Green area and its variation, derived from the periodic position
and the normal FEF equation in the original material parameter. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow

def materialSignedArea (γ : ℝ → ℂ) (P : ℝ) : ℝ :=
  ∫ u in 0..P, (γ u).re * (deriv γ u).im

def materialCubicCurvature (γ : ℝ → ℂ) (P : ℝ) : ℝ :=
  ∫ u in 0..P, curvature γ u ^ 3 * speed γ u

theorem integral_force_eq_half_cubic {γ : ℝ → ℂ} {P : ℝ}
    (hs : ContDiff ℝ ∞ γ) (hr : ∀ u, deriv γ u ≠ 0) (hp : Function.Periodic γ P) :
    (∫ u in 0..P, force γ u * speed γ u) = (1/2 : ℝ) * materialCubicCurvature γ P := by
  have h₁ : Continuous (fun u => speed γ u * curvatureSecond γ u) :=
    (speed_smooth hs hr).continuous.mul (curvatureSecond_smooth hs hr).continuous
  have h₂ : Continuous (fun u => curvature γ u ^ 3 * speed γ u) :=
    ((curvature_smooth hs hr).continuous.pow 3).mul (speed_smooth hs hr).continuous
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := P)
    (fun u _ => curvatureGradient_hasDerivAt hs hr u) (h₁.intervalIntegrable 0 P)
  have he : curvatureGradient γ P = curvatureGradient γ 0 := by
    simpa using (curvatureGradient_periodic hs hr hp) 0
  rw [he, sub_self] at hft
  calc
    _ = ∫ u in 0..P, speed γ u * curvatureSecond γ u +
        (1/2 : ℝ) * (curvature γ u ^ 3 * speed γ u) := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp [force]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (h₁.intervalIntegrable 0 P)
        ((h₂.const_mul (1/2 : ℝ)).intervalIntegrable 0 P), hft, zero_add,
        intervalIntegral.integral_const_mul]
      rfl

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem signedArea_hasDerivAt_normal (hf : c.IsNormalFEF) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun x => materialSignedArea (c.position x) c.period)
      ((1/2 : ℝ) * materialCubicCurvature (c.position t) c.period) t := by
  let γ := c.position t
  let v := c.velocity t
  have hγ : ContDiff ℝ ∞ γ := c.position_slice_smooth ht
  have hv : ContDiff ℝ ∞ v := c.velocity_slice_smooth ht
  have hdγ := (contDiff_infty_iff_deriv.mp hγ).2
  have hdv := (contDiff_infty_iff_deriv.mp hv).2
  have hsd := joint_smooth_deriv_space c.time_open c.joint_smooth
  have h := hasDerivAt_intervalIntegral_of_jointC1 (a := 0) (b := c.period)
    (F := fun t u => (c.position t u).re * (deriv (c.position t) u).im)
    c.time_open (((Complex.reCLM.contDiff.comp_contDiffOn c.joint_smooth).mul
      (Complex.imCLM.contDiff.comp_contDiffOn hsd)).of_le (by simp)) ht
  have hr (u : ℝ) : deriv (fun x => (γ x).re) u = (deriv γ u).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt u
      ((hγ.differentiable (by simp) u).hasDerivAt)).deriv
  have hi (u : ℝ) : deriv (fun x => (v x).im) u = (deriv v u).im :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt u
      ((hv.differentiable (by simp) u).hasDerivAt)).deriv
  have hibp := periodic_mul_integration_by_parts
    (Complex.reCLM.contDiff.comp hγ) (Complex.imCLM.contDiff.comp hv)
    (fun x => congrArg Complex.re (c.periodic t ht x))
    (fun x => congrArg Complex.im (c.velocity_periodic ht x))
  change (∫ u in 0..c.period, (γ u).re * deriv (fun x => (v x).im) u) =
    -(∫ u in 0..c.period, deriv (fun x => (γ x).re) u * (v u).im) at hibp
  simp only [hi, hr] at hibp
  have h₁ : Continuous (fun u => (v u).re * (deriv γ u).im) :=
    (Complex.continuous_re.comp hv.continuous).mul (Complex.continuous_im.comp hdγ.continuous)
  have h₂ : Continuous (fun u => (γ u).re * (deriv v u).im) :=
    (Complex.continuous_re.comp hγ.continuous).mul (Complex.continuous_im.comp hdv.continuous)
  have h₃ : Continuous (fun u => (deriv γ u).re * (v u).im) :=
    (Complex.continuous_re.comp hdγ.continuous).mul (Complex.continuous_im.comp hv.continuous)
  have he : (∫ u in 0..c.period, deriv (fun x =>
      (c.position x u).re * (deriv (c.position x) u).im) t) =
      (1/2 : ℝ) * materialCubicCurvature γ c.period := by
    calc
      _ = ∫ u in 0..c.period, (v u).re * (deriv γ u).im + (γ u).re * (deriv v u).im := by
        apply intervalIntegral.integral_congr
        intro u _
        exact ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (c.position_time_hasDerivAt ht u)).mul
          (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (c.position_space_time_hasDerivAt ht u))).deriv
      _ = ∫ u in 0..c.period, (v u).re * (deriv γ u).im - (deriv γ u).re * (v u).im := by
        rw [intervalIntegral.integral_add (h₁.intervalIntegrable ..) (h₂.intervalIntegrable ..),
          hibp, intervalIntegral.integral_sub (h₁.intervalIntegrable ..) (h₃.intervalIntegrable ..)]
        ring
      _ = ∫ u in 0..c.period, force γ u * speed γ u := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only
        calc
          _ = -determinant (deriv γ u) (v u) := by
            simp only [determinant, Complex.mul_im, Complex.conj_re, Complex.conj_im]
            ring
          _ = _ := by
            rw [(position_hasDerivAt hγ (c.immersion t ht) u).deriv,
              determinant_smul_left, determinant_eq_inner]
            change -(speed γ u * inner ℝ (v u) (normal γ u)) = _
            rw [real_inner_comm, c.normal_inner_velocity hf ht u]
            ring
      _ = _ := integral_force_eq_half_cubic hγ (c.immersion t ht) (c.periodic t ht)
  rw [he] at h
  exact h
end SmoothPeriodicImmersion

namespace ForwardImmersion
variable (c : ForwardImmersion)

theorem signedArea_hasDerivAt_normal (hf : c.IsNormalFEF) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => materialSignedArea (c.position x) c.period)
      ((1/2 : ℝ) * materialCubicCurvature (c.position t) c.period) t :=
  c.interior.signedArea_hasDerivAt_normal (c.interior_isNormalFEF hf) ht

end ForwardImmersion
end LengthGrowth.ActualFlow

#print axioms LengthGrowth.ActualFlow.ForwardImmersion.signedArea_hasDerivAt_normal
