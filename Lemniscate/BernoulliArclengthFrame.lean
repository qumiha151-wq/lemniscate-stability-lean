import Lemniscate.ArclengthFrame
import Lemniscate.BernoulliArclength

/-! The Frenet frame and curvature jet of the actual Bernoulli lemniscate in
physical arclength s. The existing profile coordinate is x = sqrt(2) * s.
The only input is its proved integral coordinate; no geometric identity or
variation formula is assumed. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped ComplexConjugate

private theorem bernoulli_unit_tangent_position (u : ℝ) :
    conj (bernoulliVelocity u / (‖bernoulliVelocity u‖ : ℂ)) * bernoulliCurve u =
      ((Real.sqrt 2 * bernoulliProfileQ u * bernoulliProfileP u : ℝ) : ℂ) +
        ((-(bernoulliProfileQ u)^3 : ℝ) : ℂ) * I := by
  have hpair : conj (bernoulliVelocity u) * bernoulliCurve u =
      conj (conj (bernoulliCurve u) * bernoulliVelocity u) := by
    rw [map_mul,Complex.conj_conj]
    ring
  apply Complex.ext
  · simp only [map_div₀,Complex.conj_ofReal,div_mul_eq_mul_div₀,
      Complex.div_ofReal_re,hpair,Complex.conj_re,Complex.add_re,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,one_mul,
      sub_zero,zero_sub,add_zero,zero_add]
    change (conj (bernoulliCurve u)*bernoulliVelocity u).re/‖bernoulliVelocity u‖ =
      Real.sqrt 2*bernoulliProfileQ u*bernoulliProfileP u
    rw [(bernoulli_curve_geometry u).2.2.2.2.2]
    let r := Real.sqrt (1+(Real.sin u)^2)
    have hr0 : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (by nlinarith only [sq_nonneg (Real.sin u)]))
    have hr2 : r^2 = 1+(Real.sin u)^2 := Real.sq_sqrt
      (by nlinarith only [sq_nonneg (Real.sin u)])
    change -2*Real.sin u*Real.cos u/r^3 =
      Real.sqrt 2*(Real.cos u/r)*(-Real.sqrt 2*Real.sin u/(1+(Real.sin u)^2))
    rw [← hr2]
    field_simp [hr0]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  · simp only [map_div₀,Complex.conj_ofReal,div_mul_eq_mul_div₀,
      Complex.div_ofReal_im,hpair,Complex.conj_im,Complex.add_im,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,one_mul,
      sub_zero,zero_sub,add_zero,zero_add]
    exact (bernoulli_curve_geometry u).2.2.2.2.1

theorem bernoulli_arclength_frame (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0:ℝ)..u, Real.sqrt 2 * ‖bernoulliVelocity t‖) :
    let φ : ℝ → ℝ := fun s => e.symm (Real.sqrt 2*s)
    let Γ := bernoulliCurve ∘ φ
    let t : ℝ → ℂ := fun s =>
      bernoulliVelocity (φ s) / (‖bernoulliVelocity (φ s)‖ : ℂ)
    let n : ℝ → ℂ := fun s => I*t s
    let q := bernoulliProfileQ ∘ φ
    let p := bernoulliProfileP ∘ φ
    let k : ℝ → ℝ := fun s => 3*q s
    let ks : ℝ → ℝ := fun s => 3*Real.sqrt 2*p s
    let kss : ℝ → ℝ := fun s => -6*(q s)^3
    let ksss : ℝ → ℝ := fun s => -18*Real.sqrt 2*(q s)^2*p s
    ∀ s, HasDerivAt Γ (t s) s ∧ ‖t s‖ = 1 ∧
      HasDerivAt t ((k s : ℂ)*n s) s ∧
      HasDerivAt n (-(k s : ℂ)*t s) s ∧
      HasDerivAt k (ks s) s ∧ HasDerivAt ks (kss s) s ∧
      HasDerivAt kss (ksss s) s ∧
      planarSignedCurvature Γ s = k s ∧
      conj (t s)*Γ s = ((Real.sqrt 2*q s*p s : ℝ) : ℂ) +
        ((-(q s)^3 : ℝ) : ℂ)*I ∧
      2*(p s)^2+(q s)^4 = 1 := by
  let φ : ℝ → ℝ := fun s => e.symm (Real.sqrt 2*s)
  let Γ := bernoulliCurve ∘ φ
  let t : ℝ → ℂ := fun s =>
    bernoulliVelocity (φ s) / (‖bernoulliVelocity (φ s)‖ : ℂ)
  let n : ℝ → ℂ := fun s => I*t s
  let q := bernoulliProfileQ ∘ φ
  let p := bernoulliProfileP ∘ φ
  let k : ℝ → ℝ := fun s => 3*q s
  let ks : ℝ → ℝ := fun s => 3*Real.sqrt 2*p s
  let kss : ℝ → ℝ := fun s => -6*(q s)^3
  let ksss : ℝ → ℝ := fun s => -18*Real.sqrt 2*(q s)^2*p s
  have hspeed (u : ℝ) : ‖bernoulliVelocity u‖ ≠ 0 := by
    rw [(bernoulli_curve_geometry u).2.2.1]
    exact div_ne_zero one_ne_zero (ne_of_gt (Real.sqrt_pos.mpr
      (by nlinarith only [sq_nonneg (Real.sin u)])))
  have hroot : Real.sqrt (2:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  let v : ℝ → ℝ := fun u => Real.sqrt 2*‖bernoulliVelocity u‖
  have hvelocity : Continuous bernoulliVelocity :=
    continuous_iff_continuousAt.mpr (fun u => (bernoulli_curve_geometry u).2.1.continuousAt)
  have hv : Continuous v := continuous_const.mul hvelocity.norm
  have hefun : (fun u => ∫ t in (0:ℝ)..u, v t) = (e : ℝ → ℝ) :=
    funext fun u => (he u).symm
  have heD (u : ℝ) : HasDerivAt e (v u) u := by
    have h := intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 u)
      hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt
    rw [hefun] at h
    exact h
  have hinv (x : ℝ) : HasDerivAt e.symm (v (e.symm x))⁻¹ x := by
    apply HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt
      (heD (e.symm x)) (mul_ne_zero hroot (hspeed (e.symm x)))
    exact Eventually.of_forall e.apply_symm_apply
  have hφ (s : ℝ) : HasDerivAt φ (1/‖bernoulliVelocity (φ s)‖) s := by
    convert! (hinv (Real.sqrt 2*s)).comp s
      ((hasDerivAt_id s).const_mul (Real.sqrt 2)) using 1
    change 1/‖bernoulliVelocity (φ s)‖ =
      (Real.sqrt 2*‖bernoulliVelocity (φ s)‖)⁻¹*(Real.sqrt 2*1)
    field_simp [hroot,hspeed (φ s)]
  have hreg (s : ℝ) : bernoulliVelocity (φ s) ≠ 0 :=
    norm_ne_zero_iff.mp (hspeed (φ s))
  have hQ (s : ℝ) : HasDerivAt q (Real.sqrt 2*p s) s := by
    convert! ((bernoulli_profile_data (φ s)).1).comp s (hφ s) using 1
    change Real.sqrt 2*p s =
      ((Real.sqrt 2*‖bernoulliVelocity (φ s)‖)*p s)*(1/‖bernoulliVelocity (φ s)‖)
    field_simp [hspeed (φ s)]
  have hP (s : ℝ) : HasDerivAt p (-Real.sqrt 2*(q s)^3) s := by
    convert! ((bernoulli_profile_data (φ s)).2.1).comp s (hφ s) using 1
    change -Real.sqrt 2*(q s)^3 =
      (-(Real.sqrt 2*‖bernoulliVelocity (φ s)‖)*(q s)^3)*(1/‖bernoulliVelocity (φ s)‖)
    field_simp [hspeed (φ s)]
  have hk (s : ℝ) : planarSignedCurvature bernoulliCurve (φ s) = k s := by
    have hdβ : deriv bernoulliCurve = bernoulliVelocity :=
      funext fun u => (bernoulli_curve_geometry u).1.deriv
    have hdv : deriv bernoulliVelocity = bernoulliAcceleration :=
      funext fun u => (bernoulli_curve_geometry u).2.1.deriv
    dsimp only [planarSignedCurvature]
    rw [hdβ,hdv,(bernoulli_curve_geometry (φ s)).2.2.2.1]
    dsimp only [k,q,Function.comp_def,bernoulliProfileQ]
    ring
  have hframe := arclength_frenet_frame bernoulliCurve bernoulliVelocity
    bernoulliAcceleration φ (fun u => (bernoulli_curve_geometry u).1)
      (fun u => (bernoulli_curve_geometry u).2.1) hφ hreg
  obtain ⟨hΓ,htunit,ht,hn,hcurv,_⟩ := hframe
  dsimp only
  intro s
  refine ⟨hΓ s,htunit s,?_,?_,?_,?_,?_,(hcurv s).trans (hk s),?_,
    (bernoulli_profile_data (φ s)).2.2⟩
  · simpa only [hk s] using ht s
  · simpa only [hk s] using hn s
  · convert! (hQ s).const_mul 3 using 1
    simp only [k,ks,kss,ksss,q,p,φ,Function.comp_def] <;> ring
  · convert! (hP s).const_mul (3*Real.sqrt 2) using 1
    simp only [k,ks,kss,ksss,q,p,φ,Function.comp_def]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] <;> ring
  · convert! ((hQ s).pow 3).const_mul (-6) using 1
    simp only [k,ks,kss,ksss,q,p,φ,Function.comp_def] <;> ring
  · exact bernoulli_unit_tangent_position (φ s)

end Lemniscate
