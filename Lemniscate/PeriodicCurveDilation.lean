import Lemniscate.ArclengthFrame
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Positive Euclidean dilations preserve the normalized curvature error. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ContDiff ComplexConjugate

private theorem dilated_unit_speed_frame
    (a P : ℝ) (ha : 0<a) (Γ t : ℝ → ℂ) (k : ℝ → ℝ)
    (hΓsmooth : ContDiff ℝ ∞ Γ) (htsmooth : ContDiff ℝ ∞ t)
    (hksmooth : ContDiff ℝ ∞ k)
    (hΓper : Function.Periodic Γ P) (htper : Function.Periodic t P)
    (hkper : Function.Periodic k P)
    (hΓ : ∀ s, HasDerivAt Γ (t s) s)
    (ht : ∀ s, HasDerivAt t (I*(k s:ℂ)*t s) s)
    (hu : ∀ s, ‖t s‖=1) :
    let Γa : ℝ → ℂ := fun x => (a:ℂ)*Γ (x/a)
    let ta : ℝ → ℂ := fun x => t (x/a)
    let ka : ℝ → ℝ := fun x => k (x/a)/a
    ContDiff ℝ ∞ Γa ∧ Function.Periodic Γa (a*P) ∧
    ContDiff ℝ ∞ ta ∧ Function.Periodic ta (a*P) ∧
    ContDiff ℝ ∞ ka ∧ Function.Periodic ka (a*P) ∧
    ∀ x, HasDerivAt Γa (ta x) x ∧ ‖ta x‖=1 ∧
      HasDerivAt ta (I*(ka x:ℂ)*ta x) x ∧ planarSignedCurvature Γa x=ka x := by
  let β : ℝ → ℂ := fun u => (a:ℂ)*Γ u
  let v : ℝ → ℂ := fun u => (a:ℂ)*t u
  let A : ℝ → ℂ := fun u => (a:ℂ)*(I*(k u:ℂ)*t u)
  let φ : ℝ → ℝ := fun x => x/a
  let Γa : ℝ → ℂ := fun x => (a:ℂ)*Γ (x/a)
  let ta : ℝ → ℂ := fun x => t (x/a)
  let ka : ℝ → ℝ := fun x => k (x/a)/a
  have hane : a≠0 := ne_of_gt ha
  have haC : (a:ℂ)≠0 := by exact_mod_cast hane
  have hβ (u : ℝ) : HasDerivAt β (v u) u := (hΓ u).const_mul (a:ℂ)
  have hv (u : ℝ) : HasDerivAt v (A u) u := (ht u).const_mul (a:ℂ)
  have hspeed (u : ℝ) : ‖v u‖=a := by
    dsimp only [v]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,hu u,mul_one]
  have hφ (x : ℝ) : HasDerivAt φ (1/‖v (φ x)‖) x := by
    simpa only [φ,hspeed,one_div,id_eq] using! (hasDerivAt_id x).div_const a
  have hvreg (x : ℝ) : v (φ x)≠0 := by
    apply norm_ne_zero_iff.mp
    rw [hspeed]
    exact hane
  have hcurvature (u : ℝ) : planarSignedCurvature β u=k u/a := by
    have hdβ : deriv β=v := funext fun u => (hβ u).deriv
    have hdv : deriv v=A := funext fun u => (hv u).deriv
    have hunit : conj (t u)*t u=1 := by rw [Complex.conj_mul',hu u]; norm_num
    change (conj (deriv β u)*deriv (deriv β) u).im/‖deriv β u‖^3=k u/a
    rw [hdβ,hdv,hspeed]
    have heq : conj (v u)*A u=I*((a^2*k u:ℝ):ℂ) := by
      dsimp only [v,A]
      simp only [map_mul,Complex.conj_ofReal]
      calc
        _ = I*(a:ℂ)^2*(k u:ℂ)*(conj (t u)*t u) := by ring
        _ = _ := by rw [hunit,mul_one]; push_cast; ring
    rw [heq]
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,one_mul,zero_add]
    field_simp [hane] <;> ring
  have hframe := arclength_frenet_frame β v A φ hβ hv hφ hvreg
  let tn : ℝ → ℂ := fun x => v (φ x)/(‖v (φ x)‖:ℂ)
  have htn : tn=ta := by
    funext x
    dsimp only [tn]
    rw [hspeed]
    change ((a:ℂ)*t (x/a))/(a:ℂ)=t (x/a)
    field_simp [haC]
  have hΓa (x : ℝ) : HasDerivAt Γa (ta x) x := by
    have hh := hframe.1 x
    change HasDerivAt Γa (tn x) x at hh
    rw [htn] at hh
    exact hh
  have hta (x : ℝ) : HasDerivAt ta (I*(ka x:ℂ)*ta x) x := by
    have hh := hframe.2.2.1 x
    change HasDerivAt tn ((planarSignedCurvature β (φ x):ℂ)*(I*tn x)) x at hh
    rw [hcurvature,htn] at hh
    apply hh.congr_deriv
    dsimp only [ka,φ]
    ring
  have hka (x : ℝ) : planarSignedCurvature Γa x=ka x := by
    have hh := hframe.2.2.2.2.1 x
    change planarSignedCurvature Γa x=planarSignedCurvature β (φ x) at hh
    rw [hcurvature] at hh
    exact hh
  have hdivide (x : ℝ) : (x+a*P)/a=x/a+P := by field_simp [hane] <;> ring
  refine ⟨contDiff_const.mul (hΓsmooth.comp (contDiff_id.div_const a)),?_,
    htsmooth.comp (contDiff_id.div_const a),?_,
    (hksmooth.comp (contDiff_id.div_const a)).div_const a,?_,?_⟩
  · intro x
    change (a:ℂ)*Γ ((x+a*P)/a)=(a:ℂ)*Γ (x/a)
    rw [hdivide,hΓper]
  · intro x
    change t ((x+a*P)/a)=t (x/a)
    rw [hdivide,htper]
  · intro x
    change k ((x+a*P)/a)/a=k (x/a)/a
    rw [hdivide,hkper]
  · intro x
    exact ⟨hΓa x,hu (x/a),hta x,hka x⟩

/-- The length-weighted squared curvature difference is invariant under
simultaneous positive dilation. No regularity of the profiles is needed. -/
theorem dilated_curvature_integral (a P : ℝ) (ha : 0<a) (k₀ k₁ : ℝ → ℝ) :
    (a*P)*(∫ x in (0:ℝ)..(a*P), ((k₁ (x/a)-k₀ (x/a))/a)^2)=
      P*(∫ x in (0:ℝ)..P, (k₁ x-k₀ x)^2) := by
  have hane : a≠0 := ne_of_gt ha
  have hpoint (x : ℝ) : ((k₁ (x/a)-k₀ (x/a))/a)^2=
      (a⁻¹)^2*(k₁ (x/a)-k₀ (x/a))^2 := by
    simp only [div_pow,div_eq_mul_inv]
    ring
  have heval : (a*P)/a=P := by field_simp [hane]
  rw [intervalIntegral.integral_congr (fun x _ => hpoint x),
    intervalIntegral.integral_const_mul]
  have hchange := intervalIntegral.integral_comp_div
    (fun x => (k₁ x-k₀ x)^2) (a := (0:ℝ)) (b := a*P) hane
  rw [zero_div,heval,smul_eq_mul] at hchange
  rw [hchange]
  field_simp [hane] <;> ring

/-- Simultaneous positive dilation of two same-period unit-speed curves
preserves their normalized squared signed-curvature difference. Each
rescaled Frenet frame and signed curvature is the actual geometric one. -/
theorem periodic_curve_dilation
    (a P : ℝ) (ha : 0<a) (hP : 0<P)
    (Γ t : Fin 2 → ℝ → ℂ) (k : Fin 2 → ℝ → ℝ)
    (hΓsmooth : ∀ i, ContDiff ℝ ∞ (Γ i))
    (htsmooth : ∀ i, ContDiff ℝ ∞ (t i))
    (hksmooth : ∀ i, ContDiff ℝ ∞ (k i))
    (hΓper : ∀ i, Function.Periodic (Γ i) P)
    (htper : ∀ i, Function.Periodic (t i) P)
    (hkper : ∀ i, Function.Periodic (k i) P)
    (hΓ : ∀ i s, HasDerivAt (Γ i) (t i s) s)
    (ht : ∀ i s, HasDerivAt (t i) (I*(k i s:ℂ)*t i s) s)
    (hu : ∀ i s, ‖t i s‖=1) :
    let Γa : Fin 2 → ℝ → ℂ := fun i x => (a:ℂ)*Γ i (x/a)
    let ta : Fin 2 → ℝ → ℂ := fun i x => t i (x/a)
    let ka : Fin 2 → ℝ → ℝ := fun i x => k i (x/a)/a
    0<a*P ∧
    (∀ i, ContDiff ℝ ∞ (Γa i) ∧ Function.Periodic (Γa i) (a*P) ∧
      ContDiff ℝ ∞ (ta i) ∧ Function.Periodic (ta i) (a*P) ∧
      ContDiff ℝ ∞ (ka i) ∧ Function.Periodic (ka i) (a*P) ∧
      ∀ x, HasDerivAt (Γa i) (ta i x) x ∧ ‖ta i x‖=1 ∧
        HasDerivAt (ta i) (I*(ka i x:ℂ)*ta i x) x ∧
        planarSignedCurvature (Γa i) x=ka i x) ∧
    (a*P)*(∫ x in (0:ℝ)..(a*P), ((k 1 (x/a)-k 0 (x/a))/a)^2)=
      P*(∫ x in (0:ℝ)..P, (k 1 x-k 0 x)^2) := by
  refine ⟨mul_pos ha hP,?_,dilated_curvature_integral a P ha (k 0) (k 1)⟩
  intro i
  exact dilated_unit_speed_frame a P ha (Γ i) (t i) (k i)
    (hΓsmooth i) (htsmooth i) (hksmooth i) (hΓper i) (htper i) (hkper i)
    (hΓ i) (ht i) (hu i)

end Lemniscate
