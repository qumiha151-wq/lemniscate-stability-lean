import Lemniscate.BernoulliExpander
import Lemniscate.PeriodicArclength

/-! The actual scaled arclength coordinate of the explicit lemniscate.
The curvature profiles in this coordinate satisfy q_x=p and p_x=-q^3.
Their period, initial values and first integral are all derived. -/
namespace Lemniscate
open MeasureTheory

theorem bernoulli_arclength_profile :
    ∃ e : ℝ ≃o ℝ,
      (∀ u, e u = ∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖) ∧
      0 < e (2*Real.pi) ∧
      let q : ℝ → ℝ := bernoulliProfileQ ∘ e.symm
      let p : ℝ → ℝ := bernoulliProfileP ∘ e.symm
      Function.Periodic q (e (2*Real.pi)) ∧
      Function.Periodic p (e (2*Real.pi)) ∧ q 0 = 1 ∧ p 0 = 0 ∧
      ∀ x, HasDerivAt q (p x) x ∧ HasDerivAt p (-(q x)^3) x ∧
        2*(p x)^2+(q x)^4 = 1 ∧
        planarSignedCurvature bernoulliCurve (e.symm x) = 3*q x := by
  let v : ℝ → ℝ := fun u => Real.sqrt 2*‖bernoulliVelocity u‖
  have hroot (u : ℝ) : 0 < Real.sqrt (1+(Real.sin u)^2) :=
    Real.sqrt_pos.mpr (by nlinarith only [sq_nonneg (Real.sin u)])
  have hvelocity : Continuous bernoulliVelocity :=
    continuous_iff_continuousAt.mpr (fun u => (bernoulli_curve_geometry u).2.1.continuousAt)
  have hv : Continuous v := continuous_const.mul hvelocity.norm
  have hv1 (u : ℝ) : 1 ≤ v u := by
    dsimp only [v]
    rw [(bernoulli_curve_geometry u).2.2.1,mul_one_div]
    apply (le_div_iff₀ (hroot u)).mpr
    simpa only [one_mul] using Real.sqrt_le_sqrt
      (by nlinarith only [Real.sin_sq_le_one u] : 1+(Real.sin u)^2 ≤ 2)
  have hper : Function.Periodic v (2*Real.pi) := by
    intro u
    dsimp only [v]
    rw [(bernoulli_curve_geometry (u+2*Real.pi)).2.2.1,
      (bernoulli_curve_geometry u).2.2.1,Real.sin_add_two_pi]
  obtain ⟨e,he,hinv,hT,hshift⟩ := periodic_integral_coordinate_exists v hv hv1
    (2*Real.pi) (mul_pos (by norm_num) Real.pi_pos) hper
  let q : ℝ → ℝ := bernoulliProfileQ ∘ e.symm
  let p : ℝ → ℝ := bernoulliProfileP ∘ e.symm
  have he0 : e 0 = 0 := by rw [he]; simp
  have hi0 : e.symm 0 = 0 := by
    apply e.injective
    rw [e.apply_symm_apply,he0]
  refine ⟨e,he,hT,?_,?_,?_,?_,?_⟩
  · intro x
    change bernoulliProfileQ (e.symm (x+e (2*Real.pi))) = bernoulliProfileQ (e.symm x)
    rw [hshift]
    simp only [bernoulliProfileQ,Real.cos_add_two_pi,Real.sin_add_two_pi]
  · intro x
    change bernoulliProfileP (e.symm (x+e (2*Real.pi))) = bernoulliProfileP (e.symm x)
    rw [hshift]
    simp only [bernoulliProfileP,Real.sin_add_two_pi]
  · norm_num [q,Function.comp_def,hi0,bernoulliProfileQ]
  · norm_num [p,Function.comp_def,hi0,bernoulliProfileP]
  · intro x
    have hne : v (e.symm x) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hv1 _))
    refine ⟨?_,?_,(bernoulli_profile_data (e.symm x)).2.2,?_⟩
    · convert! ((bernoulli_profile_data (e.symm x)).1).comp x (hinv x) using 1
      change p x = (v (e.symm x)*p x)*(v (e.symm x))⁻¹
      field_simp [hne]
    · convert! ((bernoulli_profile_data (e.symm x)).2.1).comp x (hinv x) using 1
      change -(q x)^3 = (-(v (e.symm x))*(q x)^3)*(v (e.symm x))⁻¹
      field_simp [hne]
    · have hvel : deriv bernoulliCurve = bernoulliVelocity :=
        funext fun u => (bernoulli_curve_geometry u).1.deriv
      have hacc : deriv bernoulliVelocity = bernoulliAcceleration :=
        funext fun u => (bernoulli_curve_geometry u).2.1.deriv
      dsimp only [planarSignedCurvature]
      rw [hvel,hacc,(bernoulli_curve_geometry (e.symm x)).2.2.2.1]
      dsimp only [q,Function.comp_def,bernoulliProfileQ]
      ring

end Lemniscate
