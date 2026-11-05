import Lemniscate.BernoulliArclengthFrame
import Lemniscate.PeriodicClassicalFourier

/-! Identification of the actual scaled-arclength profile. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

theorem bernoulli_arclength_profile_of_coordinate (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖) :
    let q : ℝ → ℝ := bernoulliProfileQ ∘ e.symm
    let p : ℝ → ℝ := bernoulliProfileP ∘ e.symm
    ∀ x, HasDerivAt q (p x) x ∧ HasDerivAt p (-(q x)^3) x ∧
      2*(p x)^2+(q x)^4=1 ∧
      planarSignedCurvature bernoulliCurve (e.symm x)=3*q x := by
  obtain ⟨e₀,he₀,_,_,_,_,_,hODE⟩ := bernoulli_arclength_profile
  have heq : e₀=e := by
    ext u
    exact (he₀ u).trans (he u).symm
  subst e₀
  exact hODE

theorem bernoulli_circle_profile_identification
    (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    (q p : C(AddCircle (e (2*Real.pi)),ℂ))
    (hq : HasCircleDeriv (e (2*Real.pi)) q p)
    (hcurvature : ∀ x : ℝ, (planarSignedCurvature bernoulliCurve (e.symm x):ℂ)=
      3*q (x:AddCircle (e (2*Real.pi)))) :
    ∀ x : ℝ, q (x:AddCircle (e (2*Real.pi)))=(bernoulliProfileQ (e.symm x):ℂ) ∧
      p (x:AddCircle (e (2*Real.pi)))=(bernoulliProfileP (e.symm x):ℂ) := by
  have hODE := bernoulli_arclength_profile_of_coordinate e he
  have hqactual (x : ℝ) :
      q (x:AddCircle (e (2*Real.pi)))=(bernoulliProfileQ (e.symm x):ℂ) := by
    have hc := hcurvature x
    rw [(hODE x).2.2.2] at hc
    have hc' : (3:ℂ)*(bernoulliProfileQ (e.symm x):ℂ)=
        3*q (x:AddCircle (e (2*Real.pi))) := by
      simpa only [Function.comp_apply,Complex.ofReal_mul,Complex.ofReal_ofNat] using hc
    exact (mul_left_cancel₀ (by norm_num : (3:ℂ)≠0) hc').symm
  intro x
  refine ⟨hqactual x,?_⟩
  have hleft := hq x
  change HasDerivAt (fun u : ℝ => q (u:AddCircle (e (2*Real.pi))))
    (p (x:AddCircle (e (2*Real.pi)))) x at hleft
  have hfun : (fun u : ℝ => q (u:AddCircle (e (2*Real.pi))))=
      fun u => (bernoulliProfileQ (e.symm u):ℂ) := funext hqactual
  rw [hfun] at hleft
  exact hleft.unique ((hODE x).1.ofReal_comp)

end Lemniscate
