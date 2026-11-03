import Lemniscate.BernoulliArclength
import Lemniscate.PeriodicClassicalFourier

/-! The actual curvature profile on its scaled-arclength circle. Its ODE,
first integral, reality and initial values follow from the explicit curve.
The Jacobi/Fourier coefficient identities are separate remaining obligations. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable def periodicCircleFunction (T : ℝ) (f : ℝ → ℂ)
    (hp : Function.Periodic f T) (hc : Continuous f) : C(AddCircle T, ℂ) where
  toFun := hp.lift
  continuous_toFun := hc.quotient_lift _

theorem periodic_circle_function_coe (T : ℝ) (f : ℝ → ℂ)
    (hp : Function.Periodic f T) (hc : Continuous f) (x : ℝ) :
    periodicCircleFunction T f hp hc (x:AddCircle T) = f x := rfl

theorem bernoulli_circle_profile_exists :
    ∃ e : ℝ ≃o ℝ,
      (∀ u, e u = ∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖) ∧
      0 < e (2*Real.pi) ∧
      ∃ q p : C(AddCircle (e (2*Real.pi)), ℂ),
        HasCircleDeriv (e (2*Real.pi)) q p ∧
        HasCircleDeriv (e (2*Real.pi)) p (-(q^3)) ∧
        (∀ x, 2*(p x)^2+(q x)^4 = 1) ∧
        (∀ x, conj (q x) = q x) ∧ (∀ x, conj (p x) = p x) ∧
        q 0 = 1 ∧ p 0 = 0 ∧
        ∀ x : ℝ, (planarSignedCurvature bernoulliCurve (e.symm x):ℂ) =
          3*q (x:AddCircle (e (2*Real.pi))) := by
  obtain ⟨e,he,hT,hqper,hpper,hq0,hp0,hODE⟩ := bernoulli_arclength_profile
  let T := e (2*Real.pi)
  let qR : ℝ → ℝ := bernoulliProfileQ ∘ e.symm
  let pR : ℝ → ℝ := bernoulliProfileP ∘ e.symm
  let qC : ℝ → ℂ := fun x => qR x
  let pC : ℝ → ℂ := fun x => pR x
  have hqCper : Function.Periodic qC T := fun x => congrArg Complex.ofReal (hqper x)
  have hpCper : Function.Periodic pC T := fun x => congrArg Complex.ofReal (hpper x)
  have hqCcont : Continuous qC := Complex.continuous_ofReal.comp
    (continuous_iff_continuousAt.mpr (fun x => (hODE x).1.continuousAt))
  have hpCcont : Continuous pC := Complex.continuous_ofReal.comp
    (continuous_iff_continuousAt.mpr (fun x => (hODE x).2.1.continuousAt))
  let q := periodicCircleFunction T qC hqCper hqCcont
  let p := periodicCircleFunction T pC hpCper hpCcont
  refine ⟨e,he,hT,q,p,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x
    change HasDerivAt qC (pC x) x
    exact (hODE x).1.ofReal_comp
  · intro x
    change HasDerivAt pC (-((qR x:ℂ)^3)) x
    simpa only [Complex.ofReal_neg,Complex.ofReal_pow] using (hODE x).2.1.ofReal_comp
  · intro x
    induction x using QuotientAddGroup.induction_on
    rename_i x
    change 2*(pR x:ℂ)^2+(qR x:ℂ)^4 = 1
    exact_mod_cast (hODE x).2.2.1
  · intro x
    induction x using QuotientAddGroup.induction_on
    rename_i x
    exact Complex.conj_ofReal (qR x)
  · intro x
    induction x using QuotientAddGroup.induction_on
    rename_i x
    exact Complex.conj_ofReal (pR x)
  · change (qR 0:ℂ) = 1
    exact_mod_cast hq0
  · change (pR 0:ℂ) = 0
    exact_mod_cast hp0
  · intro x
    change (planarSignedCurvature bernoulliCurve (e.symm x):ℂ) = 3*(qR x:ℂ)
    exact_mod_cast (hODE x).2.2.2

end Lemniscate
