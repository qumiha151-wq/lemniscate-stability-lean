import Lemniscate.BernoulliArclength
import Lemniscate.PeriodicWeierstrassProfile
import Lemniscate.SquareWeierstrassPositive
import Lemniscate.BernoulliPeriod

/-! The actual curvature profile on its scaled-arclength circle, including
its normalized shifted Weierstrass representation. No scalar normalization
or profile ODE is assumed. The actual scaled-arclength period is identified;
the Fourier coefficients remain a separate obligation. -/
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
        (∀ x : ℝ, (planarSignedCurvature bernoulliCurve (e.symm x):ℂ) =
          3*q (x:AddCircle (e (2*Real.pi)))) ∧
        ∃ a : ℝ, 0 < a ∧ 2*(a:ℂ)^2*unitSquarePeriods.weierstrassP (1/2) = 1 ∧
          e (2*Real.pi) = 2/a ∧
          (fun x : ℝ => (q (x:AddCircle (e (2*Real.pi))))^2) = normalizedWeierstrass a ∧
          (fun x : ℝ => 2*(q (x:AddCircle (e (2*Real.pi)))*
            p (x:AddCircle (e (2*Real.pi))))) = normalizedWeierstrassDerivative a := by
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
  have hqD : HasCircleDeriv T q p := by
    intro x
    change HasDerivAt qC (pC x) x
    exact (hODE x).1.ofReal_comp
  have hpD : HasCircleDeriv T p (-(q^3)) := by
    intro x
    change HasDerivAt pC (-((qR x:ℂ)^3)) x
    simpa only [Complex.ofReal_neg,Complex.ofReal_pow] using (hODE x).2.1.ofReal_comp
  have henergy : ∀ x, 2*(p x)^2+(q x)^4 = 1 := by
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i x
    change 2*(pR x:ℂ)^2+(qR x:ℂ)^4 = 1
    exact_mod_cast (hODE x).2.2.1
  have hqreal : ∀ x, conj (q x) = q x := by
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i x
    exact Complex.conj_ofReal (qR x)
  have hpreal : ∀ x, conj (p x) = p x := by
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i x
    exact Complex.conj_ofReal (pR x)
  have hq0C : q 0 = 1 := by
    change (qR 0:ℂ) = 1
    exact_mod_cast hq0
  have hp0C : p 0 = 0 := by
    change (pR 0:ℂ) = 0
    exact_mod_cast hp0
  have hcurv : ∀ x : ℝ, (planarSignedCurvature bernoulliCurve (e.symm x):ℂ) =
      3*q (x:AddCircle T) := by
    intro x
    change (planarSignedCurvature bernoulliCurve (e.symm x):ℂ) = 3*(qR x:ℂ)
    exact_mod_cast (hODE x).2.2.2
  obtain ⟨a,ha,hnorm⟩ := unit_square_normalization_exists
  have hW := circle_profile_square_weierstrass T q p hqD hpD henergy hq0C hp0C a hnorm
  have hident (x : ℝ) : (bernoulliProfileQ (e.symm x):ℂ)^2 = normalizedWeierstrass a x := by
    change (q (x:AddCircle T))^2 = normalizedWeierstrass a x
    exact congrFun hW.1 x
  have hperiod := bernoulli_weierstrass_period e he a ha hnorm hident
  exact ⟨e,he,hT,q,p,hqD,hpD,henergy,hqreal,hpreal,hq0C,hp0C,hcurv,a,ha,hnorm,
    hperiod,hW⟩

end Lemniscate
