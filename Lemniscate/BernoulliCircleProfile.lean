import Lemniscate.BernoulliArclength
import Lemniscate.PeriodicWeierstrassProfile
import Lemniscate.WeierstrassFrequencyBounds
import Lemniscate.SquareWeierstrassPositive
import Lemniscate.BernoulliPeriod
import Lemniscate.ConcreteCoefficients
import Lemniscate.CircleWeierstrassFourier
import Lemniscate.PeriodicProfileCoverSpectrum
import Lemniscate.PeriodicCoverUpperBound
import Lemniscate.PeriodicDilationEigenmode
/-! The actual curvature profile on its scaled-arclength circle, including
its normalized Weierstrass representation, period, frequency and complete
Fourier data, together with the rotational kernel and spectral gap on every
positive cover. No profile, normalization or Fourier identity is assumed. -/
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
      ∃ hT : 0 < e (2*Real.pi),
      letI : Fact (0 < e (2*Real.pi)) := ⟨hT⟩;
      ∃ q p : C(AddCircle (e (2*Real.pi)), ℂ),
        HasCircleDeriv (e (2*Real.pi)) q p ∧
        HasCircleDeriv (e (2*Real.pi)) p (-(q^3)) ∧
        (∀ x, 2*(p x)^2+(q x)^4 = 1) ∧
        (∀ x, conj (q x) = q x) ∧ (∀ x, conj (p x) = p x) ∧
        q 0 = 1 ∧ p 0 = 0 ∧
        (∀ x : ℝ, (planarSignedCurvature bernoulliCurve (e.symm x):ℂ) =
          3*q (x:AddCircle (e (2*Real.pi)))) ∧
        (∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle (e (2*Real.pi)), ℂ)) (-n) =
          fourierCoeff (q^2 : C(AddCircle (e (2*Real.pi)), ℂ)) n) ∧
        (∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle (e (2*Real.pi)), ℂ)) (2*(j:ℤ)) =
          (CoarseArithmetic.fourierCoefficient CoarseArithmetic.lemniscateFrequencySquared
            CoarseArithmetic.nome j:ℂ)) ∧
        (∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle (e (2*Real.pi)), ℂ)) (2*n+1) = 0) ∧
        (∀ M : ℕ, 0 < M → ∀ (S : ℝ) [Fact (0 < S)]
            (hS : S = (M:ℝ)*e (2*Real.pi)),
          let E := circlePeriodicExtension (e (2*Real.pi)) S M hS
          let Q := E q
          let P := E p
          let A := circleH4Operator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))
          ∃ R : circleH4Domain S,
            (R:CircleL2 S) = circleContinuousL2 S (Q*P) ∧
            (R:CircleL2 S) ≠ 0 ∧
            LinearMap.ker A = Submodule.span ℂ {R} ∧
            (∀ f g : circleH4Domain S, A f = (g:CircleL2 S) → A g = 0 → A f = 0) ∧
            (if M = 1 then (21/4:ℝ) else 1/(2*(M:ℝ)^2)) ≤
              circleSpectralGap S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))) ∧
        (∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ M : ℕ, N ≤ M →
          ∀ (S : ℝ) [Fact (0 < S)] (hS : S = (M:ℝ)*e (2*Real.pi)),
            let E := circlePeriodicExtension (e (2*Real.pi)) S M hS
            let H := E (q^2)
            let H₁ := E ((2:ℂ) • (q*p))
            let H₂ := E (1-(3:ℂ) • (q^4))
            circleSpectralGap S H H₁ H₂ ≤ K/(M:ℝ)^2) ∧
        ∃ a : ℝ, 0 < a ∧ 2*(a:ℂ)^2*unitSquarePeriods.weierstrassP (1/2) = 1 ∧
          e (2*Real.pi) = 2/a ∧
          (2*Real.pi/e (2*Real.pi))^2 = CoarseArithmetic.lemniscateFrequencySquared ∧
          (fun x : ℝ => (q (x:AddCircle (e (2*Real.pi))))^2) = normalizedWeierstrass a ∧
          (fun x : ℝ => 2*(q (x:AddCircle (e (2*Real.pi)))*
            p (x:AddCircle (e (2*Real.pi))))) = normalizedWeierstrassDerivative a := by
  obtain ⟨e,he,hT,hqper,hpper,hq0,hp0,hODE⟩ := bernoulli_arclength_profile
  let T := e (2*Real.pi)
  letI : Fact (0 < T) := ⟨hT⟩
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
  have hfrequencyA : (Real.pi*a)^2 = CoarseArithmetic.lemniscateFrequencySquared :=
    square_weierstrass_frequency_squared a hnorm
  have hfrequency : (2*Real.pi/T)^2 = CoarseArithmetic.lemniscateFrequencySquared := by
    have hw : 2*Real.pi/T = Real.pi*a := by
      dsimp only [T]
      rw [hperiod]
      field_simp [ha.ne']
    rw [hw]
    exact hfrequencyA
  have hFourier := circle_weierstrass_fourier_data T a ha.ne' hperiod hnorm (q^2) (fun x => by
    change (q (x:AddCircle T))^2 = normalizedWeierstrass a x
    exact congrFun hW.1 x)
  have hcoeff (j : ℕ) : fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (CoarseArithmetic.fourierCoefficient CoarseArithmetic.lemniscateFrequencySquared
        CoarseArithmetic.nome j:ℂ) := by
    have h := hFourier.2.1 j
    rw [hfrequencyA] at h
    exact h
  have hodd (n : ℤ) : fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0 :=
    hFourier.2.2 (2*n+1) ⟨n,by ring⟩
  refine ⟨e,he,hT,q,p,hqD,hpD,henergy,hqreal,hpreal,hq0C,hp0C,hcurv,
    hFourier.1,hcoeff,hodd,?_,?_,a,ha,hnorm,hperiod,hfrequency,hW⟩
  · intro M hM S instS hS
    let E := circlePeriodicExtension T S M hS
    let Q := E q
    let P := E p
    let gM : ℝ := if M = 1 then 21/4 else 1/(2*(M:ℝ)^2)
    obtain ⟨R,hR,hRne,hker,hgen,hbound⟩ :=
      paper_periodic_cover_spectrum T S q p hqD hpD henergy hqreal hpreal
        hFourier.1 hcoeff hodd hfrequency M hM hS
    refine ⟨R,hR,hRne,hker,hgen,?_⟩
    have hQ : HasCircleDeriv S Q P :=
      circle_periodic_extension_deriv T S M hS q p hqD
    have hP : HasCircleDeriv S P (-(Q^3)) := by
      simpa only [Q,map_neg,map_pow] using
        circle_periodic_extension_deriv T S M hS _ _ hpD
    have hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1 :=
      fun x => henergy (circleCoverProjection T S M hS x)
    have hQ0 : Q 0 = 1 := by
      have h := circle_periodic_extension_coe T S M hS q 0
      simpa only [E,Q,AddCircle.coe_zero,hq0C] using h
    obtain ⟨D,hDcoe,hDne,hDeig⟩ :=
      circle_profile_dilation_eigenmode S Q P hQ hP hE hQ0
    have hSpec : (-30:ℂ) ∈
        circleSpectrum S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)) :=
      (circle_spectrum_iff_eigenvector S _ _ _ (-30)).mpr ⟨D,hDne,hDeig⟩
    have hupper (w : ℂ)
        (hw : w ∈ circleSpectrum S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)))
        (hwne : w ≠ 0) : w.re ≤ -gM := by
      by_cases hM1 : M = 1
      · simpa only [gM,if_pos hM1] using hbound w hwne hw
      · simpa only [gM,if_neg hM1] using hbound w hwne hw
    exact (circle_spectral_gap_bounds S _ _ _ gM 30 hupper
      (-30) hSpec (by norm_num) (by norm_num)).1
  · obtain ⟨K,hK,N,hN,hlarge⟩ :=
      paper_cover_sharp_gap_bounds T q p hqD hpD henergy hqreal hpreal
        hFourier.1 hcoeff hodd hfrequency
    refine ⟨K,hK,N,hN,?_⟩
    intro M hMN S instS hS
    obtain ⟨w,hw,hwne,hlower,hupper,hgaplower,hgapupper⟩ := hlarge M hMN S hS
    exact hgapupper

end Lemniscate
