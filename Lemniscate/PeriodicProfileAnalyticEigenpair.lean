import Lemniscate.PeriodicAnalyticEigenpair
import Lemniscate.PeriodicEigenvalueCoordinates
import Lemniscate.PeriodicAnalyticBranchSymmetry
import Lemniscate.PeriodicAdjointSymmetry
import Lemniscate.AnalyticEvenQuadratic

/-! The analytic eigenpair for the actual H4-domain Bloch operator.
The linearized normalized equation is proved invertible; it is not an
additional spectral hypothesis. Profile and Fourier data remain explicit. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic Filter
open scoped ComplexConjugate Topology
variable (T : ℝ) [Fact (0 < T)]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter)
include hq hp he hqreal hpreal hs hc ho hr

theorem paper_analytic_bloch_eigenpair_exists :
    ∃ ψ : CircleL2 T, ∃ μ : ℂ → ℂ, ∃ g : ℂ → CircleL2 T,
      AnalyticAt ℂ μ 0 ∧ AnalyticAt ℂ g 0 ∧ μ 0 = 0 ∧
      g 0 = circleUnitRotation T q p ∧
      (∀ᶠ z in 𝓝 (0:ℂ), μ (-z) = μ z) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 (0:ℂ), ‖μ z‖ ≤ C*‖z‖^2) ∧
      (∀ᶠ z in 𝓝 (0:ℂ), inner ℂ ψ (g z) = 1 ∧ g z ≠ 0) ∧
      (∀ᶠ (α : ℝ) in 𝓝 0, ∃ u : circleH4Domain T,
        (u:CircleL2 T) = g (α:ℂ) ∧
        circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α u =
          μ (α:ℂ) • g (α:ℂ)) := by
  let N := paperSinglePeriodNeutralOperator T q p hq hp he hqreal hpreal hs hc ho hr
  let e : circleH4Domain T := N.neutral
  let x := circlePrincipalShift T 1 e
  let R := circlePrincipalResolvent T 1 (by norm_num)
  have hRx : R x = circleUnitRotation T q p := by
    change (circlePrincipalResolventH4 T 1 (by norm_num) (circlePrincipalShift T 1 e):CircleL2 T) = _
    rw [circle_principal_resolvent_h4_left_inverse]
    rfl
  have hRxe : circlePrincipalResolventH4 T 1 (by norm_num) x = e :=
    circle_principal_resolvent_h4_left_inverse T 1 (by norm_num) e
  obtain ⟨ψ,hn,hψ,I,hI⟩ := paper_eigenvalue_linearization_exists T q p hq hp he
    hqreal hpreal hs hc ho hr 1 (by norm_num)
  have hx : circlePrincipalBlochCoefficient T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) 1 (by norm_num) 0 x = 0 := by
    rw [circle_principal_bloch_coefficient_apply,circle_bloch_coefficient_zero]
    simp only [one_pow]
    rw [hRxe]
    exact N.kills_neutral
  have hn' : inner ℂ ψ (circlePrincipalResolvent T (1^4) (by positivity) x) = 1 := by
    simp only [one_pow]
    change inner ℂ ψ (R x) = 1
    rw [hRx]
    exact hn
  have hI' (a : ℂ) (f : CircleL2 T) : I (a,f) =
      (circlePrincipalBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) 1 (by norm_num) 0 f-
        a • circlePrincipalResolvent T (1^4) (by positivity) x,
        inner ℂ ψ (circlePrincipalResolvent T (1^4) (by positivity) f)) := by
    have hi := hI a f
    rw [← hRx] at hi
    simpa only [one_pow,R] using hi
  obtain ⟨μ,f,hμ,hf,hμ0,hf0,hsol,U,hU,hU0,huniq⟩ := circle_analytic_eigenpair_exists T
    (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) 1 (by norm_num) ψ x hx hn' I hI'
  obtain ⟨φ,hφ,huniqφ⟩ := paper_single_period_adjoint_pairing T q p hq hp he hqreal hpreal hs hc ho hr
  have hψeq : ψ = φ := huniqφ ψ ⟨hn,hψ⟩
  have hψuniq (ψ' : CircleL2 T) (hψ' : inner ℂ ψ' (circleUnitRotation T q p) = 1 ∧
      ∀ u : circleH4Domain T, inner ℂ ψ'
        (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) u) = 0) : ψ' = ψ :=
    (huniqφ ψ' hψ').trans hψeq.symm
  have hψR := circle_adjoint_pairing_reflect T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) (circle_profile_square_deriv T q p hq)
    (circle_profile_square_second T q p hq hp he) hs (circleUnitRotation T q p) ψ
    (circle_unit_rotation_reflect T q p hq hs) ⟨hn,hψ⟩ hψuniq
  have hecoe : (e:CircleL2 T) = circleUnitRotation T q p := rfl
  have heR : circleReflectH4 T e = -e := by
    apply Subtype.ext
    change circleReflect T (e:CircleL2 T) = -(e:CircleL2 T)
    rw [hecoe]
    exact circle_unit_rotation_reflect T q p hq hs
  have hxR : -circleReflect T x = x := by
    have hrx := circle_principal_shift_reflect T 1 e
    rw [heR,map_neg] at hrx
    change -x = circleReflect T x at hrx
    rw [← hrx,neg_neg]
  have heven := circle_analytic_eigenvalue_even T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) 1 (by norm_num) ψ x μ f hμ hf hμ0 hf0 hsol U hU hU0 huniq
    (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
    hs hψR hxR
  have hquad := analytic_even_quadratic_bound μ hμ hμ0 heven
  simp only [one_pow] at hsol
  let g : ℂ → CircleL2 T := fun z => R (f z)
  have hg : AnalyticAt ℂ g 0 := (R.analyticAt (f 0)).comp hf
  have hg0 : g 0 = circleUnitRotation T q p := by
    change R (f 0) = _
    rw [hf0,hRx]
  refine ⟨ψ,μ,g,hμ,hg,hμ0,hg0,heven,hquad,?_,?_⟩
  · filter_upwards [hsol] with z hz
    exact ⟨hz.2.1,hz.2.2⟩
  · have hreal : Tendsto (fun α : ℝ => (α:ℂ)) (𝓝 0) (𝓝 (0:ℂ)) :=
      Complex.continuous_ofReal.continuousAt
    filter_upwards [hreal hsol] with α hα
    refine ⟨circlePrincipalResolventH4 T 1 (by norm_num) (f (α:ℂ)),rfl,?_⟩
    have hfamily := circle_principal_bloch_family_real T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) 1 (by norm_num) α (f (α:ℂ))
    simp only [one_pow] at hfamily
    rw [← hfamily]
    exact hα.1

end Profile
end Lemniscate
