import Lemniscate.PeriodicPrincipalBlochCoefficients
import Lemniscate.NeutralEigenvalueLinearization
import Lemniscate.PeriodicAdjointNeutral

/-! The principal inverse is a linear bijection onto the actual H4 domain.
The normalized eigenvalue linearization is instantiated for the paper's
operator, with rank-one solvability proved by the existing Fredholm theorem. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circlePrincipalDomainMap (r : ℝ) (hr : 0 < r) :
    CircleL2 T →ₗ[ℂ] circleH4Domain T :=
  (circlePrincipalResolvent T r hr).toLinearMap.codRestrict (circleH4Domain T)
    (circle_principal_resolvent_mem_h4 T r hr)

theorem circle_principal_domain_map_apply (r : ℝ) (hr : 0 < r) (f : CircleL2 T) :
    circlePrincipalDomainMap T r hr f = circlePrincipalResolventH4 T r hr f := rfl

theorem circle_principal_domain_map_bijective (r : ℝ) (hr : 0 < r) :
    Function.Bijective (circlePrincipalDomainMap T r hr) := by
  constructor
  · intro f g hfg
    have h := congrArg (circlePrincipalShift T r) hfg
    simpa only [circle_principal_domain_map_apply,circle_principal_resolvent_right_inverse] using h
  · intro u
    refine ⟨circlePrincipalShift T r u,?_⟩
    rw [circle_principal_domain_map_apply,circle_principal_resolvent_h4_left_inverse]

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

theorem paper_eigenvalue_linearization_exists (b : ℝ) (hb : 1 ≤ b) :
    ∃ ψ : CircleL2 T, inner ℂ ψ (circleUnitRotation T q p) = 1 ∧
      (∀ u : circleH4Domain T, inner ℂ ψ
        (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) u) = 0) ∧
      ∃ I : (ℂ × CircleL2 T) ≃L[ℂ] (CircleL2 T × ℂ), ∀ a : ℂ, ∀ f : CircleL2 T,
        I (a,f) = (circlePrincipalBlochCoefficient T (q^2) ((2:ℂ) • (q*p))
          (1-(3:ℂ) • (q^4)) b hb 0 f-a • circleUnitRotation T q p,
          inner ℂ ψ (circlePrincipalResolvent T (b^4) (by positivity) f)) := by
  let N := paperSinglePeriodNeutralOperator T q p hq hp he hqreal hpreal hs hc ho hr
  have hneutral : (N.neutral:CircleL2 T) = circleUnitRotation T q p := rfl
  obtain ⟨ψ,⟨hnorm,hψ⟩,_⟩ := paper_single_period_adjoint_pairing T q p hq hp he hqreal hpreal hs hc ho hr
  have hnormN : inner ℂ ψ (N.neutral:CircleL2 T) = 1 := by rw [hneutral]; exact hnorm
  have hψN (u : N.domain) : inner ℂ ψ (N.op u) = 0 := hψ u
  let K : CircleL2 T →L[ℂ] CircleL2 T :=
    InnerProductSpace.rankOne ℂ (N.neutral:CircleL2 T) (N.neutral:CircleL2 T)
  have hB (u : N.domain) : circlePerturbedShift T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) 0 K u =
        inner ℂ (N.neutral:CircleL2 T) (u:CircleL2 T) • (N.neutral:CircleL2 T)-N.op u := by
    change (0:ℂ) • (u:CircleL2 T)-N.op u+K (u:CircleL2 T) = _
    simp only [zero_smul,zero_sub,K,InnerProductSpace.rankOne_apply]
    abel
  have hinj (u : circleH4Domain T)
      (hu : circlePerturbedShift T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) 0 K u = 0) :
      (u:CircleL2 T) = 0 := by
    exact N.neutral_rank_one_shift_kernel u ((hB u).symm.trans hu)
  obtain ⟨Rstable,_,hstable⟩ := circle_perturbed_inverse_of_kernel T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) 0 K hinj
  have hsolve (y : CircleL2 T) : ∃ u : N.domain,
      inner ℂ (N.neutral:CircleL2 T) (u:CircleL2 T) • (N.neutral:CircleL2 T)-N.op u = y := by
    obtain ⟨u,_,hu⟩ := hstable.1 y
    exact ⟨u,(hB u).symm.trans hu⟩
  let R := circlePrincipalResolvent T (b^4) (by positivity)
  let RD : CircleL2 T →ₗ[ℂ] N.domain := circlePrincipalDomainMap T (b^4) (by positivity)
  let C := circlePrincipalBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) b hb 0
  have hR (f : CircleL2 T) : (RD f:CircleL2 T) = R f := rfl
  have hRbij : Function.Bijective RD := circle_principal_domain_map_bijective T (b^4) (by positivity)
  have hC (f : CircleL2 T) : C f = N.op (RD f) := by
    change circlePrincipalBlochCoefficient T _ _ _ b hb 0 f =
      circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
        (circlePrincipalResolventH4 T (b^4) (by positivity) f)
    rw [circle_principal_bloch_coefficient_apply,circle_bloch_coefficient_zero]
  let I := normalizedPencilLinearizationEquiv N ψ hnormN hψN hsolve R C RD hR hRbij hC
  refine ⟨ψ,hnorm,hψ,I,?_⟩
  intro a f
  change normalizedPencilLinearization C R (N.neutral:CircleL2 T) ψ (a,f) = _
  rw [normalized_pencil_linearization_apply,hneutral]

end Profile
end Lemniscate
