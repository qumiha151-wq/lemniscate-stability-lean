import Lemniscate.PeriodicSingleSpectrum
import Lemniscate.PeriodicPerturbedFredholm
import Lemniscate.NeutralAdjointVector

/-! Existence and uniqueness of the exact normalized adjoint zero vector for
the actual single-period operator. Its H4 regularity is derived from the
maximal adjoint-domain theorem. The Jacobi profile data remain explicit. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleUnitRotation (q p : C(AddCircle T, ℂ)) : CircleL2 T :=
  ((‖circleContinuousL2 T (q*p)‖:ℂ)⁻¹) • circleContinuousL2 T (q*p)

theorem circle_adjoint_zero_of_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (ψ : CircleL2 T)
    (hψ : ∀ f : circleH4Domain T, inner ℂ ψ (circleH4Operator T h h₁ h₂ f) = 0) :
    ∃ g : circleH4Domain T, (g : CircleL2 T) = ψ ∧ circleH4FormalAdjoint T h h₁ g = 0 := by
  have hg : ψ ∈ (circleH4PMap T h h₁ h₂).adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists ψ ⟨0, fun f => by
      change inner ℂ (0 : CircleL2 T) (f : CircleL2 T) = inner ℂ ψ (circleH4Operator T h h₁ h₂ f)
      rw [inner_zero_left, hψ f]⟩
  have hH4 : ψ ∈ circleH4Domain T := by
    rw [circle_hilbert_adjoint_domain T h h₁ h₂ hh hh₁ hreal h₁real h₂real] at hg
    exact hg
  have hz : (circleH4PMap T h h₁ h₂).adjoint ⟨ψ, hg⟩ = 0 := by
    apply LinearPMap.adjoint_apply_eq (circle_h4_pmap_dense T h h₁ h₂)
    intro f
    change inner ℂ (0 : CircleL2 T) (f : CircleL2 T) = inner ℂ ψ (circleH4Operator T h h₁ h₂ f)
    rw [inner_zero_left, hψ f]
  refine ⟨⟨ψ, hH4⟩, rfl, ?_⟩
  rw [← circle_h4_hilbert_adjoint_value T h h₁ h₂ hh hh₁ hreal h₁real h₂real ⟨ψ, hH4⟩ hg]
  exact hz

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ i : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*i+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter)

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_single_period_adjoint_pairing :
    ∃! ψ : CircleL2 T, inner ℂ ψ (circleUnitRotation T q p) = 1 ∧
      ∀ f : circleH4Domain T,
        inner ℂ ψ (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f) = 0 := by
  let N := paperSinglePeriodNeutralOperator T q p hq hp he hqreal hpreal hs hc ho hr
  let K : CircleL2 T →L[ℂ] CircleL2 T :=
    InnerProductSpace.rankOne ℂ (N.neutral : CircleL2 T) (N.neutral : CircleL2 T)
  have hB (f : circleH4Domain T) :
      circlePerturbedShift T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) 0 K f =
        (inner ℂ (N.neutral : CircleL2 T) (f : CircleL2 T)) • (N.neutral : CircleL2 T)-N.op f := by
    change (0:ℂ) • (f : CircleL2 T)-N.op f+K (f : CircleL2 T) = _
    simp only [zero_smul, zero_sub, K, InnerProductSpace.rankOne_apply]
    abel
  have hinj (f : circleH4Domain T)
      (hf : circlePerturbedShift T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) 0 K f = 0) :
      (f : CircleL2 T) = 0 := by
    rw [hB] at hf
    exact N.neutral_rank_one_shift_kernel f hf
  obtain ⟨R, _, hR⟩ := circle_perturbed_inverse_of_kernel T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) 0 K hinj
  apply N.exists_unique_adjoint_neutral_of_inverse R
  · intro f
    obtain ⟨u, _, hu⟩ := hR.1 f
    exact ⟨u, by simpa only [hB] using hu⟩
  · intro u
    calc
      _ = R (circlePerturbedShift T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) 0 K u) :=
        congrArg R (hB u).symm
      _ = _ := hR.2 u

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_single_period_adjoint_vector :
    ∃! ψ : circleH4Domain T, inner ℂ (ψ : CircleL2 T) (circleUnitRotation T q p) = 1 ∧
      circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0 := by
  have h0real : ∀ x, conj ((q^2 : C(AddCircle T, ℂ)) x) = (q^2 : C(AddCircle T, ℂ)) x := by
    intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow, hqreal]
  have h1real : ∀ x, conj (((2:ℂ) • (q*p)) x) = ((2:ℂ) • (q*p)) x := by
    intro x
    change conj (2*(q x*p x)) = 2*(q x*p x)
    simp only [map_mul, map_ofNat, hqreal, hpreal]
  have h2real : ∀ x, conj ((1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x) =
      (1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x := by
    intro x
    change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub, map_mul, map_one, map_ofNat, map_pow, hqreal]
  have hh := circle_profile_square_deriv T q p hq
  have hh₁ := circle_profile_square_second T q p hq hp he
  obtain ⟨ψ, hψ, huniq⟩ := paper_single_period_adjoint_pairing T q p hq hp he hqreal hpreal hs hc ho hr
  obtain ⟨g, hg, hAg⟩ := circle_adjoint_zero_of_pairing T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) hh hh₁ h0real h1real h2real ψ hψ.2
  refine ⟨g, ⟨by simpa only [hg] using hψ.1, hAg⟩, ?_⟩
  intro g' hg'
  apply Subtype.ext
  rw [hg]
  apply huniq (g' : CircleL2 T)
  refine ⟨hg'.1, ?_⟩
  intro f
  rw [← inner_conj_symm,
    circle_h4_formal_adjoint_green T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      hh hh₁ h0real h1real h2real f g', hg'.2, inner_zero_right, map_zero]

end Profile
end Lemniscate
