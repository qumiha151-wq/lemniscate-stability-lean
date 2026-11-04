import Lemniscate.BernoulliCoverModulation

/-! The actual cover modulation data for a specified normalized adjoint
vector.  Adjoint uniqueness identifies the vector already constructed by
the profile theorem with the supplied vector.  All nonlinear estimates
are the existing estimates for that same actual profile.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

set_option maxHeartbeats 800000 in
/-- Every normalized adjoint vector has the same actual cover modulation
and mixed H2-H4 tame data, by uniqueness of the normalized adjoint vector. -/
theorem paper_periodic_cover_modulated_tame_data
    (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T) :
    circleConjugate T (ψ:CircleL2 T) = (ψ:CircleL2 T) ∧
      HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p))
        (1-(3:ℂ) • (q^4)) (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T) ∧
      let E := circlePeriodicExtension T S M hS
      let Q := E q
      let P := E p
      let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
      let K := circleBernoulliBackground S Q P
      circleConjugate S (Ψ:CircleL2 S) = (Ψ:CircleL2 S) ∧
        inner ℂ (Ψ:CircleL2 S) (circleContinuousL2 S K.b) ≠ 0 ∧
        (∀ f : circleH4Domain S,
          inner ℂ (Ψ:CircleL2 S)
            (circleH4Operator S (Q^2) ((2:ℂ) • (Q*P))
              (1-(3:ℂ) • (Q^4)) f) = 0) ∧
        circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S) 0 = 0 ∧
        HasFDerivAt (circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S))
          (circleNormalGraphDerivative S K (15/2)) 0 ∧
        ∃ δ > 0, ∃ C > 0,
          (∀ f : CircleSobolevSpace S 4,
            ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖ < δ →
            circleNormalGraphRotationFunctional S (Ψ:CircleL2 S)
              (circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S) f) = 0) ∧
          ∀ f g : CircleSobolevSpace S 4,
            ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖ < δ →
            ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 g)‖ < δ →
            ‖circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S) f-
                circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S) g-
                circleNormalGraphDerivative S K (15/2) (f-g)‖ ≤
              C*((‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖+
                    ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 g)‖)*‖f-g‖+
                (‖f‖+‖g‖)*
                  ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 (f-g))‖) := by
  obtain ⟨ψ',hnorm',hzero',hreal,hd,hdata⟩ :=
    paper_periodic_cover_modulated_tame T S q p hq hp he hqreal hpreal hs hc ho hr M hM hS
  obtain ⟨ψ₀,_,hunique⟩ :=
    paper_single_period_adjoint_vector T q p hq hp he hqreal hpreal hs hc ho hr
  have hψ : ψ' = ψ := (hunique ψ' ⟨hnorm',hzero'⟩).trans
    (hunique ψ ⟨hnorm,hψzero⟩).symm
  subst ψ'
  exact ⟨hreal,hd,hdata⟩

end Profile
end Lemniscate
