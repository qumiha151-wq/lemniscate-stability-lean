import Lemniscate.BernoulliSobolevLinearization
import Lemniscate.PeriodicProfileCoverSpectrum
import Lemniscate.PeriodicCoverEmbeddingH4
import Lemniscate.PeriodicCoverParseval
import Lemniscate.NormalGraphModulation

/-! The actual adjoint functional on every positive cover of the Bernoulli
profile. The zero Bloch lift of the normalized short-period adjoint vector
annihilates the full covered operator, and has nonzero pairing with its
geometric rotation field. These facts discharge the hypotheses of the
normal-graph modulation theorem. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

private theorem circle_cover_zero_embedding_real (M : ℕ) (hM : 0 < M)
    (f : CircleL2 T) (hf : circleConjugate T f = f) :
    circleConjugate S (circleCoverEmbedding T S M hM 0 f) =
      circleCoverEmbedding T S M hM 0 f := by
  apply circle_fourier_ext S
  intro n
  rw [circle_conjugate_fourier]
  by_cases hn : ∃ k : ℤ, circleCoverIndex M 0 k = n
  · obtain ⟨k,rfl⟩ := hn
    rw [show -circleCoverIndex M 0 k = circleCoverIndex M 0 (-k) by simp [circleCoverIndex],
      circle_cover_embedding_fourier_index,circle_cover_embedding_fourier_index,
      ← circle_conjugate_fourier,hf]
  · have hneg : ¬∃ k : ℤ, circleCoverIndex M 0 k = -n := by
      rintro ⟨k,hk⟩
      exact hn ⟨-k,by simpa [circleCoverIndex] using congrArg Neg.neg hk⟩
    rw [circle_cover_embedding_fourier_zero T S M hM 0 (-n) f hneg,
      circle_cover_embedding_fourier_zero T S M hM 0 n f hn,map_zero]

private theorem circle_periodic_cover_modulation_data
    (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0) :
    let E := circlePeriodicExtension T S M hS
    let Q := E q
    let P := E p
    let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
    let K := circleBernoulliBackground S Q P
    inner ℂ (Ψ:CircleL2 S) (circleContinuousL2 S K.b) ≠ 0 ∧
      (∀ f : circleH4Domain S,
        inner ℂ (Ψ:CircleL2 S)
          (circleH4Operator S (Q^2) ((2:ℂ) • (Q*P))
            (1-(3:ℂ) • (Q^4)) f) = 0) ∧
      circleNormalGraphFlow S K (15/2) 0 = 0 ∧
      ∀ f : CircleSobolevSpace S 4,
        circleNormalGraphRotationFunctional S (Ψ:CircleL2 S)
          (circleNormalGraphDerivative S K (15/2) f) = 0 := by
  let E := circlePeriodicExtension T S M hS
  let Q := E q
  let P := E p
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  let K := circleBernoulliBackground S Q P
  have hQ : HasCircleDeriv S Q P :=
    circle_periodic_extension_deriv T S M hS q p hq
  have hP : HasCircleDeriv S P (-(Q^3)) := by
    simpa only [Q,map_neg,map_pow] using
      circle_periodic_extension_deriv T S M hS _ _ hp
  have hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1 :=
    fun x => he (circleCoverProjection T S M hS x)
  have hMZ : (M:ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hmulti (n : ℤ) :
      fourierCoeff (Q^2 : C(AddCircle S, ℂ)) ((M:ℤ)*n) =
        fourierCoeff (q^2 : C(AddCircle T, ℂ)) n := by
    have h := circle_periodic_extension_fourier T S M hM hS (q^2) ((M:ℤ)*n)
    simpa [E,Q,map_pow,Int.mul_ediv_cancel_left _ hMZ] using h
  have hvanish (n : ℤ) (hn : ¬(M:ℤ) ∣ n) :
      fourierCoeff (Q^2 : C(AddCircle S, ℂ)) n = 0 := by
    have h := circle_periodic_extension_fourier T S M hM hS (q^2) n
    simpa only [if_neg hn,map_pow] using h
  have h0real : ∀ x, conj ((q^2 : C(AddCircle T, ℂ)) x) =
      (q^2 : C(AddCircle T, ℂ)) x := by
    intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow,hqreal]
  have h1real : ∀ x, conj (((2:ℂ) • (q*p)) x) = ((2:ℂ) • (q*p)) x := by
    intro x
    change conj (2*(q x*p x)) = 2*(q x*p x)
    simp only [map_mul,map_ofNat,hqreal,hpreal]
  have h2real : ∀ x, conj ((1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x) =
      (1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x := by
    intro x
    change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub,map_mul,map_one,map_ofNat,map_pow,hqreal]
  have hannihilate (f : circleH4Domain T) :
      inner ℂ (ψ:CircleL2 T)
        (circleH4Operator T (q^2) ((2:ℂ) • (q*p))
          (1-(3:ℂ) • (q^4)) f) = 0 := by
    rw [← inner_conj_symm,circle_h4_formal_adjoint_green T (q^2)
      ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circle_profile_square_deriv T q p hq)
      (circle_profile_square_second T q p hq hp he) h0real h1real h2real f ψ,
      hψzero,inner_zero_right,map_zero]
  have hcover (f : circleH4Domain S) :
      inner ℂ (Ψ:CircleL2 S)
        (circleH4Operator S (Q^2) ((2:ℂ) • (Q*P))
          (1-(3:ℂ) • (Q^4)) f) = 0 := by
    rw [show (Ψ:CircleL2 S) =
      circleCoverEmbedding T S M hM 0 (ψ:CircleL2 T) from rfl,
      circle_cover_embedding_inner,
      circle_cover_operator_intertwine T S M hM hS _ _ _ _ _ _
        (circle_profile_square_deriv T q p hq)
        (circle_profile_square_second T q p hq hp he)
        (circle_profile_square_deriv S Q P hQ)
        (circle_profile_square_second S Q P hQ hP hE) hmulti hvanish]
    simpa only [Int.cast_zero,zero_div,circle_bloch_at_zero] using
      hannihilate (circleCoverComponentH4 T S M hM hS 0 f)
  have hpairbase : inner ℂ (ψ:CircleL2 T) (circleContinuousL2 T (q*p)) ≠ 0 := by
    intro hz
    have h := hnorm
    simp only [circleUnitRotation,inner_smul_right,hz,mul_zero] at h
    exact zero_ne_one h
  have hsqrt : ((Real.sqrt 2:ℝ):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
  have hpair : inner ℂ (Ψ:CircleL2 S) (circleContinuousL2 S K.b) ≠ 0 := by
    change inner ℂ (circleCoverEmbedding T S M hM 0 (ψ:CircleL2 T))
      (circleContinuousL2 S (((Real.sqrt 2:ℝ):ℂ) • (Q*P))) ≠ 0
    rw [circle_continuous_l2_smul,inner_smul_right,circle_cover_embedding_inner,
      circle_cover_rotation_component T S M hM hS q p hq Q P hQ hmulti]
    exact mul_ne_zero hsqrt hpairbase
  have hlin := bernoulli_sobolev_flow_linearization S Q P hE
  have hoperator : circleNormalGraphDerivative S K (15/2) =
      circleSobolevOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)) :=
    (circle_normal_graph_hasFDerivAt S K (15/2)).unique hlin.2
  refine ⟨hpair,hcover,hlin.1,?_⟩
  intro f
  change inner ℂ (Ψ:CircleL2 S) (circleNormalGraphDerivative S K (15/2) f) = 0
  rw [hoperator,circle_sobolev_operator_eq_h4]
  exact hcover (circleSobolevToH4Domain S f)

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

/-- Every positive cover has a genuine adjoint phase functional for the
normal-graph equation. Its modulation preserves the actual linearization
and satisfies the mixed H2-H4 remainder bound on a true H2 neighborhood. -/
theorem paper_periodic_cover_modulated_tame
    (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T) :
    ∃ ψ : circleH4Domain T,
      inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1 ∧
      circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0 ∧
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
  obtain ⟨ψ,hnorm,hψzero,hreal,_,hd⟩ :=
    paper_single_period_neutral_decomposition T q p hq hp he hqreal hpreal hs hc ho hr
  obtain ⟨hpair,hcover,hzero,hneutral⟩ :=
    circle_periodic_cover_modulation_data T S q p hq hp he hqreal hpreal
      M hM hS ψ hnorm hψzero
  refine ⟨ψ,hnorm,hψzero,hreal,hd,?_,hpair,hcover,?_⟩
  · exact circle_cover_zero_embedding_real T S M hM (ψ:CircleL2 T) hreal
  · exact circle_normal_graph_modulated_tame S
      (circleBernoulliBackground S
        (circlePeriodicExtension T S M hS q) (circlePeriodicExtension T S M hS p))
      (15/2) (circleCoverEmbeddingH4 T S M hM hS 0 ψ:CircleL2 S)
      hpair hzero hneutral

end Profile
end Lemniscate
