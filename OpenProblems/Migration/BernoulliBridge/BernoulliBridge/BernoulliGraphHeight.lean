import Lemniscate.BernoulliPhysicalGraphStability

noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set CoarseArithmetic
open scoped ContDiff Topology NNReal ENNReal ComplexConjugate

/-- A small bound on each parabolic segment controls the actual normal height at
every normalized time, including the initial slice. -/
theorem bernoulli_all_time_height_bound
    (S : ℝ) [Fact (0<S)] {q p : C(AddCircle S,ℂ)} {ψ : CircleL2 S}
    {τ : ℝ} {hτ : 0<τ} {η : ℝ} {x₀ : CircleSobolevSpace S 2}
    (D : BernoulliNormalGraphEvolution S q p ψ τ hτ η x₀)
    (σ s : ℝ) :
    |((circleSobolevH1Embedding S (circleSobolevInclusion S 1 (D.u (Real.toNNReal σ))))
      ((Real.sqrt 2*s):AddCircle S)).re| ≤ (‖circleSobolevH1Embedding S‖+1)*η := by
  let t := Real.toNNReal σ
  have hcover : ∃ (m : ℕ) (r : unitInterval),circleParabolicSegmentTime τ hτ m r=t := by
    by_cases hz : t=0
    · refine ⟨0,0,?_⟩
      rw [hz]
      apply Subtype.ext
      norm_num [circleParabolicSegmentTime]
    · have ht : 0<(t:ℝ) := lt_of_le_of_ne t.property (by
        intro he
        apply hz
        exact Subtype.ext he.symm)
      obtain ⟨m,r,_,_,h⟩ := circle_parabolic_interior_time τ hτ t ht t le_rfl
      exact ⟨m,r,h⟩
  obtain ⟨m,r,hr⟩ := hcover
  have hu : ‖D.u t‖≤η := by
    rw [←hr,D.segments]
    calc
      _ ≤ ‖circleParabolicCurve S τ (D.U m)‖ := (circleParabolicCurve S τ (D.U m)).norm_coe_le_norm r
      _ ≤ ‖D.U m‖ := norm_fst_le (D.U m).val
      _ ≤ η := (D.segmentSmall m).le
  have hincl : ‖circleSobolevInclusion S 1 (D.u t)‖ ≤ ‖D.u t‖ :=
    ContinuousLinearMap.le_of_opNorm_le _ (circle_sobolev_inclusion_norm_le S 1) _ |>.trans_eq (one_mul _)
  calc
    _ ≤ ‖(circleSobolevH1Embedding S (circleSobolevInclusion S 1 (D.u t))) ((Real.sqrt 2*s):AddCircle S)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖circleSobolevH1Embedding S (circleSobolevInclusion S 1 (D.u t))‖ :=
      ContinuousMap.norm_coe_le_norm _ _
    _ ≤ ‖circleSobolevH1Embedding S‖ * ‖circleSobolevInclusion S 1 (D.u t)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖circleSobolevH1Embedding S‖+1)*η :=
      mul_le_mul (by linarith) (hincl.trans hu) (norm_nonneg _) (by positivity)

end Lemniscate
