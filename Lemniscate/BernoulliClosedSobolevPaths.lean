import Lemniscate.BernoulliPhysicalGraphStability
import Lemniscate.ContinuousInitialTraceExtension

/-! Retain every actual Sobolev representative of the given evolution,
including the initial endpoint, on one common closed time domain. -/
noncomputable section
namespace Lemniscate
open Set
open scoped Topology NNReal

theorem bernoulli_closed_sobolev_paths
    (T : ℝ) [Fact (0<T)] (q p : C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (τ : ℝ) (hτ : 0<τ) (η : ℝ) (x₀ : CircleSobolevSpace T 2)
    (D : BernoulliNormalGraphEvolution T q p ψ τ hτ η x₀) :
    ∃ v : ∀ n : ℕ, ℝ → CircleSobolevSpace T (n+2),
      (∀ n, ContinuousOn (v n) (Ici (0:ℝ))) ∧
      (∀ n t, t ∈ Ici (0:ℝ) →
        circleSobolevCoordinate T (n+2) 0 (v n t) =
          circleSobolevCoordinate T 2 0 (D.u (Real.toNNReal t))) ∧
      (∀ n, v n 0 = D.initialLifts (n+2) 0) ∧
      ∀ n t (ht : 0<t), v n t = D.w (n+2) ⟨t,ht⟩ := by
  have hpaths (n : ℕ) := continuous_initial_trace_extension
    (circleSobolevCoordinate T (n+2) 0) (circle_sobolev_value_injective T (n+2))
    (fun t : ℝ => circleSobolevCoordinate T 2 0 (D.u (Real.toNNReal t)))
    τ hτ (D.w (n+2)) (D.initialLifts (n+2))
    (by
      intro t
      have hc : Real.toNNReal (t:ℝ) = (⟨(t:ℝ),t.property.le⟩ : ℝ≥0) :=
        Subtype.ext (Real.coe_toNNReal (t:ℝ) t.property.le)
      simpa only [hc] using D.positiveValue (n+2) t)
    (by
      intro r
      have hc : circleParabolicSegmentTime τ hτ 0 r = Real.toNNReal (τ*(r:ℝ)) := by
        apply Subtype.ext
        simpa only [circleParabolicSegmentTime,Nat.cast_zero,zero_div,zero_add] using!
          (Real.coe_toNNReal (τ*(r:ℝ)) (mul_nonneg hτ.le r.property.1)).symm
      calc
        _ = circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ (D.U 0) r) :=
          D.initialValues (n+2) r
        _ = circleSobolevCoordinate T 2 0
            (D.u (circleParabolicSegmentTime τ hτ 0 r)) :=
          congrArg (circleSobolevCoordinate T 2 0) (D.segments 0 r).symm
        _ = _ := by rw [hc])
  choose v hv using hpaths
  exact ⟨v,fun n => (hv n).1,fun n => (hv n).2.1,
    fun n => (hv n).2.2.1,fun n => (hv n).2.2.2⟩

end Lemniscate
