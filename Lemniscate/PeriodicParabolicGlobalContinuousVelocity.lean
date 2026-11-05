import Lemniscate.PeriodicParabolicClassicalTime
import Lemniscate.PeriodicParabolicInitialClassicalTime
import Lemniscate.PeriodicParabolicGlobalClassicalTime
import Lemniscate.PeriodicParabolicInteriorTime

/-! Assemble the actual continuous velocity on the same overlapping MR
segments. Both the positive-time derivative and the initial right derivative
come from the recorded Bochner primitive. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Set
open scoped Topology NNReal

theorem circle_global_hasDerivWithinAt_of_continuous_velocity
    (T : ℝ) [Fact (0<T)] (τ : ℝ) (hτ : 0<τ)
    (u : C(ℝ≥0,CircleSobolevSpace T 2))
    (U : ℕ → CircleParabolicSpace T τ)
    (hrep : ∀ m r, u (circleParabolicSegmentTime τ hτ m r)=
      circleParabolicCurve T τ (U m) r)
    (v : ℝ → C(AddCircle T,ℂ)) (hv : ContinuousOn v (Ici (0:ℝ)))
    (hAE : ∀ m, ∀ᵐ r ∂volume,
      circleParabolicTimeDerivative T τ (U m) r =
        circleContinuousL2 T (v (circleParabolicSegmentTime τ hτ m r))) :
    ∀ t : ℝ, 0≤t → HasDerivWithinAt
      (fun s : ℝ => circleSobolevH1Embedding T
        (circleSobolevInclusion T 1 (u (Real.toNNReal s))))
      (v t) (Ici (0:ℝ)) t := by
  let value : CircleSobolevSpace T 2 → C(AddCircle T,ℂ) :=
    fun f => circleSobolevH1Embedding T (circleSobolevInclusion T 1 f)
  let V (m : ℕ) : C(unitInterval,C(AddCircle T,ℂ)) :=
    ⟨fun r => v (τ*((m:ℝ)/2+(r:ℝ))),
      hv.comp_continuous
        (continuous_const.mul (continuous_const.add continuous_subtype_val))
        (fun r => mul_nonneg hτ.le (add_nonneg (by positivity) r.property.1))⟩
  have hlocal (m : ℕ) (r : unitInterval) :
      HasDerivWithinAt
        (fun s : ℝ => value (circleParabolicCurve T τ (U m)
          (projIcc (0:ℝ) 1 zero_le_one s)))
        (τ • v (circleParabolicSegmentTime τ hτ m r)) (Icc (0:ℝ) 1) (r:ℝ) := by
    have hAE' : ∀ᵐ t : unitInterval ∂volume, 0≤(t:ℝ) →
        circleParabolicTimeDerivative T τ (U m) t =
          circleContinuousL2 T (V m (projIcc (0:ℝ) 1 zero_le_one (t:ℝ))) := by
      filter_upwards [hAE m] with t ht _
      simpa only [projIcc_val,V] using! ht
    have hd := circle_parabolic_hasDerivWithinAt_of_continuous_velocity
      T τ (U m) 0 le_rfl zero_lt_one (V m) hAE' (r:ℝ) r.property.1 r.property.2
    simpa only [value,projIcc_val,V,circleParabolicSegmentTime] using! hd
  have hcover (t : ℝ≥0) (ht : 0<t) :
      ∃ (m : ℕ) (r : unitInterval),
        0<(r:ℝ) ∧ (r:ℝ)<1 ∧ circleParabolicSegmentTime τ hτ m r=t := by
    obtain ⟨m,r,hr1,hlo,heq⟩ := circle_parabolic_interior_time τ hτ t ht t le_rfl
    refine ⟨m,r,?_,hr1,heq⟩
    exact (lt_min (by norm_num : (0:ℝ)<1/2) (div_pos ht hτ)).trans_le hlo
  have hpositive := circle_global_classical_time_derivative τ hτ value u
    (fun m => circleParabolicCurve T τ (U m)) v hrep hcover
      (fun m r hr0 hr1 => (hlocal m r).hasDerivAt (Icc_mem_nhds hr0 hr1))
  intro t ht
  rcases eq_or_lt_of_le ht with hz | hp
  · subst t
    have hc : circleParabolicSegmentTime τ hτ 0 0=0 := by
      apply Subtype.ext
      norm_num [circleParabolicSegmentTime]
    have hvzero : τ • v (circleParabolicSegmentTime τ hτ 0 0)=τ • v 0 :=
      congrArg (fun s : ℝ≥0 => τ • v (s:ℝ)) hc
    exact circle_initial_classical_time_derivative τ hτ value u
      (circleParabolicCurve T τ (U 0)) (v 0) (hrep 0) ((hlocal 0 0).congr_deriv hvzero)
  · exact (hpositive t hp).hasDerivWithinAt

end Lemniscate
