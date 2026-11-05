import Lemniscate.PeriodicParabolicGlobalSolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! An actual overlapping solution has actual parabolic restrictions of
arbitrarily short duration starting at any nonnegative time. This avoids
reconstructing a second classical solution for the uniqueness comparison. -/
noncomputable section
namespace Lemniscate
open MeasureTheory Filter Set
open scoped Topology NNReal

variable (T : ℝ) [Fact (0<T)]

/-- The same global curve solves the same autonomous equation on a true
parabolic interval starting at any time. Its continuous H2 norm does not
increase, while no smallness of the restricted parabolic norm is claimed. -/
theorem circle_parabolic_global_local_restriction
    (τ : ℝ) (hτ : 0<τ) (u : ℝ≥0 → CircleSobolevSpace T 2)
    (U : ℕ → CircleParabolicSpace T τ)
    (hrep : ∀ m r, u (circleParabolicSegmentTime τ hτ m r)=circleParabolicCurve T τ (U m) r)
    (hcover : ∀ σ : ℝ≥0, 0<σ → ∃ (m : ℕ) (r : unitInterval),
      0<(r:ℝ) ∧ (r:ℝ)<1 ∧ circleParabolicSegmentTime τ hτ m r=σ)
    (F : CircleSobolevSpace T 4 → CircleL2 T)
    (hPDE : ∀ m, ∀ᵐ r : unitInterval ∂volume,
      circleParabolicTimeDerivative T τ (U m) r=F (circleParabolicH4 T τ (U m) r))
    (σ₀ : ℝ≥0) (ε : ℝ) (hε : 0<ε) :
    ∃ d>0, d<ε ∧ ∃ m : ℕ, ∃ R : CircleParabolicSpace T d,
      (∀ r : unitInterval, circleParabolicCurve T d R r=
        u (Real.toNNReal ((σ₀:ℝ)+d*(r:ℝ)))) ∧
      circleParabolicInitialValue T d R=u σ₀ ∧
      ‖circleParabolicCurve T d R‖≤‖circleParabolicCurve T τ (U m)‖ ∧
      ∀ᵐ r : unitInterval ∂volume,
        circleParabolicTimeDerivative T d R r=F (circleParabolicH4 T d R r) := by
  have hstart : ∃ (m : ℕ) (a : unitInterval), (a:ℝ)<1 ∧
      circleParabolicSegmentTime τ hτ m a=σ₀ := by
    by_cases hσ : σ₀=0
    · refine ⟨0,0,by norm_num,?_⟩
      subst σ₀
      apply NNReal.coe_injective
      norm_num [circleParabolicSegmentTime] <;> rfl
    · obtain ⟨m,a,_,ha,hEq⟩ := hcover σ₀
        (lt_of_le_of_ne (show (0:ℝ≥0)≤σ₀ from zero_le) (Ne.symm hσ))
      exact ⟨m,a,ha,hEq⟩
  obtain ⟨m,a,ha,hEq⟩ := hstart
  let c := min ((1-(a:ℝ))/2) (ε/(2*τ))
  have hc : 0<c := lt_min (div_pos (sub_pos.mpr ha) (by norm_num))
    (div_pos hε (mul_pos (by norm_num) hτ))
  have hcEnd : c<1-(a:ℝ) := by
    have hb := min_le_left ((1-(a:ℝ))/2) (ε/(2*τ))
    dsimp only [c]
    linarith only [hb,ha]
  let b : unitInterval := ⟨(a:ℝ)+c,⟨add_nonneg a.property.1 hc.le,by linarith only [hcEnd]⟩⟩
  have hab : a<b := by change (a:ℝ)<(a:ℝ)+c; linarith only [hc]
  let d := τ*((b:ℝ)-(a:ℝ))
  have hdEq : d=τ*c := by dsimp only [d,b]; ring
  have hd : 0<d := by rw [hdEq]; exact mul_pos hτ hc
  have hdε : d<ε := by
    have hb : c≤ε/(2*τ) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hb hτ.le
    have heq : τ*(ε/(2*τ))=ε/2 := by field_simp [hτ.ne']
    rw [heq] at hmul
    rw [hdEq]
    linarith only [hmul,hε]
  let R : CircleParabolicSpace T d := circleParabolicRestriction T τ a b hab (U m)
  have hR := circle_parabolic_restriction_components T τ a b hab (U m)
  have hclock (r : unitInterval) : circleParabolicSegmentTime τ hτ m
      (unitTimeAffine a b hab r)=Real.toNNReal ((σ₀:ℝ)+d*(r:ℝ)) := by
    have hbase := congrArg (fun x : ℝ≥0 => (x:ℝ)) hEq
    change τ*((m:ℝ)/2+(a:ℝ))=(σ₀:ℝ) at hbase
    have hreal : τ*((m:ℝ)/2+((a:ℝ)+((b:ℝ)-(a:ℝ))*(r:ℝ)))=
        (σ₀:ℝ)+d*(r:ℝ) := by
      rw [← hbase]
      dsimp only [d]
      ring
    have hsource : (circleParabolicSegmentTime τ hτ m (unitTimeAffine a b hab r):ℝ)=
        τ*((m:ℝ)/2+((a:ℝ)+((b:ℝ)-(a:ℝ))*(r:ℝ))) := rfl
    exact NNReal.coe_injective (hsource.trans (hreal.trans
      (Real.coe_toNNReal _ (add_nonneg σ₀.property (mul_nonneg hd.le r.property.1))).symm))
  refine ⟨d,hd,hdε,m,R,?_,?_,hR.2.2.2.2,?_⟩
  · intro r
    exact (hR.1 r).trans ((hrep m (unitTimeAffine a b hab r)).symm.trans (congrArg u (hclock r)))
  · exact hR.2.2.2.1.trans ((hrep m a).symm.trans (congrArg u hEq))
  · exact circle_parabolic_restriction_pde T τ a b hab F (U m) (hPDE m)

end Lemniscate
