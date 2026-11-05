import Lemniscate.PeriodicParabolicLocalRestriction

/-! A local normal-graph solution agrees with an overlapping global
solution after restarting at any nonnegative time. Both are compared on
one actual parabolic interval, with only their continuous H2 norms small. -/
noncomputable section
namespace Lemniscate
open MeasureTheory Set
open scoped NNReal Topology

variable (T : ℝ) [Fact (0<T)]

/-- Local uniqueness applies to a given short chart and a direct restriction
of the global solution. No bound on a restricted maximal-regularity norm is
required. The local construction may be used at any sufficiently short
duration, so the two intervals have exactly the same duration. -/
theorem circle_parabolic_global_local_uniqueness
    (τ : ℝ) (hτ : 0<τ) (u : ℝ≥0 → CircleSobolevSpace T 2)
    (U : ℕ → CircleParabolicSpace T τ)
    (hrep : ∀ m r, u (circleParabolicSegmentTime τ hτ m r)=
      circleParabolicCurve T τ (U m) r)
    (hcover : ∀ σ : ℝ≥0, 0<σ → ∃ (m : ℕ) (r : unitInterval),
      0<(r:ℝ) ∧ (r:ℝ)<1 ∧ circleParabolicSegmentTime τ hτ m r=σ)
    (F : CircleSobolevSpace T 4 → CircleL2 T) (δ : ℝ)
    (hsmall : ∀ m, ‖circleParabolicCurve T τ (U m)‖<δ)
    (hPDE : ∀ m, ∀ᵐ r : unitInterval ∂volume,
      circleParabolicTimeDerivative T τ (U m) r=F (circleParabolicH4 T τ (U m) r))
    (hunique : ∀ d : ℝ, 0<d → ∀ R V : CircleParabolicSpace T d,
      circleParabolicInitialValue T d R=circleParabolicInitialValue T d V →
      ‖circleParabolicCurve T d R‖<δ → ‖circleParabolicCurve T d V‖<δ →
      (∀ᵐ r : unitInterval ∂volume, circleParabolicTimeDerivative T d R r=
        F (circleParabolicH4 T d R r)) →
      (∀ᵐ r : unitInterval ∂volume, circleParabolicTimeDerivative T d V r=
        F (circleParabolicH4 T d V r)) → R=V)
    (σ₀ : ℝ≥0) (ε : ℝ) (hε : 0<ε)
    (v : ℝ → CircleSobolevSpace T 2) (hv₀ : v 0=u σ₀)
    (hchart : ∀ d : ℝ, 0<d → d<ε → ∃ R : CircleParabolicSpace T d,
      (∀ r : unitInterval, circleParabolicCurve T d R r=v (d*(r:ℝ))) ∧
      ‖circleParabolicCurve T d R‖<δ ∧
      ∀ᵐ r : unitInterval ∂volume, circleParabolicTimeDerivative T d R r=
        F (circleParabolicH4 T d R r)) :
    ∃ d>0, d<ε ∧ ∀ s ∈ Icc (0:ℝ) d,
      v s=u (Real.toNNReal ((σ₀:ℝ)+s)) := by
  obtain ⟨d,hd,hdε,m,R,hR,hR₀,hRsmall,hRPDE⟩ :=
    circle_parabolic_global_local_restriction T τ hτ u U hrep hcover F hPDE σ₀ ε hε
  obtain ⟨V,hV,hVsmall,hVPDE⟩ := hchart d hd hdε
  have hV₀ : circleParabolicInitialValue T d V=u σ₀ := by
    change circleParabolicCurve T d V 0=u σ₀
    simpa only [show ((0:unitInterval):ℝ)=0 from rfl,mul_zero,hv₀] using hV 0
  have hEq : R=V := hunique d hd R V (hR₀.trans hV₀.symm)
    (hRsmall.trans_lt (hsmall m)) hVsmall hRPDE hVPDE
  refine ⟨d,hd,hdε,?_⟩
  intro s hs
  let r : unitInterval := ⟨s/d,⟨div_nonneg hs.1 hd.le,(div_le_one hd).mpr hs.2⟩⟩
  have hscale : d*(r:ℝ)=s := by
    change d*(s/d)=s
    field_simp [hd.ne']
  calc
    v s=circleParabolicCurve T d V r := by rw [hV r,hscale]
    _=circleParabolicCurve T d R r := congrArg (fun W => circleParabolicCurve T d W r) hEq.symm
    _=u (Real.toNNReal ((σ₀:ℝ)+s)) := by rw [hR r,hscale]

end Lemniscate
