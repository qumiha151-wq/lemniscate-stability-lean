import Lemniscate.PeriodicParabolicGlobalSolution
import Mathlib.Algebra.Order.Floor.Semiring

/-! Uniqueness of global solutions represented by overlapping actual
parabolic segments with the same duration. Only the already proved
finite-interval uniqueness is used.  -/

noncomputable section
namespace Lemniscate
open MeasureTheory
open scoped ENNReal NNReal Topology

private theorem segment_times_cover (τ : ℝ) (hτ : 0 < τ) (t : ℝ≥0) :
    ∃ (n : ℕ) (r : unitInterval), circleParabolicSegmentTime τ hτ n r = t := by
  let q : ℝ := (t:ℝ)/τ
  have hq : 0 ≤ q := div_nonneg (NNReal.coe_nonneg t) hτ.le
  let n := Nat.floor (2*q)
  have hn : (n:ℝ) ≤ 2*q := Nat.floor_le (by positivity)
  have hn' : 2*q < (n:ℝ)+1 := Nat.lt_floor_add_one (2*q)
  let r : unitInterval := ⟨q-(n:ℝ)/2,by constructor <;> linarith only [hn,hn']⟩
  refine ⟨n,r,?_⟩
  apply Subtype.ext
  change τ*((n:ℝ)/2+(q-(n:ℝ)/2)) = (t:ℝ)
  calc
    τ*((n:ℝ)/2+(q-(n:ℝ)/2)) = τ*q := by ring
    _ = (t:ℝ) := by dsimp only [q]; field_simp [ne_of_gt hτ]

private theorem segment_sequence_unique
    {H Y : Type*} (initial : Y → H) (curve : Y → unitInterval → H) (Good : Y → Prop)
    (hc0 : ∀ y, curve y 0 = initial y)
    (hunique : ∀ y z, initial y = initial z → Good y → Good z → y = z)
    (τ : ℝ) (hτ : 0 < τ)
    (u v : ℝ≥0 → H) (U V : ℕ → Y)
    (hU : ∀ n, Good (U n)) (hV : ∀ n, Good (V n))
    (hrepU : ∀ n r, u (circleParabolicSegmentTime τ hτ n r) = curve (U n) r)
    (hrepV : ∀ n r, v (circleParabolicSegmentTime τ hτ n r) = curve (V n) r)
    (hinit : u 0 = v 0) :
    (∀ t, u t = v t) ∧ ∀ n, U n = V n := by
  have hz : circleParabolicSegmentTime τ hτ 0 0 = 0 := by
    apply Subtype.ext
    norm_num [circleParabolicSegmentTime]
  let m : unitInterval := ⟨1/2,by constructor <;> norm_num⟩
  have ht (n : ℕ) : circleParabolicSegmentTime τ hτ (n+1) 0 =
      circleParabolicSegmentTime τ hτ n m := by
    apply Subtype.ext
    change τ*(((n+1:ℕ):ℝ)/2+0) = τ*((n:ℝ)/2+1/2)
    push_cast
    ring
  have hstart (w : ℝ≥0 → H) (W : ℕ → Y)
      (hr : ∀ n r, w (circleParabolicSegmentTime τ hτ n r) = curve (W n) r) :
      initial (W 0) = w 0 :=
    (hc0 (W 0)).symm.trans ((hr 0 0).symm.trans (congrArg w hz))
  have hnext (w : ℝ≥0 → H) (W : ℕ → Y)
      (hr : ∀ n r, w (circleParabolicSegmentTime τ hτ n r) = curve (W n) r)
      (n : ℕ) : initial (W (n+1)) = curve (W n) m :=
    (hc0 (W (n+1))).symm.trans
      ((hr (n+1) 0).symm.trans ((congrArg w (ht n)).trans (hr n m)))
  have hsegments (n : ℕ) : U n = V n := by
    induction n with
    | zero =>
      exact hunique (U 0) (V 0)
        ((hstart u U hrepU).trans (hinit.trans (hstart v V hrepV).symm)) (hU 0) (hV 0)
    | succ n ih =>
      exact hunique (U (n+1)) (V (n+1))
        ((hnext u U hrepU n).trans
          ((congrArg (fun y => curve y m) ih).trans (hnext v V hrepV n).symm))
        (hU (n+1)) (hV (n+1))
  refine ⟨?_,hsegments⟩
  intro t
  obtain ⟨n,r,hr⟩ := segment_times_cover τ hτ t
  exact (congrArg u hr.symm).trans ((hrepU n r).trans
    ((congrArg (fun y => curve y r) (hsegments n)).trans
      ((hrepV n r).symm.trans (congrArg v hr))))

variable (T : ℝ) [Fact (0 < T)]

set_option maxHeartbeats 800000 in
/-- Two global curves represented by small actual parabolic segments of
one common duration agree, together with every segment, if their initial
values agree. No phase condition or energy estimate is required. -/
theorem circle_parabolic_global_uniqueness
    (τ δ : ℝ) (hτ : 0 < τ) (F : CircleSobolevSpace T 4 → CircleL2 T)
    (hunique : ∀ U V : CircleParabolicSpace T τ,
      circleParabolicInitialValue T τ U = circleParabolicInitialValue T τ V →
      ‖circleParabolicCurve T τ U‖ < δ → ‖circleParabolicCurve T τ V‖ < δ →
      (∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ U r = F (circleParabolicH4 T τ U r)) →
      (∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ V r = F (circleParabolicH4 T τ V r)) → U = V)
    (u v : C(ℝ≥0,CircleSobolevSpace T 2)) (U V : ℕ → CircleParabolicSpace T τ)
    (hU : ∀ n, ‖circleParabolicCurve T τ (U n)‖ < δ ∧
      ∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ (U n) r = F (circleParabolicH4 T τ (U n) r))
    (hV : ∀ n, ‖circleParabolicCurve T τ (V n)‖ < δ ∧
      ∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ (V n) r = F (circleParabolicH4 T τ (V n) r))
    (hrepU : ∀ n r, u (circleParabolicSegmentTime τ hτ n r) = circleParabolicCurve T τ (U n) r)
    (hrepV : ∀ n r, v (circleParabolicSegmentTime τ hτ n r) = circleParabolicCurve T τ (V n) r)
    (hinit : u 0 = v 0) : u = v ∧ ∀ n, U n = V n := by
  let Good : CircleParabolicSpace T τ → Prop := fun W =>
    ‖circleParabolicCurve T τ W‖ < δ ∧
      ∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ W r = F (circleParabolicH4 T τ W r)
  have hu : ∀ A B : CircleParabolicSpace T τ,
      circleParabolicInitialValue T τ A = circleParabolicInitialValue T τ B →
      Good A → Good B → A = B := by
    intro A B hi hA hB
    exact hunique A B hi hA.1 hB.1 hA.2 hB.2
  have hs := segment_sequence_unique (circleParabolicInitialValue T τ)
    (fun W r => circleParabolicCurve T τ W r) Good (fun _ => rfl) hu
    τ hτ u v U V hU hV hrepU hrepV hinit
  exact ⟨ContinuousMap.ext hs.1,hs.2⟩

end Lemniscate
