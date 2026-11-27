import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ClosedSimilarity.CrossingParity

/-- The horizontal component of `-(Z · N) N` on the limiting central arc,
    where the position is `(U,G)` and the tangent is `(w,U²/2)`. -/
def horizontalRate (U w G : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(U t * (-(U t ^ 2 / 2)) + G t * w t) * (-(U t ^ 2 / 2))

/-- Differentiating the scaled stress identity at zero requires only
    joint continuity of its force along the perturbed trajectories. -/
theorem stress_first_variation (W R : ℝ → ℝ → ℝ) (cr : Continuous R.uncurry)
    (zero : ∀ ε, W ε 0 = 0)
    (rate : ∀ ε t, HasDerivAt (W ε) (ε * R ε t) t) (b : ℝ) :
    HasDerivAt (fun ε => W ε b) (∫ t in (0:ℝ)..b, R 0 t) 0 := by
  let A := fun ε => ∫ t in (0:ℝ)..b, R ε t
  have ca : Continuous A := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    cr 0 b
  have factor (ε : ℝ) : W ε b = ε * A ε := by
    have ct : Continuous (fun t => ε * R ε t) := continuous_const.mul (cr.uncurry_left ε)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := 0) (b := b) (fun t _ => rate ε t) (ct.intervalIntegrable 0 b)
    rw [zero, sub_zero, intervalIntegral.integral_const_mul] at h
    exact h.symm
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (ca.continuousAt.continuousWithinAt (s := {0}ᶜ)).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have ne : ε ≠ 0 := hε
  rw [slope_def_field, factor, factor]
  simp [ne]

/-- The integrated horizontal stress variation between oscillator zeros. -/
theorem integral_horizontalRate_of_zeros (U w G : ℝ → ℝ)
    (cw : Continuous w) (dU : ∀ t, HasDerivAt U (w t) t)
    (dG : ∀ t, HasDerivAt G (U t ^ 2 / 2) t)
    {a b : ℝ} (ha : U a = 0) (hb : U b = 0) :
    (∫ t in a..b, horizontalRate U w G t) = -(∫ t in a..b, U t ^ 5) / 3 := by
  have cU := continuous_iff_continuousAt.mpr (fun t => (dU t).continuousAt)
  have cG := continuous_iff_continuousAt.mpr (fun t => (dG t).continuousAt)
  let D := fun t => horizontalRate U w G t + U t ^ 5 / 3
  have cd : Continuous D := by dsimp [D, horizontalRate]; fun_prop
  have hd (t) : HasDerivAt (fun s => G s * U s ^ 3 / 6) (D t) t := by
    convert! ((dG t).mul ((dU t).pow 3)).div_const 6 using 1
    simp only [D, horizontalRate, Pi.pow_apply]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (fun t _ => hd t) (cd.intervalIntegrable a b)
  have cr : Continuous (horizontalRate U w G) := by unfold horizontalRate; fun_prop
  have c5 : Continuous (fun t => U t ^ 5 / 3) := by fun_prop
  change (∫ t in a..b, horizontalRate U w G t + U t ^ 5 / 3) = _ at h
  rw [intervalIntegral.integral_add (cr.intervalIntegrable a b) (c5.intervalIntegrable a b),
    intervalIntegral.integral_div] at h
  simp only [ha, hb, zero_pow (by decide : 3 ≠ 0), mul_zero, zero_div, sub_zero] at h
  linarith

/-- Even half-period endpoints give zero horizontal stress variation. Odd
    endpoints give the same strictly negative variation for every index. -/
theorem horizontalRate_parity (U w G : ℝ → ℝ) {H : ℝ} (half : 0 < H)
    (cw : Continuous w) (dU : ∀ t, HasDerivAt U (w t) t)
    (dG : ∀ t, HasDerivAt G (U t ^ 2 / 2) t)
    (zero : U 0 = 0) (anti : ∀ t, U (t + H) = -U t)
    (pos : ∀ t ∈ Ioo 0 H, 0 < U t) :
    let C := -(∫ t in (0:ℝ)..H, U t ^ 5) / 3
    C < 0 ∧ ∀ n : ℕ,
      (∫ t in (0:ℝ)..(n:ℝ)*(2*H), horizontalRate U w G t) = 0 ∧
      (∫ t in (0:ℝ)..((n:ℝ)*(2*H)+H), horizontalRate U w G t) = C := by
  let F := fun x => ∫ t in (0:ℝ)..x, U t ^ 5
  have cU := continuous_iff_continuousAt.mpr (fun t => (dU t).continuousAt)
  have c5 := cU.pow 5
  have step (x : ℝ) : F (x+H) = F H - F x := by
    have shift : (∫ t in H..x+H, U t ^ 5) = -F x := by
      have trans := intervalIntegral.integral_comp_add_right (f := fun t => U t ^ 5)
        (a := 0) (b := x) H
      rw [zero_add] at trans
      rw [← trans]
      simp_rw [anti, show ∀ y : ℝ, (-y)^5 = -(y^5) by intro y; ring]
      exact intervalIntegral.integral_neg
    have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (c5.intervalIntegrable 0 H) (c5.intervalIntegrable H (x+H))
    change F H + (∫ t in H..x+H, U t ^ 5) = F (x+H) at h
    linarith
  have pair (n : ℕ) : U ((n:ℝ)*(2*H)) = 0 ∧ F ((n:ℝ)*(2*H)) = 0 := by
    induction n with
    | zero => simp [F, zero]
    | succ n ih =>
      rw [Nat.cast_succ, show ((n:ℝ)+1)*(2*H) = (n:ℝ)*(2*H)+H+H by ring,
        anti, anti, step, step, ih.1, ih.2]
      constructor <;> ring
  have positive : 0 < F H := intervalIntegral.intervalIntegral_pos_of_pos_on
    (c5.intervalIntegrable 0 H) (fun t ht => pow_pos (pos t ht) 5) half
  change -(F H) / 3 < 0 ∧ _
  refine ⟨by linarith, ?_⟩
  intro n
  obtain ⟨uz, iz⟩ := pair n
  have uh : U ((n:ℝ)*(2*H)+H) = 0 := by rw [anti, uz, neg_zero]
  constructor
  · rw [integral_horizontalRate_of_zeros U w G cw dU dG zero uz]
    change -(F _) / 3 = 0
    rw [iz]; norm_num
  · rw [integral_horizontalRate_of_zeros U w G cw dU dG zero uh]
    change -(F _) / 3 = -(F H) / 3
    rw [step, iz, sub_zero]

/-- In a continuous stress family with the scaled Frenet forcing law the
    actual stress derivatives in the perturbation parameter split by parity. -/
theorem stress_derivative_parity (W R : ℝ → ℝ → ℝ) (U w G : ℝ → ℝ)
    {H : ℝ} (half : 0 < H) (cr : Continuous R.uncurry) (initial : ∀ ε, W ε 0 = 0)
    (rate : ∀ ε t, HasDerivAt (W ε) (ε * R ε t) t) (base : R 0 = horizontalRate U w G)
    (cw : Continuous w) (dU : ∀ t, HasDerivAt U (w t) t)
    (dG : ∀ t, HasDerivAt G (U t ^ 2 / 2) t)
    (zero : U 0 = 0) (anti : ∀ t, U (t + H) = -U t)
    (pos : ∀ t ∈ Ioo 0 H, 0 < U t) :
    let C := -(∫ t in (0:ℝ)..H, U t ^ 5) / 3
    C < 0 ∧ ∀ n : ℕ,
      HasDerivAt (fun ε => W ε ((n:ℝ)*(2*H))) 0 0 ∧
      HasDerivAt (fun ε => W ε ((n:ℝ)*(2*H)+H)) C 0 := by
  obtain ⟨neg, bounds⟩ := horizontalRate_parity U w G half cw dU dG zero anti pos
  refine ⟨neg, fun n => ?_⟩
  obtain ⟨even, odd⟩ := bounds n
  exact ⟨by simpa only [base, even] using stress_first_variation W R cr initial rate ((n:ℝ)*(2*H)),
    by simpa only [base, odd] using stress_first_variation W R cr initial rate ((n:ℝ)*(2*H)+H)⟩

end ClosedSimilarity.CrossingParity
#print axioms ClosedSimilarity.CrossingParity.stress_first_variation
#print axioms ClosedSimilarity.CrossingParity.integral_horizontalRate_of_zeros
#print axioms ClosedSimilarity.CrossingParity.horizontalRate_parity
#print axioms ClosedSimilarity.CrossingParity.stress_derivative_parity
