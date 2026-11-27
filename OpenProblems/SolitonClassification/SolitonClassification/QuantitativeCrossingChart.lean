import SolitonClassification.FourthOrderZeroCount
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

noncomputable section
open Set
namespace SolitonClassification.CrossingMultiplicity

/-- The explicit chart size gives strict contraction for the four
    anisotropic coefficient bounds of the normalized graph equation. -/
theorem explicit_chart_short {U d : ℝ} (hu : 1 ≤ U) (dp : 0 ≤ d)
    (small : d ≤ 1/(2^24*U^2)) :
    2^15*U^2*d^4 + 2^57*U^5*d^3 + 2^44*U^4*d^2 + 2^19*U*d < 1 := by
  have up : 0<U := lt_of_lt_of_le zero_lt_one hu
  let D : ℝ := 1/(2^24*U^2)
  have hd : d ≤ D := small
  calc
    _ ≤ 2^15*U^2*D^4 + 2^57*U^5*D^3 + 2^44*U^4*D^2 + 2^19*U*D := by gcongr
    _ = 1/((2:ℝ)^81*U^6) + 1/(2^15*U) + 1/16 + 1/(32*U) := by
      dsimp [D]
      field_simp
      ring
    _ ≤ 1/((2:ℝ)^81*1^6) + 1/(2^15*1) + 1/16 + 1/(32*1) := by gcongr
    _ < 1 := by norm_num

/-- A nonidentical chart difference obeying the four explicit bounds
    has at most three zeros throughout the whole closed overlap. -/
theorem finite_three_on_explicit_chart {f g h j k : ℝ → ℝ} {a b U : ℝ}
    (hu : 1 ≤ U) (ab : a ≤ b) (small : b-a ≤ 1/(2^24*U^2))
    (cf : ContinuousOn f (Icc a b)) (cg : ContinuousOn g (Icc a b))
    (ch : ContinuousOn h (Icc a b)) (cj : ContinuousOn j (Icc a b))
    (df : ∀x∈Ioo a b, HasDerivAt f (g x) x) (dg : ∀x∈Ioo a b, HasDerivAt g (h x) x)
    (dh : ∀x∈Ioo a b, HasDerivAt h (j x) x) (dj : ∀x∈Ioo a b, HasDerivAt j (k x) x)
    (bound : ∀x∈Icc a b, |k x| ≤ 2^15*U^2*|f x| + 2^57*U^5*|g x| +
        2^44*U^4*|h x| + 2^19*U*|j x|)
    (distinct : ∃x∈Icc a b, f x ≠ 0) :
    {x ∈ Icc a b | f x = 0}.Finite ∧ {x ∈ Icc a b | f x = 0}.ncard ≤ 3 := by
  have up : 0 < U := lt_of_lt_of_le zero_lt_one hu
  apply finite_zero_set_of_not_four_zeros
  intro four
  obtain ⟨x,hx,nz⟩ := distinct
  exact nz (eq_zero_of_four_zeros cf cg ch cj df dg dh dj (by positivity) (by positivity)
    (by positivity) (by positivity) bound (explicit_chart_short hu (sub_nonneg.mpr ab) small) four x hx)

end SolitonClassification.CrossingMultiplicity
#print axioms SolitonClassification.CrossingMultiplicity.explicit_chart_short
#print axioms SolitonClassification.CrossingMultiplicity.finite_three_on_explicit_chart
