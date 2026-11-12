import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Util.CollectAxioms

/-!
# Concrete weighted shooting field and its tube bounds

The state coordinates are (x,y,u/4,w/4,k/16,v/64,m). The seventh coordinate
does not enter the field and is unbounded in the tube.
-/
namespace CentroidEscape
noncomputable section

abbrev WeightedState := Fin 7 → ℝ

def shootingWeights : WeightedState := ![1,1,4,4,16,64,1]

def unweight (a : WeightedState) : WeightedState := fun i => shootingWeights i * a i

def shootingField (z : WeightedState) : WeightedState :=
  ![z 2, z 3, -z 4*z 3, z 4*z 2, z 5,
    -(z 4)^3/2+z 0*z 3-z 1*z 2, z 0]

def weightedField (a : WeightedState) : WeightedState :=
  ![4*a 2, 4*a 3, -16*a 4*a 3, 16*a 4*a 2, 4*a 5,
    -32*(a 4)^3+(a 0*a 3-a 1*a 2)/16, a 0]

theorem weightedField_conjugacy (a : WeightedState) :
    unweight (weightedField a) = shootingField (unweight a) := by
  ext i
  fin_cases i <;> simp [unweight, shootingWeights, weightedField, shootingField] <;> ring

def tubeRadius : WeightedState := ![8/5,12/5,11/40,11/40,7/32,3/32,0]

def weightedTube : Set WeightedState := {a | ∀ i : Fin 7, i ≠ 6 → |a i| ≤ tubeRadius i}

lemma tube_coordinates {a : WeightedState} (ha : a ∈ weightedTube) :
    |a 0| ≤ 8/5 ∧ |a 1| ≤ 12/5 ∧ |a 2| ≤ 11/40 ∧
    |a 3| ≤ 11/40 ∧ |a 4| ≤ 7/32 ∧ |a 5| ≤ 3/32 := by
  exact ⟨ha 0 (by decide), ha 1 (by decide), ha 2 (by decide),
    ha 3 (by decide), ha 4 (by decide), ha 5 (by decide)⟩

lemma product_difference_bound (a b c d : ℝ) :
    |a*b-c*d| ≤ |a| * |b-d| + |a-c| * |d| := by
  calc
    |a*b-c*d| = |a*(b-d)+(a-c)*d| := by congr 1; ring
    _ ≤ |a*(b-d)| + |(a-c)*d| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]

lemma cube_difference_bound {a b r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (ha : |a| ≤ r) (hb : |b| ≤ r) (hab : |a-b| ≤ δ) :
    |a^3-b^3| ≤ 3*r^2*δ := by
  have hsq : |a*a-b*b| ≤ 2*r*δ := by
    calc
      |a*a-b*b| ≤ |a| * |a-b| + |a-b| * |b| := product_difference_bound _ _ _ _
      _ ≤ r*δ+δ*r := by gcongr
      _ = _ := by ring
  have hb2 : |b*b| ≤ r*r := by rw [abs_mul]; gcongr
  calc
    |a^3-b^3| = |a*(a*a)-b*(b*b)| := by congr 1; ring
    _ ≤ |a| * |a*a-b*b| + |a-b| * |b*b| := product_difference_bound _ _ _ _
    _ ≤ r*(2*r*δ)+δ*(r*r) := by gcongr
    _ = _ := by ring

theorem weightedField_bound {a : WeightedState} (ha : a ∈ weightedTube) :
    ‖weightedField a‖ ≤ 2 := by
  rcases tube_coordinates ha with ⟨h0,h1,h2,h3,h4,h5⟩
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  fin_cases i
  · change |4*a 2| ≤ 2
    rw [abs_mul]; norm_num; linarith
  · change |4*a 3| ≤ 2
    rw [abs_mul]; norm_num; linarith
  · change |-16*a 4*a 3| ≤ 2
    rw [abs_mul, abs_mul]; norm_num
    calc
      16* |a 4| * |a 3| ≤ 16*(7/32)*(11/40) := by gcongr
      _ ≤ 2 := by norm_num
  · change |16*a 4*a 2| ≤ 2
    rw [abs_mul, abs_mul]; norm_num
    calc
      16* |a 4| * |a 2| ≤ 16*(7/32)*(11/40) := by gcongr
      _ ≤ 2 := by norm_num
  · change |4*a 5| ≤ 2
    rw [abs_mul]; norm_num; linarith
  · change |-32*(a 4)^3+(a 0*a 3-a 1*a 2)/16| ≤ 2
    calc
      |-32*(a 4)^3+(a 0*a 3-a 1*a 2)/16| ≤
          32* |a 4|^3+(|a 0| * |a 3| + |a 1| * |a 2|)/16 := by
        calc
          _ ≤ |-32*(a 4)^3| + |(a 0*a 3-a 1*a 2)/16| := abs_add_le _ _
          _ ≤ |-32*(a 4)^3| + (|a 0*a 3| + |a 1*a 2|)/16 := by
            rw [abs_div]; norm_num
            simpa only [abs_mul] using div_le_div_of_nonneg_right
              (abs_sub (a 0*a 3) (a 1*a 2)) (by norm_num : (0:ℝ) ≤ 16)
          _ = _ := by rw [abs_mul, abs_pow, abs_mul, abs_mul]; norm_num
      _ ≤ 32*(7/32)^3+((8/5)*(11/40)+(12/5)*(11/40))/16 := by gcongr
      _ ≤ 2 := by norm_num
  · change |a 0| ≤ 2
    linarith

theorem weightedField_lipschitz : LipschitzOnWith 8 weightedField weightedTube := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro a ha b hb
  rcases tube_coordinates ha with ⟨a0,a1,a2,a3,a4,a5⟩
  rcases tube_coordinates hb with ⟨b0,b1,b2,b3,b4,b5⟩
  have hd (i : Fin 7) : |a i-b i| ≤ ‖a-b‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (a-b) i
  have hδ := norm_nonneg (a-b)
  have hp43 : |a 4*a 3-b 4*b 3| ≤ (7/32+11/40)*‖a-b‖ := by
    calc
      _ ≤ |a 4| * |a 3-b 3| + |a 4-b 4| * |b 3| := product_difference_bound _ _ _ _
      _ ≤ (7/32)*‖a-b‖+‖a-b‖*(11/40) := by gcongr <;> apply hd
      _ = _ := by ring
  have hp42 : |a 4*a 2-b 4*b 2| ≤ (7/32+11/40)*‖a-b‖ := by
    calc
      _ ≤ |a 4| * |a 2-b 2| + |a 4-b 4| * |b 2| := product_difference_bound _ _ _ _
      _ ≤ (7/32)*‖a-b‖+‖a-b‖*(11/40) := by gcongr <;> apply hd
      _ = _ := by ring
  have hp03 : |a 0*a 3-b 0*b 3| ≤ (8/5+11/40)*‖a-b‖ := by
    calc
      _ ≤ |a 0| * |a 3-b 3| + |a 0-b 0| * |b 3| := product_difference_bound _ _ _ _
      _ ≤ (8/5)*‖a-b‖+‖a-b‖*(11/40) := by gcongr <;> apply hd
      _ = _ := by ring
  have hp12 : |a 1*a 2-b 1*b 2| ≤ (12/5+11/40)*‖a-b‖ := by
    calc
      _ ≤ |a 1| * |a 2-b 2| + |a 1-b 1| * |b 2| := product_difference_bound _ _ _ _
      _ ≤ (12/5)*‖a-b‖+‖a-b‖*(11/40) := by gcongr <;> apply hd
      _ = _ := by ring
  have hc := cube_difference_bound (by norm_num : (0:ℝ) ≤ 7/32) hδ a4 b4 (hd 4)
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · change |4*a 2-4*b 2| ≤ 8*‖a-b‖
    rw [← mul_sub, abs_mul]; norm_num; linarith [hd 2]
  · change |4*a 3-4*b 3| ≤ 8*‖a-b‖
    rw [← mul_sub, abs_mul]; norm_num; linarith [hd 3]
  · change |-16*a 4*a 3-(-16*b 4*b 3)| ≤ 8*‖a-b‖
    rw [show -16*a 4*a 3-(-16*b 4*b 3) = -16*(a 4*a 3-b 4*b 3) by ring, abs_mul]
    norm_num; nlinarith
  · change |16*a 4*a 2-16*b 4*b 2| ≤ 8*‖a-b‖
    rw [show 16*a 4*a 2-16*b 4*b 2 = 16*(a 4*a 2-b 4*b 2) by ring, abs_mul]
    norm_num; nlinarith
  · change |4*a 5-4*b 5| ≤ 8*‖a-b‖
    rw [← mul_sub, abs_mul]; norm_num; linarith [hd 5]
  · change |(-32*(a 4)^3+(a 0*a 3-a 1*a 2)/16)-(-32*(b 4)^3+(b 0*b 3-b 1*b 2)/16)| ≤ 8*‖a-b‖
    calc
      _ = |-32*((a 4)^3-(b 4)^3)+((a 0*a 3-b 0*b 3)-(a 1*a 2-b 1*b 2))/16| := by congr 1; ring
      _ ≤ 32* |(a 4)^3-(b 4)^3| + (|a 0*a 3-b 0*b 3| + |a 1*a 2-b 1*b 2|)/16 := by
        calc
          _ ≤ |-32*((a 4)^3-(b 4)^3)| + |((a 0*a 3-b 0*b 3)-(a 1*a 2-b 1*b 2))/16| := abs_add_le _ _
          _ ≤ |-32*((a 4)^3-(b 4)^3)| + (|a 0*a 3-b 0*b 3| + |a 1*a 2-b 1*b 2|)/16 := by
            rw [abs_div]; norm_num
            exact div_le_div_of_nonneg_right (abs_sub _ _) (by norm_num : (0:ℝ) ≤ 16)
          _ = _ := by rw [abs_mul]; norm_num
      _ ≤ 32*(3*(7/32)^2*‖a-b‖)+((8/5+11/40)*‖a-b‖+(12/5+11/40)*‖a-b‖)/16 := by gcongr
      _ ≤ 8*‖a-b‖ := by nlinarith
  · change |a 0-b 0| ≤ 8*‖a-b‖
    linarith [hd 0]

def clipScalar (r x : ℝ) : ℝ := min (max x (-r)) r

lemma clipScalar_lipschitz (r : ℝ) : LipschitzWith 1 (clipScalar r) :=
  (LipschitzWith.id.max_const (-r)).min_const r

lemma clipScalar_bound {r : ℝ} (hr : 0 ≤ r) (x : ℝ) : |clipScalar r x| ≤ r := by
  rw [abs_le]
  exact ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩

lemma clipScalar_eq_self {r x : ℝ} (h : |x| ≤ r) : clipScalar r x = x := by
  rcases abs_le.mp h with ⟨hl,hu⟩
  simp [clipScalar, max_eq_left hl, min_eq_left hu]

def clipState (a : WeightedState) : WeightedState :=
  fun i => if i = 6 then a i else clipScalar (tubeRadius i) (a i)

lemma tubeRadius_nonneg (i : Fin 7) : 0 ≤ tubeRadius i := by
  fin_cases i <;> norm_num [tubeRadius]

theorem clipState_mem (a : WeightedState) : clipState a ∈ weightedTube := by
  intro i hi
  simp only [clipState, if_neg hi]
  exact clipScalar_bound (tubeRadius_nonneg i) (a i)

theorem clipState_eq_self {a : WeightedState} (ha : a ∈ weightedTube) : clipState a = a := by
  ext i
  by_cases hi : i = 6
  · simp [clipState, hi]
  · simp only [clipState, if_neg hi]
    exact clipScalar_eq_self (ha i hi)

theorem clipState_lipschitz : LipschitzWith 1 clipState := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro a b
  simp only [NNReal.coe_one, one_mul]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  have hd : |a i-b i| ≤ ‖a-b‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (a-b) i
  simp only [Pi.sub_apply, Real.norm_eq_abs, clipState]
  by_cases hi : i = 6
  · simpa only [if_pos hi] using hd
  · simp only [if_neg hi]
    have hl := (clipScalar_lipschitz (tubeRadius i)).dist_le_mul (a i) (b i)
    have he : |clipScalar (tubeRadius i) (a i)-clipScalar (tubeRadius i) (b i)| ≤ |a i-b i| := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hl
    exact he.trans hd

def clippedField (a : WeightedState) : WeightedState := weightedField (clipState a)

theorem clippedField_bound (a : WeightedState) : ‖clippedField a‖ ≤ 2 :=
  weightedField_bound (clipState_mem a)

theorem clippedField_eq {a : WeightedState} (ha : a ∈ weightedTube) :
    clippedField a = weightedField a := by rw [clippedField, clipState_eq_self ha]

theorem clippedField_lipschitz : LipschitzWith 8 clippedField := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro a b
  have hf := lipschitzOnWith_iff_norm_sub_le.mp weightedField_lipschitz
    (clipState_mem a) (clipState_mem b)
  have hc := lipschitzWith_iff_norm_sub_le.mp clipState_lipschitz a b
  simp only [NNReal.coe_one, one_mul] at hc
  exact hf.trans (mul_le_mul_of_nonneg_left hc (by positivity))

end
end CentroidEscape

#print axioms CentroidEscape.weightedField_bound
#print axioms CentroidEscape.clippedField_lipschitz

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Weighted-field audit passed for {checked} declarations."


