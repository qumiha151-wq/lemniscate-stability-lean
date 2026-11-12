import CentroidEscape.WeightedField

/-!
# Exact finite expansion of the concrete shooting field

The multilinear expressions are explicit coordinate polynomials. Their
majorant constants are derived from the actual rational tube bounds.
-/
namespace CentroidEscape
noncomputable section

def weightedLinear (a u : WeightedState) : WeightedState :=
  ![4*u 2,4*u 3,-16*(a 4*u 3+u 4*a 3),16*(a 4*u 2+u 4*a 2),4*u 5,
    -96*(a 4)^2*u 4+(a 0*u 3+u 0*a 3-a 1*u 2-u 1*a 2)/16,u 0]

def weightedBilinear (a u v : WeightedState) : WeightedState :=
  ![0,0,-16*u 4*v 3,16*u 4*v 2,0,
    -96*a 4*u 4*v 4+(u 0*v 3-u 1*v 2)/16,0]

def weightedTrilinear (u v w : WeightedState) : WeightedState :=
  ![0,0,0,0,0,-32*u 4*v 4*w 4,0]

theorem weightedField_expansion (a u : WeightedState) :
    weightedField (a+u) = weightedField a+weightedLinear a u+
      weightedBilinear a u u+weightedTrilinear u u u := by
  ext i
  fin_cases i <;> simp [weightedField, weightedLinear, weightedBilinear,
    weightedTrilinear] <;> ring

lemma weighted_coord_bound (u : WeightedState) (i : Fin 7) : |u i| ≤ ‖u‖ := by
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i

theorem weightedTrilinear_bound (u v w : WeightedState) :
    ‖weightedTrilinear u v w‖ ≤ 32*‖u‖*‖v‖*‖w‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i <;> try { change ‖(0:ℝ)‖ ≤ _; simp; positivity }
  change |-32*u 4*v 4*w 4| ≤ _
  rw [abs_mul, abs_mul, abs_mul]
  norm_num
  gcongr <;> apply weighted_coord_bound

theorem weightedBilinear_bound {a : WeightedState} (ha : a ∈ weightedTube)
    (u v : WeightedState) : ‖weightedBilinear a u v‖ ≤ 22*‖u‖*‖v‖ := by
  rcases tube_coordinates ha with ⟨a0,a1,a2,a3,a4,a5⟩
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have huv : 0 ≤ ‖u‖*‖v‖ := mul_nonneg hu hv
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i <;> try { change ‖(0:ℝ)‖ ≤ _; simp; positivity }
  · change |-16*u 4*v 3| ≤ _
    rw [abs_mul, abs_mul]; norm_num
    calc
      16* |u 4| * |v 3| ≤ 16*‖u‖*‖v‖ := by gcongr <;> apply weighted_coord_bound
      _ ≤ _ := by nlinarith
  · change |16*u 4*v 2| ≤ _
    rw [abs_mul, abs_mul]; norm_num
    calc
      16* |u 4| * |v 2| ≤ 16*‖u‖*‖v‖ := by gcongr <;> apply weighted_coord_bound
      _ ≤ _ := by nlinarith
  · change |-96*a 4*u 4*v 4+(u 0*v 3-u 1*v 2)/16| ≤ _
    calc
      _ ≤ |-96*a 4*u 4*v 4| + |(u 0*v 3-u 1*v 2)/16| := abs_add_le _ _
      _ ≤ 96* |a 4| * |u 4| * |v 4| + (|u 0| * |v 3| + |u 1| * |v 2|)/16 := by
        rw [abs_mul, abs_mul, abs_mul, abs_div]
        norm_num
        simpa only [abs_mul] using div_le_div_of_nonneg_right
          (abs_sub (u 0*v 3) (u 1*v 2)) (by norm_num : (0:ℝ) ≤ 16)
      _ ≤ 96*(7/32)*‖u‖*‖v‖+(‖u‖*‖v‖+‖u‖*‖v‖)/16 := by
        gcongr <;> apply weighted_coord_bound
      _ ≤ _ := by nlinarith

theorem weightedLinear_bound {a : WeightedState} (ha : a ∈ weightedTube)
    (u : WeightedState) : ‖weightedLinear a u‖ ≤ 8*‖u‖ := by
  rcases tube_coordinates ha with ⟨a0,a1,a2,a3,a4,a5⟩
  have hu := norm_nonneg u
  have h43 : |a 4*u 3+u 4*a 3| ≤ (7/32+11/40)*‖u‖ := by
    calc
      _ ≤ |a 4*u 3| + |u 4*a 3| := abs_add_le _ _
      _ = |a 4| * |u 3| + |u 4| * |a 3| := by rw [abs_mul, abs_mul]
      _ ≤ (7/32)*‖u‖+‖u‖*(11/40) := by gcongr <;> apply weighted_coord_bound
      _ = _ := by ring
  have h42 : |a 4*u 2+u 4*a 2| ≤ (7/32+11/40)*‖u‖ := by
    calc
      _ ≤ |a 4*u 2| + |u 4*a 2| := abs_add_le _ _
      _ = |a 4| * |u 2| + |u 4| * |a 2| := by rw [abs_mul, abs_mul]
      _ ≤ (7/32)*‖u‖+‖u‖*(11/40) := by gcongr <;> apply weighted_coord_bound
      _ = _ := by ring
  have hs : |a 0*u 3+u 0*a 3-a 1*u 2-u 1*a 2| ≤
      |a 0| * |u 3| + |u 0| * |a 3| + |a 1| * |u 2| + |u 1| * |a 2| := by
    calc
      _ ≤ |a 0*u 3+u 0*a 3-a 1*u 2| + |u 1*a 2| := abs_sub _ _
      _ ≤ (|a 0*u 3+u 0*a 3| + |a 1*u 2|)+|u 1*a 2| := by gcongr; apply abs_sub
      _ ≤ ((|a 0*u 3| + |u 0*a 3|)+|a 1*u 2|)+|u 1*a 2| := by gcongr; apply abs_add_le
      _ = _ := by simp only [abs_mul]
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · change |4*u 2| ≤ _
    rw [abs_mul]; norm_num; linarith [weighted_coord_bound u 2]
  · change |4*u 3| ≤ _
    rw [abs_mul]; norm_num; linarith [weighted_coord_bound u 3]
  · change |-16*(a 4*u 3+u 4*a 3)| ≤ _
    rw [abs_mul]; norm_num; nlinarith
  · change |16*(a 4*u 2+u 4*a 2)| ≤ _
    rw [abs_mul]; norm_num; nlinarith
  · change |4*u 5| ≤ _
    rw [abs_mul]; norm_num; linarith [weighted_coord_bound u 5]
  · change |-96*(a 4)^2*u 4+(a 0*u 3+u 0*a 3-a 1*u 2-u 1*a 2)/16| ≤ _
    calc
      _ ≤ |-96*(a 4)^2*u 4| + |(a 0*u 3+u 0*a 3-a 1*u 2-u 1*a 2)/16| := abs_add_le _ _
      _ ≤ 96* |a 4|^2* |u 4| + (|a 0| * |u 3| + |u 0| * |a 3| + |a 1| * |u 2| + |u 1| * |a 2|)/16 := by
        rw [abs_mul, abs_mul, abs_pow, abs_div]
        norm_num
        exact div_le_div_of_nonneg_right hs (by norm_num)
      _ ≤ 96*(7/32)^2*‖u‖+((8/5)*‖u‖+‖u‖*(11/40)+(12/5)*‖u‖+‖u‖*(11/40))/16 := by
        gcongr <;> apply weighted_coord_bound
      _ ≤ _ := by nlinarith
  · change |u 0| ≤ _
    linarith [weighted_coord_bound u 0]

theorem weightedLinear_add (a u v : WeightedState) :
    weightedLinear a (u+v) = weightedLinear a u+weightedLinear a v := by
  ext i
  fin_cases i <;> simp [weightedLinear] <;> ring

theorem weightedLinear_smul (a u : WeightedState) (c : ℝ) :
    weightedLinear a (c • u) = c • weightedLinear a u := by
  ext i
  fin_cases i <;> simp [weightedLinear, smul_eq_mul] <;> ring

theorem weightedBilinear_add_left (a u v w : WeightedState) :
    weightedBilinear a (u+v) w = weightedBilinear a u w+weightedBilinear a v w := by
  ext i
  fin_cases i <;> simp [weightedBilinear] <;> ring

theorem weightedBilinear_add_right (a u v w : WeightedState) :
    weightedBilinear a u (v+w) = weightedBilinear a u v+weightedBilinear a u w := by
  ext i
  fin_cases i <;> simp [weightedBilinear] <;> ring

theorem weightedBilinear_smul_left (a u v : WeightedState) (c : ℝ) :
    weightedBilinear a (c • u) v = c • weightedBilinear a u v := by
  ext i
  fin_cases i <;> simp [weightedBilinear, smul_eq_mul] <;> ring

theorem weightedBilinear_smul_right (a u v : WeightedState) (c : ℝ) :
    weightedBilinear a u (c • v) = c • weightedBilinear a u v := by
  ext i
  fin_cases i <;> simp [weightedBilinear, smul_eq_mul] <;> ring

theorem weightedTrilinear_add_first (u v w z : WeightedState) :
    weightedTrilinear (u+v) w z = weightedTrilinear u w z+weightedTrilinear v w z := by
  ext i
  fin_cases i <;> simp [weightedTrilinear]
  all_goals ring

theorem weightedTrilinear_add_second (u v w z : WeightedState) :
    weightedTrilinear u (v+w) z = weightedTrilinear u v z+weightedTrilinear u w z := by
  ext i
  fin_cases i <;> simp [weightedTrilinear]
  all_goals ring

theorem weightedTrilinear_add_third (u v w z : WeightedState) :
    weightedTrilinear u v (w+z) = weightedTrilinear u v w+weightedTrilinear u v z := by
  ext i
  fin_cases i <;> simp [weightedTrilinear]
  all_goals ring

theorem weightedTrilinear_smul_first (u v w : WeightedState) (c : ℝ) :
    weightedTrilinear (c • u) v w = c • weightedTrilinear u v w := by
  ext i
  fin_cases i <;> simp [weightedTrilinear, smul_eq_mul]
  all_goals ring

theorem weightedTrilinear_smul_second (u v w : WeightedState) (c : ℝ) :
    weightedTrilinear u (c • v) w = c • weightedTrilinear u v w := by
  ext i
  fin_cases i <;> simp [weightedTrilinear, smul_eq_mul]
  all_goals ring

theorem weightedTrilinear_smul_third (u v w : WeightedState) (c : ℝ) :
    weightedTrilinear u v (c • w) = c • weightedTrilinear u v w := by
  ext i
  fin_cases i <;> simp [weightedTrilinear, smul_eq_mul]
  all_goals ring

theorem weightedField_majorant {a : WeightedState} (ha : a ∈ weightedTube)
    (u : WeightedState) :
    ‖weightedField (a+u)‖ ≤ 2+8*‖u‖+22*‖u‖^2+32*‖u‖^3 := by
  rw [weightedField_expansion]
  have h1 := norm_add_le (weightedField a) (weightedLinear a u)
  have h2 := norm_add_le (weightedField a+weightedLinear a u) (weightedBilinear a u u)
  have h3 := norm_add_le (weightedField a+weightedLinear a u+weightedBilinear a u u)
    (weightedTrilinear u u u)
  nlinarith [weightedField_bound ha, weightedLinear_bound ha u,
    weightedBilinear_bound ha u u, weightedTrilinear_bound u u u]

end
end CentroidEscape

#print axioms CentroidEscape.weightedLinear_bound
#print axioms CentroidEscape.weightedBilinear_bound
#print axioms CentroidEscape.weightedTrilinear_bound

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
  logInfo m!"Weighted-expansion audit passed for {checked} declarations."



