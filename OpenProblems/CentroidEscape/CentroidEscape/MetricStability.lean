import CentroidEscape.MetricCertificates
import Mathlib.Analysis.Real.Sqrt

/-!
# The actual weighted field has logarithmic norm at most 39/20

The diagonal metric in raw coordinates is (1,1,1,1,5/4,2/5,1).
In the existing WeightedState coordinates it is (1,1,4,4,20,128/5,1).
This module proves the quadratic Jacobian inequality throughout the actual
six-coordinate tube. The seventh moment coordinate remains unrestricted.
The statement concerns the original field, not its coordinatewise clamp.
-/
namespace CentroidEscape.MetricStability
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

lemma affine_interval_nonneg {f : ℝ → ℝ} (A B l r t : ℝ)
    (hf : ∀ s, f s = A+B*s) (hlt : l≤t) (htr : t≤r)
    (hl : 0≤f l) (hr : 0≤f r) : 0≤f t := by
  rw [hf] at hl hr ⊢
  by_cases hb : 0≤B
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hlt)]
  · have hbn : B≤0 := le_of_not_ge hb
    nlinarith [mul_nonneg (neg_nonneg.mpr hbn) (sub_nonneg.mpr htr)]

lemma extend_x (x y u w r : ℝ) (h : Fin 7 → ℝ)
    (hx0 : -(8/5)≤x) (hx1 : x≤8/5)
    (hl : 0≤boxForm (-(8/5)) y u w r h)
    (hr : 0≤boxForm (8/5) y u w r h) : 0≤boxForm x y u w r h := by
  apply affine_interval_nonneg (boxForm 0 y u w r h) (-(2/5)*h 3*h 5)
    (-(8/5)) (8/5) x ?_ hx0 hx1 hl hr
  intro s
  dsimp [boxForm]
  ring

lemma extend_y (x y u w r : ℝ) (h : Fin 7 → ℝ)
    (hy0 : -(12/5)≤y) (hy1 : y≤12/5)
    (hl : 0≤boxForm x (-(12/5)) u w r h)
    (hr : 0≤boxForm x (12/5) u w r h) : 0≤boxForm x y u w r h := by
  apply affine_interval_nonneg (boxForm x 0 u w r h) ((2/5)*h 2*h 5)
    (-(12/5)) (12/5) y ?_ hy0 hy1 hl hr
  intro s
  dsimp [boxForm]
  ring

lemma extend_u (x y u w r : ℝ) (h : Fin 7 → ℝ)
    (hu0 : -(11/10)≤u) (hu1 : u≤11/10)
    (hl : 0≤boxForm x y (-(11/10)) w r h)
    (hr : 0≤boxForm x y (11/10) w r h) : 0≤boxForm x y u w r h := by
  apply affine_interval_nonneg (boxForm x y 0 w r h)
    (-(4/5)*h 3*h 4+(2/5)*h 1*h 5) (-(11/10)) (11/10) u ?_ hu0 hu1 hl hr
  intro s
  dsimp [boxForm]
  ring

lemma extend_w (x y u w r : ℝ) (h : Fin 7 → ℝ)
    (hw0 : -(11/10)≤w) (hw1 : w≤11/10)
    (hl : 0≤boxForm x y u (-(11/10)) r h)
    (hr : 0≤boxForm x y u (11/10) r h) : 0≤boxForm x y u w r h := by
  apply affine_interval_nonneg (boxForm x y u 0 r h)
    ((4/5)*h 2*h 4-(2/5)*h 0*h 5) (-(11/10)) (11/10) w ?_ hw0 hw1 hl hr
  intro s
  dsimp [boxForm]
  ring

lemma extend_r (x y u w r : ℝ) (h : Fin 7 → ℝ)
    (hr0 : 0≤r) (hr1 : r≤49/4)
    (hl : 0≤boxForm x y u w 0 h)
    (hr : 0≤boxForm x y u w (49/4) h) : 0≤boxForm x y u w r h := by
  apply affine_interval_nonneg (boxForm x y u w 0 h)
    ((12/25)*h 4*h 5) 0 (49/4) r ?_ hr0 hr1 hl hr
  intro s
  dsimp [boxForm]
  ring

theorem boxForm_nonneg {x y u w r : ℝ}
    (hx : |x|≤8/5) (hy : |y|≤12/5) (hu : |u|≤11/10) (hw : |w|≤11/10)
    (hr0 : 0≤r) (hr1 : r≤49/4) (h : Fin 7 → ℝ) : 0≤boxForm x y u w r h := by
  rcases abs_le.mp hx with ⟨hx0,hx1⟩
  rcases abs_le.mp hy with ⟨hy0,hy1⟩
  rcases abs_le.mp hu with ⟨hu0,hu1⟩
  rcases abs_le.mp hw with ⟨hw0,hw1⟩
  apply extend_x x y u w r h hx0 hx1
  all_goals apply extend_y _ y u w r h hy0 hy1
  all_goals apply extend_u _ _ u w r h hu0 hu1
  all_goals apply extend_w _ _ _ w r h hw0 hw1
  all_goals apply extend_r _ _ _ _ r h hr0 hr1
  all_goals first
    | exact vertex0 h | exact vertex1 h | exact vertex2 h | exact vertex3 h
    | exact vertex4 h | exact vertex5 h | exact vertex6 h | exact vertex7 h
    | exact vertex8 h | exact vertex9 h | exact vertex10 h | exact vertex11 h
    | exact vertex12 h | exact vertex13 h | exact vertex14 h | exact vertex15 h
    | exact vertex16 h | exact vertex17 h | exact vertex18 h | exact vertex19 h
    | exact vertex20 h | exact vertex21 h | exact vertex22 h | exact vertex23 h
    | exact vertex24 h | exact vertex25 h | exact vertex26 h | exact vertex27 h
    | exact vertex28 h | exact vertex29 h | exact vertex30 h | exact vertex31 h

def metricCoordinates (h : WeightedState) : WeightedState :=
  ![h 0,h 1,4*h 2,4*h 3,20*h 4,(128/5)*h 5,h 6]

def metricEnergy (h : WeightedState) : ℝ :=
  (h 0)^2+(h 1)^2+16*(h 2)^2+16*(h 3)^2+400*(h 4)^2+
    (16384/25)*(h 5)^2+(h 6)^2

def metricPairing (h j : WeightedState) : ℝ :=
  h 0*j 0+h 1*j 1+16*h 2*j 2+16*h 3*j 3+400*h 4*j 4+
    (16384/25)*h 5*j 5+h 6*j 6

theorem metricSquare_coordinates (h : WeightedState) :
    metricSquare (metricCoordinates h)=metricEnergy h := by
  simp [metricSquare, metricCoordinates, metricEnergy]
  ring

theorem weightedLinear_metric_identity (a h : WeightedState) :
    (39/20)*metricEnergy h-metricPairing h (weightedLinear a h) =
      boxForm (a 0) (a 1) (4*a 2) (4*a 3) ((16*a 4)^2) (metricCoordinates h) := by
  simp [boxForm, metricSquare, metricCoordinates, metricEnergy, metricPairing, weightedLinear]
  ring

/-- The actual Jacobian's symmetric quadratic form on the full six-coordinate tube. -/
theorem weightedLinear_metric_bound {a : WeightedState} (ha : a∈weightedTube)
    (h : WeightedState) : metricPairing h (weightedLinear a h)≤(39/20)*metricEnergy h := by
  rcases tube_coordinates ha with ⟨a0,a1,a2,a3,a4,a5⟩
  have hu : |4*a 2|≤11/10 := by rw [abs_mul]; norm_num; linarith
  have hw : |4*a 3|≤11/10 := by rw [abs_mul]; norm_num; linarith
  have hk : |16*a 4|≤7/2 := by rw [abs_mul]; norm_num; linarith
  have hr : (16*a 4)^2≤49/4 := by
    rcases abs_le.mp hk with ⟨hl,hr⟩
    nlinarith [sq_nonneg (16*a 4)]
  have hb := boxForm_nonneg a0 a1 hu hw (sq_nonneg (16*a 4)) hr (metricCoordinates h)
  rw [← weightedLinear_metric_identity] at hb
  linarith

theorem metricEnergy_nonneg (h : WeightedState) : 0≤metricEnergy h := by
  dsimp [metricEnergy]
  positivity

def metricNorm (h : WeightedState) : ℝ := Real.sqrt (metricEnergy h)

theorem metricNorm_nonneg (h : WeightedState) : 0≤metricNorm h := Real.sqrt_nonneg _

theorem metricNorm_sq (h : WeightedState) : (metricNorm h)^2=metricEnergy h :=
  Real.sq_sqrt (metricEnergy_nonneg h)

theorem coordinate_sq_le_metricEnergy (h : WeightedState) (i : Fin 7) :
    (h i)^2≤metricEnergy h := by
  fin_cases i <;> dsimp [metricEnergy]
  all_goals nlinarith [sq_nonneg (h 0),sq_nonneg (h 1),sq_nonneg (h 2),
    sq_nonneg (h 3),sq_nonneg (h 4),sq_nonneg (h 5),sq_nonneg (h 6)]

theorem weightedNorm_le_metricNorm (h : WeightedState) : ‖h‖≤metricNorm h := by
  rw [pi_norm_le_iff_of_nonneg (metricNorm_nonneg h)]
  intro i
  simpa only [Real.norm_eq_abs, metricNorm] using
    Real.abs_le_sqrt (coordinate_sq_le_metricEnergy h i)

theorem metricEnergy_le_weightedNorm (h : WeightedState) :
    metricEnergy h≤(27259/25)*‖h‖^2 := by
  have hc (i : Fin 7) : (h i)^2≤‖h‖^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (h i)) (norm_nonneg h)).mpr (weighted_coord_bound h i)
  dsimp [metricEnergy]
  nlinarith [hc 0,hc 1,hc 2,hc 3,hc 4,hc 5,hc 6]

/-- The factor 34 is used for error injection, not at each propagation step. -/
theorem metricNorm_le_weightedNorm (h : WeightedState) : metricNorm h≤34*‖h‖ := by
  rw [metricNorm, Real.sqrt_le_left (by positivity : 0≤34*‖h‖)]
  nlinarith [metricEnergy_le_weightedNorm h, sq_nonneg ‖h‖]

theorem weightedField_secant_identity (a b : WeightedState) :
    (39/20)*metricEnergy (b-a)-metricPairing (b-a) (weightedField b-weightedField a) =
      boxForm ((a 0+b 0)/2) ((a 1+b 1)/2) (2*(a 2+b 2)) (2*(a 3+b 3))
        ((256/3)*((a 4)^2+a 4*b 4+(b 4)^2)) (metricCoordinates (b-a)) := by
  simp [boxForm, metricSquare, metricCoordinates, metricEnergy, metricPairing, weightedField]
  ring

/-- A finite difference inequality for the actual field; no mean-value or
smoothness assumption and no coordinate clamp enters this statement. -/
theorem weightedField_oneSided {a b : WeightedState}
    (ha : a∈weightedTube) (hb : b∈weightedTube) :
    metricPairing (b-a) (weightedField b-weightedField a)≤(39/20)*metricEnergy (b-a) := by
  rcases tube_coordinates ha with ⟨a0,a1,a2,a3,a4,a5⟩
  rcases tube_coordinates hb with ⟨b0,b1,b2,b3,b4,b5⟩
  have midpoint_bound (x y r : ℝ) (hx : |x|≤r) (hy : |y|≤r) : |(x+y)/2|≤r := by
    rw [abs_div]
    norm_num
    linarith [abs_add_le x y]
  have hu : |2*(a 2+b 2)|≤11/10 := by
    rw [abs_mul]
    norm_num
    linarith [abs_add_le (a 2) (b 2)]
  have hw : |2*(a 3+b 3)|≤11/10 := by
    rw [abs_mul]
    norm_num
    linarith [abs_add_le (a 3) (b 3)]
  have ha4 : (a 4)^2≤(7/32:ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a 4)) (by norm_num : (0:ℝ)≤7/32)).mpr a4
  have hb4 : (b 4)^2≤(7/32:ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (b 4)) (by norm_num : (0:ℝ)≤7/32)).mpr b4
  have hr0 : 0≤(256/3:ℝ)*((a 4)^2+a 4*b 4+(b 4)^2) := by
    nlinarith [sq_nonneg (a 4+b 4),sq_nonneg (a 4-b 4)]
  have hr1 : (256/3:ℝ)*((a 4)^2+a 4*b 4+(b 4)^2)≤49/4 := by
    nlinarith [sq_nonneg (a 4-b 4)]
  have hform := boxForm_nonneg (midpoint_bound _ _ _ a0 b0)
    (midpoint_bound _ _ _ a1 b1) hu hw hr0 hr1 (metricCoordinates (b-a))
  rw [← weightedField_secant_identity] at hform
  linarith

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.weightedLinear_metric_bound

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape.MetricStability).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Metric stability audit passed for {checked} declarations."
