import SolitonClassification.PhysicalCrossingResponse
import SolitonClassification.CrossingTangencies
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 220000
open Set Metric MeasureTheory Filter
open scoped Topology
namespace ClosedSimilarity.CrossingResponse
open GlobalSupport

theorem fast_coordinate_cont (i : Fin 4) : Continuous (fun z : ℝ × ℝ => shot z.1 z.2 i) := by
  have c : Continuous (fun z : ℝ × ℝ => (z.2,(z.1,(![0,1,0,0] : Phase)))) :=
    continuous_snd.prodMk (continuous_fst.prodMk continuous_const)
  exact (continuous_apply i).comp (continuous_solution.comp c)

private theorem displacement {B C : ℝ} {f g : ℝ → ℝ} (cf : Continuous f) (cg : Continuous g)
    (cp : 0 ≤ C) (h : ∀ u ∈ Icc 0 B, |f u-g u| ≤ C) {t : ℝ} (ht : t ∈ Icc 0 B) :
    |(∫ u in (0:ℝ)..t, f u) - ∫ u in (0:ℝ)..t, g u| ≤ C*B := by
  rw [← intervalIntegral.integral_sub (cf.intervalIntegrable ..) (cg.intervalIntegrable ..)]
  have d := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := C)
    (f := fun u => f u - g u) (fun u hu => by
      rw [uIoc_of_le ht.1] at hu
      simpa only [Real.norm_eq_abs] using h u ⟨hu.1.le,hu.2.trans ht.2⟩)
  exact (by simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] using d :
    |∫ u in (0:ℝ)..t, f u-g u| ≤ C*t).trans (mul_le_mul_of_nonneg_left ht.2 cp)

private theorem curvature_parameter_bound {B : ℝ} (bp : 0 ≤ B) :
    ∃ c > 0, ∀ e : ℝ, |e| ≤ 1 → ∀ t ∈ Icc 0 B, |K e t-K 0 t| ≤ c*|e| := by
  let z : Phase := ![0,1,0,0]
  let a : Data := (0,z)
  obtain ⟨c,cp,hc⟩ := compact_initial_estimate (isCompact_closedBall a 1) bp
  refine ⟨c,cp,?_⟩
  intro e he
  have dist0 : dist ((e,z):Data) a = |e| := by
    simp only [a,dist_prod_same_right,Real.dist_eq,sub_zero]
  have bound (t : ℝ) (ht : t∈Icc 0 B) : |K e t-K 0 t| ≤ c*|e| := by
    have h := hc (e,z) (show ((e,z):Data) ∈ closedBall a 1 by rwa [mem_closedBall,dist0])
      a (mem_closedBall_self zero_le_one) t (by simpa only [abs_of_nonneg ht.1] using ht.2)
    rw [dist0] at h
    change dist (e, shot e t) (0, shot 0 t) ≤ _ at h
    rw [Prod.dist_eq] at h
    have proj := dist_le_pi_dist (shot e t) (shot 0 t) (0 : Fin 4)
    rw [Real.dist_eq] at proj
    exact proj.trans ((le_max_right ..).trans h)
  exact bound

private theorem angle_primitive (e s : ℝ) : angle e s = ∫ t in (0:ℝ)..s, K e t := rfl
private theorem X_primitive (e s : ℝ) : X e s = ∫ t in (0:ℝ)..s, tx e t := rfl

private theorem slice_cont (f : ℝ → ℝ → ℝ) (cf : Continuous f.uncurry) (e : ℝ) :
    Continuous (f e) := cf.comp (continuous_const.prodMk continuous_id)

set_option backward.isDefEq.respectTransparency true in
private theorem position_parameter_bound {B c e : ℝ} (bp : 0 ≤ B) (cp : 0 ≤ c)
    (kin : ∀ t ∈ Icc 0 B, |K e t-K 0 t| ≤ c * |e|) {t : ℝ} (ht : t ∈ Icc 0 B) :
    |X e t-X 0 t| ≤ c * |e| * B * B := by
  have ck (j : ℝ) : Continuous (K j) := slice_cont K (fast_coordinate_cont 0) j
  have angleBound (s : ℝ) (hs : s∈Icc 0 B) : |angle e s-angle 0 s| ≤ c * |e| * B := by
    rw [angle_primitive e s,angle_primitive 0 s]
    exact displacement (B := B) (C := c * |e|) (ck e) (ck 0) (mul_nonneg cp (abs_nonneg e)) kin hs
  have txBound (s : ℝ) (hs : s∈Icc 0 B) : |tx e s-tx 0 s| ≤ c * |e| * B :=
    (Real.abs_cos_sub_cos_le (angle e s) (angle 0 s)).trans (angleBound s hs)
  have cx (j : ℝ) : Continuous (tx j) := slice_cont tx tx_cont j
  rw [X_primitive e t,X_primitive 0 t]
  exact displacement (B := B) (C := c * |e| * B) (cx e) (cx 0)
    (mul_nonneg (mul_nonneg cp (abs_nonneg e)) bp) txBound ht

/-- A single parameter Lipschitz bound controls the curvature and horizontal
    position on every prescribed compact time interval of the true shot. -/
theorem fast_parameter_bound {B : ℝ} (bp : 0 ≤ B) :
    ∃ C ≥ 1, ∀ e : ℝ, |e| ≤ 1 → ∀ t ∈ Icc 0 B,
      |K e t-K 0 t| ≤ C*|e| ∧ |X e t-X 0 t| ≤ C*|e| := by
  obtain ⟨c,cp,hc⟩ := curvature_parameter_bound bp
  let C := 1+c+c*B*B
  have one : 1 ≤ C := by dsimp [C]; linarith [mul_nonneg (mul_nonneg cp.le bp) bp]
  refine ⟨C,one,?_⟩
  intro e he t ht
  have bound := hc e he
  refine ⟨(bound t ht).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg e)),?_⟩
  · dsimp [C]; linarith [mul_nonneg (mul_nonneg cp.le bp) bp]
  · apply (position_parameter_bound bp cp.le bound ht).trans
    calc
      c * |e| * B*B = (c*B*B)*|e| := by ring
      _ ≤ C*|e| := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (abs_nonneg e)

theorem fast_vertical_position_bound {B t : ℝ} (ht : t ∈ Icc 0 B) (e : ℝ) : |Y e t| ≤ B := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (C := (1:ℝ)) (f := ty e) (fun u _ => by
      simpa only [Real.norm_eq_abs,ty] using Real.abs_sin_le_one (angle e u))
  apply le_trans _ ht.2
  change |∫ u in (0:ℝ)..t, ty e u| ≤ t
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1,one_mul] using h

/-- At every point of the moving seam line, curvature is controlled even
    when the slope is large compared with the perturbation parameter. -/
theorem curvature_at_axis {B : ℝ} (bp : 0 ≤ B) :
    ∃ D ≥ 1, ∀ e β t : ℝ, |e| ≤ 1 → t ∈ Icc 0 B → X e t = β * Y e t →
      |K e t| ≤ D*(|β|+|e|) := by
  obtain ⟨C,one,all⟩ := fast_parameter_bound bp
  let D := 2*C+B
  have cd : 2*C ≤ D := by dsimp [D]; linarith
  have bd : B ≤ D := by dsimp [D]; linarith
  refine ⟨D,by linarith,?_⟩
  intro e β t he ht hit
  obtain ⟨k,x⟩ := all e he t ht
  have fk := frozen_positionX t
  have tri : |K e t| ≤ |K e t-K 0 t| + |X 0 t-X e t| + |X e t| := by
    calc
      _ = |(K e t-K 0 t + (X 0 t-X e t)) + X e t| := by rw [fk]; congr 1; ring
      _ ≤ _ := (abs_add_le (K e t-K 0 t+(X 0 t-X e t)) (X e t)).trans
        (add_le_add (abs_add_le (K e t-K 0 t) (X 0 t-X e t)) le_rfl)
  rw [abs_sub_comm (X 0 t) (X e t)] at tri
  have y := mul_le_mul_of_nonneg_left (fast_vertical_position_bound ht e) (abs_nonneg β)
  have last : |X e t| ≤ |β| * B := by simpa only [hit,abs_mul] using y
  nlinarith only [tri,x,k,last,mul_le_mul_of_nonneg_right cd (abs_nonneg e),
    mul_le_mul_of_nonneg_right bd (abs_nonneg β)]

end ClosedSimilarity.CrossingResponse
#print axioms ClosedSimilarity.CrossingResponse.fast_parameter_bound
#print axioms ClosedSimilarity.CrossingResponse.curvature_at_axis
