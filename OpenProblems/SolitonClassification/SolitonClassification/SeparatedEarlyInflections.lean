import SolitonClassification.PrimitiveInflections

noncomputable section
namespace ClosedSimilarity.ReflectedArc.ZeroTurnExpander
open GlobalSupport OuterStress MeasureTheory Set

/-- Every sufficiently wide subinterval of the initial slow time interval
    contains a simple zero, expressed here in physical arclength. -/
private theorem simple_inflection_in_window {L b A C : ℝ} (P : ZeroTurnExpander L b)
    (large : 32 ≤ b) (hA : 0 ≤ A) (hAC : A ≤ C) (hC : C ≤ 1)
    (wide : 8 * Real.pi ≤ (C - A) * b) :
    ∃ s ∈ Icc (A * Real.sqrt b) (C * Real.sqrt b), P.k s = 0 ∧ deriv P.k s ≠ 0 := by
  have bp : 0 < b := by linarith
  let δ := b⁻¹
  let z := centreData b bp
  have hd : 0 < δ := inv_pos.mpr bp
  have small : δ ≤ 1/32 := by
    change b⁻¹ ≤ _; rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) large
  have init : z.K 0 = 0 ∧ z.V 0 = 1 ∧ z.p 0 = 0 ∧ z.q 0 = 0 := by
    simp [z, centreData, ofSupport, solution_zero, bp.ne']
  obtain ⟨hk, hv, hp, hq⟩ := init
  have bounds (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      Rates δ x z.root z.shape z.slope z.along z.across ∧ |z.along x| ≤ 1 ∧ |z.across x| ≤ 1 ∧
      4*1*δ ≤ z.root x^3 ∧ 1/2 ≤ z.root x := by
    obtain ⟨pq, amp⟩ := z.centre_bounds hd hk hv hp hq hx.1
    have x2 := pow_le_pow_left₀ hx.1 hx.2 2
    have apos : 0 < z.amplitude x := by nlinarith
    have rsq : z.root x^2 = z.amplitude x := Real.sq_sqrt apos.le
    have pos : 0 ≤ z.root x := Real.sqrt_nonneg _
    have rlo : 1/2 ≤ z.root x := le_of_sq_le_sq (by nlinarith) pos
    have r3 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) rlo 3
    have frame := z.radius_sq x apos
    refine ⟨z.normalized_rates x apos hd, ?_, ?_, by linarith, rlo⟩
    · apply le_of_sq_le_sq _ zero_le_one
      rw [sq_abs]; nlinarith [sq_nonneg (z.across x)]
    · apply le_of_sq_le_sq _ zero_le_one
      rw [sq_abs]; nlinarith [sq_nonneg (z.along x)]
  let g := Angle.spin δ z.root z.shape z.slope z.along z.across
  let θ := fun x : ℝ => ∫ t in (0:ℝ)..x, g t
  have cg : ContinuousOn g (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact fun x hx => (Angle.spin_continuousAt (bounds x hx).1).continuousWithinAt
  have ct : ContinuousOn θ (Icc 0 1) := by
    simpa only [uIcc_of_le zero_le_one] using intervalIntegral.continuousOn_primitive_interval
      (cg.integrableOn_compact isCompact_uIcc (μ := volume))
  have sub : Icc A C ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc hA hC
  have inc := Angle.winding_on_interval hAC (fun x hx => bounds x (sub hx))
  have lower : (C-A)*b/8 ≤ ∫ t in A..C, g t := by
    convert inc using 1; dsimp [δ]; field_simp; ring
  have integr : IntervalIntegrable g volume 0 1 := cg.intervalIntegrable
  have add := intervalIntegral.integral_add_adjacent_intervals
    (integr.mono_set (show uIcc 0 A ⊆ uIcc 0 1 by
      simp only [uIcc_of_le hA, uIcc_of_le zero_le_one]; exact Icc_subset_Icc_right (hAC.trans hC)))
    (integr.mono_set (show uIcc A C ⊆ uIcc 0 1 by
      simpa only [uIcc_of_le hAC, uIcc_of_le zero_le_one] using sub))
  change θ A + (∫ t in A..C, g t) = θ C at add
  let m : ℤ := ⌈θ A / Real.pi⌉
  have low : θ A ≤ (m:ℝ)*Real.pi := (div_le_iff₀ Real.pi_pos).mp (Int.le_ceil _)
  have high : (m:ℝ)*Real.pi ≤ θ C := by
    have cut : (m:ℝ) < θ A/Real.pi + 1 := Int.ceil_lt_add_one _
    have bound := (lt_div_iff₀ Real.pi_pos).mp (show (m:ℝ)-1 < θ A/Real.pi by linarith)
    linarith
  obtain ⟨u, hu, hit⟩ := intermediate_value_Icc hAC (ct.mono sub) ⟨low, high⟩
  have sn : Real.sin (θ u) = 0 := by rw [hit, Real.sin_int_mul_pi]
  let f := Real.sqrt δ
  have fp : 0 < f := Real.sqrt_pos.mpr hd
  have scale : 1/f = Real.sqrt b := by simp [f, δ, Real.sqrt_inv]
  have point := ((physical_centre_winding large).1 u (sub hu)).2.1
  change Angle.sn z.shape u = Real.sin (θ u) at point
  have canon : z.shape u = 0 := (div_eq_zero_iff.mp (point.trans sn)).resolve_right (by positivity)
  have rp := (bounds u (sub hu)).1.pos
  have zeroK : z.K u = 0 := (div_eq_zero_iff.mp canon).resolve_right rp.ne'
  have eq := congrFun P.cartesianSupport_eq_solution (u/f)
  have K : z.K u = f*P.k (u/f) := by
    change f*(solution 1 ![0,b,0,0] (u/f) 0) = _; rw [← eq]; rfl
  have pk := (mul_eq_zero.mp (K.symm.trans zeroK)).resolve_left fp.ne'
  refine ⟨u/f, ?_, pk, ?_⟩
  · have phys : u/f = u*Real.sqrt b := by rw [← scale]; ring
    rw [phys]
    exact ⟨mul_le_mul_of_nonneg_right hu.1 (Real.sqrt_nonneg _),
      mul_le_mul_of_nonneg_right hu.2 (Real.sqrt_nonneg _)⟩
  · intro flat
    have V : z.V u = 0 := by
      change δ*(solution 1 ![0,b,0,0] (u/f) 1) = _
      rw [← eq]; change δ*deriv P.k (u/f) = 0; rw [flat, mul_zero]
    simp [Data.root, Data.amplitude, zeroK, V] at rp

/-- On every sufficiently high-marker closed expander, any prescribed finite
    number of early simple curvature zeros can be separated by more than
    any prescribed physical arclength. -/
theorem separated_early_simple_inflections (n : ℕ) (H : ℝ) (hH : 0 < H) :
    ∃ B : ℝ, ∀ {L b : ℝ}, B ≤ b → ∀ P : ZeroTurnExpander L b,
      ∃ v : Fin n → ℝ,
        (∀ i, 0 < v i ∧ v i ≤ Real.sqrt b/576 ∧ P.k (v i) = 0 ∧ deriv P.k (v i) ≠ 0) ∧
        ∀ i j, i ≠ j → H < |v i - v j| := by
  let w : ℝ := 1 / (1152*((n:ℝ)+1))
  have wp : 0 < w := by dsimp [w]; positivity
  have total : (2*((n:ℝ)+1))*w = 1/576 := by dsimp [w]; field_simp; ring
  refine ⟨max 32 (max (8*Real.pi/w) ((H/w+1)^2)), ?_⟩
  intro L b big P
  have large : 32 ≤ b := (le_max_left ..).trans big
  have bb := (le_max_right ..).trans big
  have wide : 8*Real.pi ≤ w*b := by
    have h : 8*Real.pi/w ≤ b := (le_max_left ..).trans bb
    simpa only [mul_comm] using (div_le_iff₀ wp).mp h
  have bp : 0 < b := by linarith
  have rpos := Real.sqrt_pos.mpr bp
  have gap : H < w*Real.sqrt b := by
    have h : (H/w+1)^2 ≤ b := (le_max_right ..).trans bb
    have low : H/w+1 ≤ Real.sqrt b := by
      simpa only [Real.sqrt_sq (by positivity : 0 ≤ H/w+1)] using Real.sqrt_le_sqrt h
    have strict : H/w < Real.sqrt b := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ wp).mp strict
  let a := fun i : Fin n => (2*(i.val:ℝ)+1)*w
  let c := fun i : Fin n => a i + w
  have apos (i : Fin n) : 0 < a i := by dsimp [a]; positivity
  have cap (i : Fin n) : c i ≤ 1/576 := by
    have hn : (i.val:ℝ) ≤ n := by exact_mod_cast i.isLt.le
    have mult := mul_le_mul_of_nonneg_right hn wp.le
    dsimp [c,a]; linarith
  have hit (i : Fin n) :
      ∃ s ∈ Icc (a i * Real.sqrt b) (c i * Real.sqrt b), P.k s = 0 ∧ deriv P.k s ≠ 0 := by
    apply simple_inflection_in_window P large (apos i).le (by dsimp [c]; linarith)
      ((cap i).trans (by norm_num))
    simpa [c] using wide
  choose v loc zero simple using hit
  refine ⟨v, ?_, ?_⟩
  · intro i
    have upper := (loc i).2.trans (mul_le_mul_of_nonneg_right (cap i) rpos.le)
    exact ⟨(mul_pos (apos i) rpos).trans_le (loc i).1, by linarith, zero i, simple i⟩
  · have sep {i j : Fin n} (hij : i < j) : H < v j - v i := by
      have hn : (i.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast (show i.val+1 ≤ j.val from hij)
      have mult := mul_le_mul_of_nonneg_right hn wp.le
      have d : c i+w ≤ a j := by dsimp [c,a]; linarith
      have scaled := mul_le_mul_of_nonneg_right d rpos.le
      linarith [(loc i).2, (loc j).1]
    intro i j ne
    rcases lt_or_gt_of_ne ne with hij | hji
    · exact (sep hij).trans_le (by rw [abs_sub_comm]; exact le_abs_self _)
    · exact (sep hji).trans_le (le_abs_self _)

end ClosedSimilarity.ReflectedArc.ZeroTurnExpander
#print axioms ClosedSimilarity.ReflectedArc.ZeroTurnExpander.separated_early_simple_inflections
