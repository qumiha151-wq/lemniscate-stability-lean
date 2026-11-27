import SolitonClassification.FastAxisWindow

noncomputable section
set_option maxHeartbeats 260000
open Set Filter MeasureTheory
open scoped Topology
namespace ClosedSimilarity.CrossingResponse

def responseValue (a : ℝ) : ℝ := -(∫ t in (0:ℝ)..a, K 0 t ^ 5) / 3

private theorem wy_cont : Continuous (fun z : ℝ × ℝ => stressY z.1 z.2) :=
  (((fast_coordinate_cont 0).pow 2).div_const 2 |>.mul ty_cont).add
    ((fast_coordinate_cont 1).mul tx_cont)

theorem frozen_vertical_stress (t : ℝ) : stressY 0 t = 1 := by
  unfold stressY
  rw [← (frozen_tangent t).2, ← (frozen_tangent t).1]
  simpa only [sq, ty, tx] using Real.sin_sq_add_cos_sq (angle 0 t)

private theorem dot_stress (e t : ℝ) :
    stressX e t * tx e t + stressY e t * ty e t = K e t ^ 2 / 2 := by
  have unit : ty e t ^ 2 + tx e t ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  unfold stressX stressY
  linear_combination (K e t ^ 2 / 2)*unit

private theorem ratio_forced {ι : Type*} {l : Filter ι} {e β m q k : ι → ℝ}
    {c q₀ D0 : ℝ} (one : 1≤D0)
    (he : Tendsto e l (𝓝 0)) (hb : Tendsto β l (𝓝 0))
    (mc : Tendsto (fun j => m j / e j) l (𝓝 c)) (qc : Tendsto q l (𝓝 q₀))
    (eps : ∀ᶠ j in l, 0<e j) (curv : ∀ᶠ j in l, |k j|≤D0*(|β j|+e j))
    (eq : ∀ᶠ j in l, β j=m j-q j*(k j)^2) : Tendsto (fun j => β j/e j) l (𝓝 c) := by
  let D := max D0 (max (|c|+1) (|q₀|+1))
  have d0 : D0 ≤ D := le_max_left ..
  have d1 : 1 ≤ D := one.trans d0
  have cm : |c|+1 ≤ D := (le_max_left ..).trans (le_max_right ..)
  have cq : |q₀|+1 ≤ D := (le_max_right ..).trans (le_max_right ..)
  have eSmall : ∀ᶠ j in l, 4*D^3*e j ≤ 1 := by
    have h : Tendsto (fun j => 4*D^3*e j) l (𝓝 0) := by simpa using he.const_mul (4*D^3)
    exact (h.eventually_lt_const zero_lt_one).mono (fun _ h => h.le)
  have bSmall : ∀ᶠ j in l, 4*D^3*|β j| ≤ 1 := by
    have h : Tendsto (fun j => 4*D^3*|β j|) l (𝓝 0) := by simpa using hb.abs.const_mul (4*D^3)
    exact (h.eventually_lt_const zero_lt_one).mono (fun _ h => h.le)
  have err : ∀ᶠ j in l, ‖β j/e j - m j/e j‖ ≤ 16*D^5 * e j := by
    filter_upwards [eps,curv,eq,eSmall,bSmall,mc.abs.eventually_lt_const (lt_add_one _),
      qc.abs.eventually_lt_const (lt_add_one _)] with j ep kB tanEq es bs mb qb
    have mB : |m j| ≤ D*e j := by
      change |m j/e j| < |c|+1 at mb
      rw [abs_div, abs_of_pos ep] at mb
      exact ((div_lt_iff₀ ep).mp mb).le.trans (mul_le_mul_of_nonneg_right cm ep.le)
    have est := (CrossingTangencies.tangency_accuracy d1 ep.le es bs mB (qb.le.trans cq)
      (kB.trans (mul_le_mul_of_nonneg_right d0 (add_nonneg (abs_nonneg _) ep.le))) tanEq).2
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos ep, div_le_iff₀ ep]
    simpa only [pow_two,mul_assoc] using est
  have vanish : Tendsto (fun j => β j/e j - m j/e j) l (𝓝 0) :=
    squeeze_zero_norm' err (by simpa using he.const_mul (16*D^5))
  simpa only [Pi.add_apply,sub_add_cancel,zero_add] using vanish.add mc

private theorem moving_value {ι : Type*} {l : Filter ι} (F : ℝ → ℝ → ℝ)
    (c : Continuous (fun z : ℝ × ℝ => F z.1 z.2)) {e r : ι → ℝ} {a : ℝ}
    (he : Tendsto e l (𝓝 0)) (hr : Tendsto r l (𝓝 a)) :
    Tendsto (fun j => F (e j) (r j)) l (𝓝 (F 0 a)) :=
  (c.tendsto (0,a)).comp (he.prodMk_nhds hr)

private theorem normalizedStress {ι : Type*} {l : Filter ι} {e r : ι → ℝ} {a : ℝ}
    (root : K 0 a=0) (he : Tendsto e l (𝓝 0)) (hr : Tendsto r l (𝓝 a))
    (eps : ∀ᶠ j in l, 0<e j):
    Tendsto (fun j => (stressX (e j) (r j) / stressY (e j) (r j))/e j) l (𝓝 (responseValue a)) := by
  have nn : Tendsto (fun j => (e j,r j)) l (𝓝[{z : ℝ × ℝ | z.1 ≠ 0}] ((0:ℝ),a)) :=
    tendsto_nhdsWithin_iff.mpr ⟨he.prodMk_nhds hr,eps.mono (fun _ h => h.ne')⟩
  have wx := (joint_response_quotient root).comp nn
  have wy := moving_value stressY wy_cont he hr
  rw [frozen_vertical_stress] at wy
  have h := wx.div wy one_ne_zero
  rw [div_one] at h
  apply h.congr
  intro j
  change (stressX (e j) (r j)/e j)/stressY (e j) (r j) = _
  ring

private theorem moving_curvature {ι : Type*} {l : Filter ι} {e β r : ι → ℝ} {a : ℝ}
    (ap : 0<a) (he : Tendsto e l (𝓝 0)) (hr : Tendsto r l (𝓝 a))
    (eps : ∀ᶠ j in l, 0<e j)
    (axis : ∀ᶠ j in l, X (e j) (r j) = β j * Y (e j) (r j)) :
    ∃ D ≥ 1, ∀ᶠ j in l, |K (e j) (r j)| ≤ D*(|β j|+e j) := by
  obtain ⟨D,one,bound⟩ := curvature_at_axis (B := a+1) (by linarith)
  refine ⟨D,one,?_⟩
  filter_upwards [eps,axis,hr.eventually_const_lt ap,hr.eventually_lt_const (lt_add_one a),
    he.eventually_lt_const zero_lt_one] with j ep ax lo hi small
  have h := bound (e j) (β j) (r j) (by rw [abs_of_pos ep]; exact small.le) ⟨lo.le,hi.le⟩ ax
  rwa [abs_of_pos ep] at h

/-- Tangency forces the scaled slope to be the stress response at the frozen root. -/
theorem slope_limit_of_tangent {ι : Type*} {l : Filter ι} {e β r : ι → ℝ}
    {a : ℝ} (ap : 0 < a) (root : K 0 a = 0) (simple : V 0 a ≠ 0)
    (he : Tendsto e l (𝓝 0)) (hb : Tendsto β l (𝓝 0)) (hr : Tendsto r l (𝓝 a))
    (eps : ∀ᶠ j in l, 0 < e j)
    (axis : ∀ᶠ j in l, X (e j) (r j) = β j * Y (e j) (r j))
    (tangent : ∀ᶠ j in l, β j * tx (e j) (r j) + ty (e j) (r j) = 0) :
    Tendsto (fun j => β j/e j) l (𝓝 (responseValue a)) := by
  obtain ⟨D,one,kB⟩ := moving_curvature ap he hr eps axis
  have ucv := moving_value tx tx_cont he hr
  have vcv := moving_value stressY wy_cont he hr
  rw [(frozen_tangent a).1] at ucv
  rw [frozen_vertical_stress] at vcv
  have qc := tendsto_const_nhds (x := (1:ℝ)) |>.div
    (((tendsto_const_nhds (x := (2:ℝ))).mul ucv).mul vcv)
    (mul_ne_zero (mul_ne_zero (by norm_num) simple) one_ne_zero)
  apply ratio_forced one he hb (normalizedStress root he hr eps) qc eps kB
  filter_upwards [ucv.eventually_ne simple,vcv.eventually_ne one_ne_zero,tangent] with j u v tan
  exact CrossingTangencies.slope_at_tangency u v (dot_stress _ _) tan

/-- Two distinct limiting stress variations exclude simultaneous tangency
    of the moving true-shot crossings for all sufficiently large indices. -/
theorem eventually_one_transverse {e β r s : ℕ → ℝ} {a b : ℝ}
    (ap : 0<a) (bp : 0<b) (ra : K 0 a=0) (rb : K 0 b=0)
    (sa : V 0 a ≠ 0) (sb : V 0 b ≠ 0) (different : responseValue a ≠ responseValue b)
    (he : Tendsto e atTop (𝓝 0)) (hb : Tendsto β atTop (𝓝 0))
    (hr : Tendsto r atTop (𝓝 a)) (hs : Tendsto s atTop (𝓝 b))
    (eps : ∀ᶠ j in atTop, 0<e j)
    (ar : ∀ᶠ j in atTop, X (e j) (r j) = β j * Y (e j) (r j))
    (as' : ∀ᶠ j in atTop, X (e j) (s j) = β j * Y (e j) (s j)) :
    ∀ᶠ j in atTop, β j * tx (e j) (r j) + ty (e j) (r j) ≠ 0 ∨
      β j * tx (e j) (s j) + ty (e j) (s j) ≠ 0 := by
  by_contra bad
  have frequent : ∃ᶠ j in atTop, ¬(β j * tx (e j) (r j) + ty (e j) (r j) ≠ 0 ∨
      β j * tx (e j) (s j) + ty (e j) (s j) ≠ 0) := not_eventually.mp bad
  obtain ⟨φ,mono,fail⟩ := extraction_of_frequently_atTop frequent
  have f := mono.tendsto_atTop
  have both (j) := not_or.mp (fail j)
  have one := slope_limit_of_tangent ap ra sa (he.comp f) (hb.comp f) (hr.comp f)
    (f.eventually eps) (f.eventually ar) (Eventually.of_forall (fun j => not_ne_iff.mp (both j).1))
  have two := slope_limit_of_tangent bp rb sb (he.comp f) (hb.comp f) (hs.comp f)
    (f.eventually eps) (f.eventually as') (Eventually.of_forall (fun j => not_ne_iff.mp (both j).2))
  exact different (tendsto_nhds_unique one two)

end ClosedSimilarity.CrossingResponse
#print axioms ClosedSimilarity.CrossingResponse.slope_limit_of_tangent
#print axioms ClosedSimilarity.CrossingResponse.eventually_one_transverse
