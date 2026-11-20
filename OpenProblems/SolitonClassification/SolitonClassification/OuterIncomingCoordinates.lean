import SolitonClassification.OuterStressOrbit
import SolitonClassification.MovingSeamReflection

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open ReflectedArc

/-- Outer position radius and inner oscillator radius in the same physical state. -/
def outerRadius (δ : ℝ) (x : Phase) := Real.sqrt δ*(scale x)^3
def innerRoot (x : Phase) := root x/scale x

theorem scale_power (x : Phase) : (scale x)^6=radiusSquared x := by
  unfold scale
  rw [←Real.rpow_natCast _ 6,←Real.rpow_mul (show 0≤radiusSquared x by unfold radiusSquared; positivity)]
  norm_num

theorem unit_chart (x : Phase) (reg : regular x) :
    (shape x^2/2)^2+slope x^2=1 ∧ along x^2+across x^2=1 := by
  have ha : 0<amplitude x := Real.sqrt_pos.mpr reg.2
  have hr : 0<root x := Real.sqrt_pos.mpr ha
  have hs : 0<scale x := Real.rpow_pos_of_pos reg.1 _
  have A : amplitude x^2=(x 0^2/2)^2+x 1^2 := Real.sq_sqrt reg.2.le
  have r : root x^2=amplitude x := Real.sq_sqrt ha.le
  have s : scale x^6=x 2^2+x 3^2 := scale_power x
  constructor
  · unfold shape slope
    rw [show (x 0/root x)^2=x 0^2/amplitude x by rw [div_pow,r]]
    field_simp [ha.ne']
    nlinarith only [A]
  · unfold along across
    field_simp [ha.ne',hs.ne']
    linear_combination -((x 2)^2+(x 3)^2)*4*A - 4*(amplitude x)^2*s

/-- Identities in the original support coordinates. The phase pair is unchanged,
    while the two frame projections differ by precisely the outer radius. -/
theorem outer_chart {δ : ℝ} (hd : 0<δ) (z : ℝ → Support)
    (hz : ∀s,HasDerivAt z (supportField (z s)) s) (s : ℝ) :
    let y := OuterStress.ofSupport hd z hz
    let x := z (s/Real.sqrt δ)
    regular x →
      y.root s = Real.sqrt δ * root x ∧
      y.shape s = shape x ∧ y.slope s = slope x ∧
      y.along s = along x*outerRadius δ x ∧ y.across s = across x*outerRadius δ x ∧
      (innerRoot x)^3 * outerRadius δ x * δ = y.root s^3 ∧
      impact x*(innerRoot x)^2*(outerRadius δ x)^2*δ = y.across s*y.root s^3 ∧
      (1/scale x^4)^3*(outerRadius δ x)^4=δ^2 := by
  dsimp only
  let f := Real.sqrt δ
  let y := OuterStress.ofSupport hd z hz
  let x := z (s/f)
  intro reg
  have hf : 0<f := Real.sqrt_pos.mpr hd
  have fs : f^2=δ := Real.sq_sqrt hd.le
  have ha : 0<amplitude x := Real.sqrt_pos.mpr reg.2
  have hr : 0<root x := Real.sqrt_pos.mpr ha
  have hl : 0<scale x := Real.rpow_pos_of_pos reg.1 _
  have A : y.amplitude s=δ*amplitude x := by
    have ea := y.amplitude_sq s
    have ep : amplitude x^2=(x 0^2/2)^2+x 1^2 := Real.sq_sqrt reg.2.le
    have nn : 0≤y.amplitude s := Real.sqrt_nonneg _
    apply (sq_eq_sq₀ nn (mul_nonneg hd.le ha.le)).mp
    rw [ea,mul_pow,ep]
    change ((f*x 0)^2/2)^2+(δ*x 1)^2=_
    rw [mul_pow,fs]; ring
  have R : y.root s=f*root x := by
    unfold OuterStress.Data.root
    rw [A,Real.sqrt_mul hd.le]
    rfl
  have rad : y.radial s=δ*f*(x 0^2/2*x 3+x 1*x 2) := by
    change (f*x 0)^2/2*(f*x 3)+δ*x 1*(f*x 2)=_
    rw [mul_pow,fs]; ring
  have cross : y.transverse s=δ*f*(x 0^2/2*x 2-x 1*x 3) := by
    change (f*x 0)^2/2*(f*x 2)-δ*x 1*(f*x 3)=_
    rw [mul_pow,fs]; ring
  have al : y.along s=along x*outerRadius δ x := by
    unfold OuterStress.Data.along
    rw [rad,A]
    unfold along outerRadius
    change _ = _*(f*_)
    field_simp [hd.ne',ha.ne',hl.ne']
  have ac : y.across s=across x*outerRadius δ x := by
    unfold OuterStress.Data.across
    rw [cross,A]
    unfold across outerRadius
    change _ = _*(f*_)
    field_simp [hd.ne',ha.ne',hl.ne']
  refine ⟨R,?_,?_,al,ac,?_,?_,?_⟩
  · change f*x 0/y.root s=x 0/root x
    rw [R]; field_simp [hf.ne',hr.ne']
  · change δ*x 1/y.amplitude s=x 1/amplitude x
    rw [A]; field_simp [hd.ne',ha.ne']
  · change (root x/scale x)^3*(f*scale x^3)*δ=y.root s^3
    rw [R,←fs]; field_simp [hl.ne']
  · change (root x/scale x*across x)*(root x/scale x)^2*(outerRadius δ x)^2*δ=y.across s*y.root s^3
    rw [ac,R]
    unfold outerRadius
    change (root x / scale x * across x) * (root x / scale x)^2 * (f*scale x^3)^2 * δ =
      across x*(f*scale x^3)*(f*root x)^3
    rw [←fs]; field_simp [hl.ne']
  · change (1/scale x^4)^3*(f*scale x^3)^4=δ^2
    rw [←fs]; field_simp [hl.ne']

theorem regular_of_outer_along {δ : ℝ} (hd : 0<δ) (z : ℝ → Support)
    (hz : ∀s,HasDerivAt z (supportField (z s)) s) {s : ℝ}
    (pos : 0<(OuterStress.ofSupport hd z hz).along s) : regular (z (s/Real.sqrt δ)) := by
  let x := z (s/Real.sqrt δ)
  let f := Real.sqrt δ
  change 0<((f*x 0)^2/2*(f*x 3)+δ*x 1*(f*x 2))/_ at pos
  constructor
  · change 0<x 2^2+x 3^2
    by_contra! hn
    have h2 : x 2=0 := by nlinarith [sq_nonneg (x 3),sq_nonneg (x 2)]
    have h3 : x 3=0 := by nlinarith [sq_nonneg (x 2),sq_nonneg (x 3)]
    simp [h2,h3] at pos
  · change 0<(x 0^2/2)^2+x 1^2
    by_contra! hn
    have h1 : x 1=0 := by nlinarith [sq_nonneg (x 0^2/2),sq_nonneg (x 1)]
    have h0 : x 0^2/2=0 := by nlinarith [sq_nonneg (x 1),sq_nonneg (x 0^2/2)]
    have h0' : x 0=0 := by nlinarith
    simp [h0',h1] at pos

theorem radius_identity {δ : ℝ} (hd : 0<δ) (z : ℝ → Support)
    (hz : ∀s,HasDerivAt z (supportField (z s)) s) (s : ℝ) :
    let y := OuterStress.ofSupport hd z hz
    (outerRadius δ (z (s/Real.sqrt δ)))^2=(y.p s)^2+(y.q s)^2 := by
  dsimp only
  let x := z (s/Real.sqrt δ)
  change (Real.sqrt δ*scale x^3)^2=(Real.sqrt δ*x 2)^2+(Real.sqrt δ*x 3)^2
  have h : scale x^6=x 2^2+x 3^2 := scale_power x
  linear_combination (Real.sqrt δ)^2*h

theorem height_error {x : Phase} (reg : regular x) (far : 1 ≤ innerRoot x) :
    |-height x-(innerRoot x)^2*along x| ≤ 1 := by
  obtain ⟨osc,unit⟩ := unit_chart x reg
  have corr := FrozenStress.chi_bound osc unit
  have h : -height x-(innerRoot x)^2*along x =
      FrozenStress.chi (shape x) (slope x) (along x) (across x)/innerRoot x := by
    unfold height innerRoot; ring
  rw [h,abs_div,abs_of_pos (by linarith : 0 < innerRoot x)]
  exact (div_le_one (by linarith)).mpr (by linarith)

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.outer_chart
