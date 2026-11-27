import SolitonClassification.Rotating.IntegerGlobalCrossingGeometry

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCrossings
open Set
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def projection {b L : ℝ} (I : WindingOneImmersion b L) (nx ny s : ℝ) := nx*I.x s+ny*I.y s
def margin (nx ny length : ℝ) := 10*(|nx|+|ny|)*length^2/8

theorem projected_chord_error {b L : ℝ} (I : WindingOneImmersion b L)
    (nx ny : ℝ) {a e z : ℝ} (ae : a≤e) (hz : z∈Icc 0 1)
    (bound : ∀v∈Icc a e,|I.k v|≤10) :
    |projection I nx ny (chord z a e)-chord z (projection I nx ny a) (projection I nx ny e)|≤
      margin nx ny (e-a) := by
  let f:=projection I nx ny
  let g:=fun v => nx*Real.cos (I.theta v)+ny*Real.sin (I.theta v)
  let d:=fun v => nx*(-Real.sin (I.theta v)*I.k v)+ny*(Real.cos (I.theta v)*I.k v)
  have df (v : ℝ) : HasDerivAt f (g v) v := ((I.tangentX v).const_mul nx).add ((I.tangentY v).const_mul ny)
  have dg (v : ℝ) : HasDerivAt g (d v) v :=
    (((I.angleDerivative v).cos).const_mul nx).add (((I.angleDerivative v).sin).const_mul ny)
  apply chord_error (K:=10*(|nx|+|ny|)) df dg ae (by positivity) _ hz
  intro v hv
  dsimp only [d]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul ny,abs_mul,abs_neg,abs_mul]
  have k := bound v hv
  have A := mul_le_mul (Real.abs_sin_le_one (I.theta v)) k (abs_nonneg _) zero_le_one
  have B := mul_le_mul (Real.abs_cos_le_one (I.theta v)) k (abs_nonneg _) zero_le_one
  linarith only [mul_le_mul_of_nonneg_left A (abs_nonneg nx),mul_le_mul_of_nonneg_left B (abs_nonneg ny)]

private theorem affine_parameter {a e s : ℝ} (hs : s∈Icc a e) :
    ∃z∈Icc (0:ℝ) 1,s=chord z a e := by
  by_cases eq : a=e
  · exact ⟨0,⟨le_rfl,zero_le_one⟩,by have v : s=a := le_antisymm (eq ▸ hs.2 : s≤a) hs.1; simp [chord,v]⟩
  · have pos : 0<e-a := sub_pos.mpr (lt_of_le_of_ne (hs.1.trans hs.2) eq)
    refine ⟨(s-a)/(e-a),⟨div_nonneg (sub_nonneg.mpr hs.1) pos.le,(div_le_one pos).mpr (by linarith [hs.2])⟩,?_⟩
    unfold chord
    field_simp [pos.ne'];ring

theorem projection_enclosure {b L : ℝ} (I : WindingOneImmersion b L) (nx ny : ℝ) {a e s : ℝ}
    (hs : s∈Icc a e) (bound : ∀v∈Icc a e,|I.k v|≤10) :
    min (projection I nx ny a) (projection I nx ny e)-margin nx ny (e-a) ≤ projection I nx ny s ∧
    projection I nx ny s ≤ max (projection I nx ny a) (projection I nx ny e)+margin nx ny (e-a) := by
  obtain ⟨z,hz,eq⟩ := affine_parameter hs
  have err := abs_le.mp (projected_chord_error I nx ny (hs.1.trans hs.2) hz bound)
  rw [←eq] at err
  let p:=projection I nx ny a
  let q:=projection I nx ny e
  have w : 0≤1-z := sub_nonneg.mpr hz.2
  have lo : min p q≤chord z p q := by
    unfold chord
    have x := mul_le_mul_of_nonneg_left (min_le_left p q) w
    have y := mul_le_mul_of_nonneg_left (min_le_right p q) hz.1
    linarith only [x,y]
  have up : chord z p q≤max p q := by
    unfold chord
    have x := mul_le_mul_of_nonneg_left (le_max_left p q) w
    have y := mul_le_mul_of_nonneg_left (le_max_right p q) hz.1
    linarith only [x,y]
  change min p q - _ ≤ _ ∧ _ ≤ max p q + _
  constructor <;> linarith only [err.1,err.2,lo,up]

/-- A strict endpoint projection gap exceeding both curvature margins
excludes intersections on the complete pair of physical arcs. -/
theorem separated_projected_chords {b L : ℝ} (I : WindingOneImmersion b L) (nx ny : ℝ)
    {a e c d s t : ℝ} (hs : s∈Icc a e) (ht : t∈Icc c d)
    (ka : ∀v∈Icc a e,|I.k v|≤10) (kc : ∀v∈Icc c d,|I.k v|≤10)
    (gap : max (projection I nx ny a) (projection I nx ny e)+margin nx ny (e-a)+margin nx ny (d-c) <
      min (projection I nx ny c) (projection I nx ny d)) :
    (I.x s,I.y s)≠(I.x t,I.y t) := by
  intro eq
  have ep : projection I nx ny s=projection I nx ny t := by
    unfold projection
    rw [show I.x s=I.x t from congrArg Prod.fst eq,show I.y s=I.y t from congrArg Prod.snd eq]
  linarith only [(projection_enclosure I nx ny hs ka).2,(projection_enclosure I nx ny ht kc).1,gap,ep]

end
end SolitonClassification.Rotating.IntegerTarget.GlobalCrossings
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCrossings.separated_projected_chords
