import SolitonClassification.MovingSeamHeight
import SolitonClassification.IncomingSectionCoordinates

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open FrozenStress

private theorem chart {z : Phase} (reg : regular z) :
    0 < scale z ∧ 0 < root z ∧ (root z)^2=amplitude z ∧
    ((shape z)^2/2)^2+(slope z)^2=1 ∧ (along z)^2+(across z)^2=1 ∧
    z 2/(scale z)^3=slope z*along z+(shape z)^2/2*across z ∧
    z 3/(scale z)^3=(shape z)^2/2*along z-slope z*across z := by
  have hs : 0 < scale z := Real.rpow_pos_of_pos reg.1 _
  have ha : 0 < amplitude z := Real.sqrt_pos.mpr reg.2
  have hr : 0 < root z := Real.sqrt_pos.mpr ha
  have sr : (scale z)^6=radiusSquared z := by
    unfold scale
    rw [←Real.rpow_natCast _ 6,←Real.rpow_mul reg.1.le]; norm_num
  have aa : (amplitude z)^2=(z 0^2/2)^2+z 1^2 := Real.sq_sqrt reg.2.le
  have rr : (root z)^2=amplitude z := Real.sq_sqrt ha.le
  let u := (shape z)^2/2
  let w := slope z
  let P := z 2/(scale z)^3
  let Q := z 3/(scale z)^3
  have n1 : u=(z 0^2/2)/amplitude z := by simp only [u,shape,div_pow,rr]; ring
  have one : u^2+w^2=1 := by rw [n1]; unfold w slope; field_simp [ha.ne']; nlinarith only [aa]
  have unit : P^2+Q^2=1 := by
    unfold P Q
    field_simp [hs.ne']
    unfold radiusSquared at sr
    nlinarith only [sr]
  have a : along z=u*Q+w*P := by
    rw [n1]
    unfold along w slope Q P
    field_simp [hs.ne',ha.ne']
  have b : across z=u*P-w*Q := by
    rw [n1]
    unfold across w slope Q P
    field_simp [hs.ne',ha.ne']
  refine ⟨hs,hr,rr,one,?_,?_,?_⟩
  · rw [a,b]
    linear_combination (P^2+Q^2)*one+unit
  · change P=w*along z+u*across z
    rw [a,b]
    linear_combination -P*one
  · change Q=u*along z-w*across z
    rw [a,b]
    linear_combination -Q*one

/-- Equality of the incoming section coordinates recovers the full four
    physical support coordinates, with no ambiguity in the tangent frame. -/
theorem physical_state_injective {x y : Phase} (hx : regular x) (hy : regular y)
    (bigX : 4 ≤ root x/scale x) (bigY : 4 ≤ root y/scale y)
    (inX : 0 ≤ along x) (inY : 0 ≤ along y)
    (radius : scale x=scale y) (phaseU : shape x=shape y) (phaseW : slope x=slope y)
    (impact : root x/scale x*across x=root y/scale y*across y) (he : height x=height y) :
    x=y := by
  obtain ⟨sx,rx,rrx,ox,ax,px,qx⟩ := chart hx
  obtain ⟨sy,ry,rry,_,ay,py,qy⟩ := chart hy
  have quad : (shape x)^2/2 ≤ 1 := le_of_sq_le_sq
    (by nlinarith only [ox,sq_nonneg (slope x)]) zero_le_one
  have hu : |shape x| ≤ 2 := by
    apply le_of_sq_le_sq _ (by norm_num)
    rw [sq_abs]
    linarith only [quad]
  have hw : |slope x| ≤ 1 := by
    apply le_of_sq_le_sq _ zero_le_one
    rw [sq_abs]
    linarith only [ox,sq_nonneg ((shape x)^2/2),show (1:ℝ)^2=1 by norm_num]
  have h := Incoming.recover_frame hu hw bigX bigY inX inY ax ay impact (by
    unfold height at he
    rw [←phaseU,←phaseW] at he
    linarith)
  obtain ⟨rootEq,a,b⟩ := h
  rw [radius] at rootEq
  have rr : root x=root y := by simpa only [div_left_inj' sy.ne'] using rootEq
  have am : amplitude x=amplitude y := by rw [←rrx,←rry,rr]
  have e0 := phaseU
  have e1 := phaseW
  unfold shape at e0
  unfold slope at e1
  rw [rr] at e0
  rw [am] at e1
  rw [radius,phaseW,phaseU,a,b] at px qx
  funext i
  fin_cases i
  · exact (div_left_inj' ry.ne').mp e0
  · exact (div_left_inj' (Real.sqrt_pos.mpr hy.2).ne').mp e1
  · exact (div_left_inj' (pow_ne_zero 3 sy.ne')).mp (px.trans py.symm)
  · exact (div_left_inj' (pow_ne_zero 3 sy.ne')).mp (qx.trans qy.symm)

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.physical_state_injective
