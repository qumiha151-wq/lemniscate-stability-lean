import SolitonClassification.MovingSeamReflection
import SolitonClassification.PhysicalSeamScale

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open FrozenStress

/-- Restoring physical scale leaves the radial direction, oscillator
    coordinates, stress amplitude in moving radius units, corrected height,
    and transverse impact exactly invariant. -/
theorem restore_invariants {l : ℝ} (hl : 0<l) (x : Phase) :
    scale (restore l x)=l*scale x ∧ root (restore l x)=l*root x ∧
    shape (restore l x)=shape x ∧ slope (restore l x)=slope x ∧
    along (restore l x)=along x ∧ across (restore l x)=across x ∧
    height (restore l x)=height x ∧ impact (restore l x)=impact x := by
  have r : radiusSquared (restore l x)=l^6*radiusSquared x := by simp [radiusSquared,restore]; ring
  have e : stressSquared (restore l x)=l^4*stressSquared x := by simp [stressSquared,restore]; ring
  have re : 0≤radiusSquared x := by unfold radiusSquared; positivity
  have s : scale (restore l x)=l*scale x := by
    unfold scale
    rw [r,Real.mul_rpow (by positivity) re,←Real.rpow_natCast l 6,←Real.rpow_mul hl.le]
    norm_num
  have a : amplitude (restore l x)=l^2*amplitude x := by
    unfold amplitude
    rw [e,show l^4=(l^2)^2 by ring,Real.sqrt_mul (by positivity),Real.sqrt_sq (sq_nonneg _)]
  have rt : root (restore l x)=l*root x := by
    unfold root
    rw [a,Real.sqrt_mul (sq_nonneg l),Real.sqrt_sq hl.le]
  have sh : shape (restore l x)=shape x := by
    simp only [shape,rt]
    change l*x 0/(l*root x)=_
    rw [mul_div_mul_left _ _ hl.ne']
  have sl : slope (restore l x)=slope x := by
    simp only [slope,a]
    change l^2*x 1/(l^2*amplitude x)=_
    rw [mul_div_mul_left _ _ (pow_ne_zero _ hl.ne')]
  have al : along (restore l x)=along x := by
    simp only [along,a,s]
    change ((l*x 0)^2/2*(l^3*x 3)+(l^2*x 1)*(l^3*x 2))/
      ((l^2*amplitude x)*(l*scale x)^3)=_
    rw [show ((l*x 0)^2/2*(l^3*x 3)+(l^2*x 1)*(l^3*x 2))=l^5*(x 0^2/2*x 3+x 1*x 2) by ring,
      show (l^2*amplitude x)*(l*scale x)^3=l^5*(amplitude x*scale x^3) by ring,
      mul_div_mul_left _ _ (pow_ne_zero _ hl.ne')]
  have ac : across (restore l x)=across x := by
    simp only [across,a,s]
    change ((l*x 0)^2/2*(l^3*x 2)-(l^2*x 1)*(l^3*x 3))/
      ((l^2*amplitude x)*(l*scale x)^3)=_
    rw [show ((l*x 0)^2/2*(l^3*x 2)-(l^2*x 1)*(l^3*x 3))=l^5*(x 0^2/2*x 2-x 1*x 3) by ring,
      show (l^2*amplitude x)*(l*scale x)^3=l^5*(amplitude x*scale x^3) by ring,
      mul_div_mul_left _ _ (pow_ne_zero _ hl.ne')]
  exact ⟨s,rt,sh,sl,al,ac,by simp only [height,rt,s,sh,sl,al,ac,mul_div_mul_left _ _ hl.ne'],
    by simp only [impact,rt,s,ac,mul_div_mul_left _ _ hl.ne']⟩

/-- The negative-time crossing is a crossing by the coefficient-one physical
    seam orbit after restoring arclength and the actual initial support. -/
theorem physical_incoming_crossing {l d : ℝ} (hl : 0<l) (eq : l^4*d=1)
    {c t H : ℝ} (hit : height (shot d c t)=H) :
    let x := solution 1 (restore l ![c,0,1,0]) (-t/l);
    -height x=H ∧ impact x=impact (shot d c t) ∧ scale x=l*scale (shot d c (-t)) := by
  dsimp only
  rw [physical_support_conjugacy eq,show l*(-t/l)=-t by field_simp [hl.ne']]
  obtain ⟨s,_,_,_,_,_,h,i⟩ := restore_invariants hl (shot d c (-t))
  have neg := negative_section d c t H hit
  exact ⟨by rw [show height (restore l (solution d ![c,0,1,0] (-t)))=_ from h]; exact neg.1,
    i.trans neg.2.1,s⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.physical_incoming_crossing
