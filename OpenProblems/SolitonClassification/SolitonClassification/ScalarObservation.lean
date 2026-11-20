import SolitonClassification.TangentLawGeometry

/-! Recovery of the square of arclength curvature from a single directional
height or squared distance. The equations hold also at stationary points
of the observed coordinate, and use the actual position derivatives. -/
noncomputable section
namespace ClosedSimilarity.ClosedUnitFrenetCurve

theorem height_curvature_identity (C : ClosedUnitFrenetCurve) {u v : ℝ}
    (unit : u^2+v^2=1) (s : ℝ) :
    let h := fun t => u*C.x t + v*C.y t
    (1-(deriv h s)^2)*(C.k s)^2=(deriv (deriv h) s)^2 := by
  let h := fun t => u*C.x t + v*C.y t
  have dh (t : ℝ) : deriv h t = u*C.tx t+v*C.ty t :=
    ((C.dx t).const_mul u |>.add ((C.dy t).const_mul v)).deriv
  have d2 : deriv (deriv h) s = C.k s*(-u*C.ty s+v*C.tx s) := by
    rw [funext dh]
    have d := (((C.dtx s).const_mul u).add ((C.dty s).const_mul v)).deriv
    simp only [Pi.add_def] at d
    rw [d]
    ring
  change (1-(deriv h s)^2)*(C.k s)^2=(deriv (deriv h) s)^2
  rw [dh,d2]
  linear_combination -(C.k s)^2*((u^2+v^2)*(C.unit s)+unit)

theorem squared_distance_curvature_identity (C : ClosedUnitFrenetCurve) (a b s : ℝ) :
    let h := fun t => (C.x t-a)^2+(C.y t-b)^2
    (h s-(deriv h s/2)^2)*(C.k s)^2=(deriv (deriv h) s/2-1)^2 := by
  let x := fun t => C.x t-a
  let y := fun t => C.y t-b
  let h := fun t => (x t)^2+(y t)^2
  have dx (t:ℝ) : HasDerivAt x (C.tx t) t := (C.dx t).sub_const a
  have dy (t:ℝ) : HasDerivAt y (C.ty t) t := (C.dy t).sub_const b
  have dh (t:ℝ) : deriv h t = 2*x t*C.tx t+2*y t*C.ty t := by
    simpa [h, Pi.add_def, Pi.pow_def] using (((dx t).pow 2).add ((dy t).pow 2)).deriv
  have d2 : deriv (deriv h) s/2-1=C.k s*(-x s*C.ty s+y s*C.tx s) := by
    rw [funext dh]
    have d := ((((dx s).const_mul 2).mul (C.dtx s)).add (((dy s).const_mul 2).mul (C.dty s))).deriv
    simp only [Pi.add_def, Pi.mul_def] at d
    rw [d]
    linear_combination C.unit s
  change (h s-(deriv h s/2)^2)*(C.k s)^2=(deriv (deriv h) s/2-1)^2
  rw [dh,d2]
  dsimp only [h]
  linear_combination -(C.k s)^2*((x s)^2+(y s)^2)*(C.unit s)

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.height_curvature_identity
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.squared_distance_curvature_identity
