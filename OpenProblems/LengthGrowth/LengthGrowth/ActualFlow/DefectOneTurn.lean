import LengthGrowth.ActualFlow.DefectPhysicalMoments

noncomputable section
open MeasureTheory
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- Strict sign on an actual once-turning arclength slice. Only initial
geometric input and the free elastic spatial operator occur in the statement. -/
theorem bending_one_turn_strict
    (turning : (∫ s in 0..c.period,c.curvature s)=2*Real.pi)
    (above : 4*Real.pi^2<2*c.energy*c.period)
    (below : 2*c.energy*c.period≤4*Real.pi^2+36) :
    c.energy*(∫ s in 0..c.period,c.curvature s*c.force s)<c.period*c.dissipation := by
  by_contra! bad
  let L := c.period
  let B := 2*c.energy
  let μ := 2*Real.pi/L
  let R := Real.sqrt (B/L)
  let σ := R/μ
  let d := L*B-4*Real.pi^2
  let u := fun s => c.curvature s-μ
  let V := ∫ s in 0..L,u s^2
  let I₃ := ∫ s in 0..L,u s^3
  let I₄ := ∫ s in 0..L,u s^4
  let J := ∫ s in 0..L,c.curvature s*c.force s
  have lp : 0<L := c.period_pos
  have bp : 0<B := by dsimp [B]; exact mul_pos (by norm_num) c.energy_pos
  have mp : 0<μ := by dsimp [μ]; positivity
  have rp : 0<R := Real.sqrt_pos_of_pos (div_pos bp lp)
  have sp : 0<σ := div_pos rp mp
  have turn : L*μ=2*Real.pi := by dsimp [μ]; field_simp
  have rms : L*R^2=B := by
    dsimp only [R]; rw [Real.sq_sqrt (div_nonneg bp.le lp.le)]; field_simp
  have rs : μ*σ=R := by dsimp [σ]; field_simp
  have energy : B=L*μ^2*σ^2 := by rw [←rms,←rs]; ring
  have mean : (∫ s in 0..c.period,c.curvature s)=L*μ := turning.trans turn.symm
  obtain ⟨avg,m2,m3,m4⟩ := BendingSublevel.centered_moments c.curvature_continuous mean
  change (∫ s in 0..L,u s)=0 at avg
  change (∫ s in 0..L,c.curvature s^2)=L*μ^2+V at m2
  change (∫ s in 0..L,c.curvature s^3)=L*μ^3+3*μ*V+I₃ at m3
  change (∫ s in 0..L,c.curvature s^4)=L*μ^4+6*μ^2*V+4*μ*I₃+I₄ at m4
  have bend : B=L*μ^2+V := by
    change 2*((∫ s in 0..L,c.curvature s^2)/2)=L*μ^2+V
    linarith only [m2]
  have tSq : (L*μ)^2=4*Real.pi^2 := by rw [turn]; ring
  have dV : L*V=d := by
    change L*V=L*B-4*Real.pi^2
    rw [bend,←tSq]; ring
  have dpos : 0<d := by
    change 0<L*B-4*Real.pi^2
    change 4*Real.pi^2<B*L at above
    linarith only [above]
  have dcap : d≤36 := by
    change L*B-4*Real.pi^2≤36
    change B*L≤4*Real.pi^2+36 at below
    linarith only [below]
  have vp : 0<V := pos_of_mul_pos_right (dV.symm ▸ dpos) lp.le
  have variance : V=L*μ^2*(σ^2-1) := by linarith only [energy,bend]
  have ratio : 4*Real.pi^2*(σ^2-1)=d := by rw [←dV,variance,←tSq]; ring
  have mass : 2*Real.pi*V=d*μ := by rw [←dV,←turn]; ring
  have s1 : 1≤σ := by
    have ss : 0<σ^2-1 := pos_of_mul_pos_right (show 0<4*Real.pi^2*(σ^2-1) by rwa [ratio]) (by positivity)
    by_contra! h
    nlinarith only [ss,mul_pos (sub_pos.mpr h) (show 0<σ+1 by linarith)]
  have qp := BendingSublevel.positive_gradient_of_variance c μ avg vp
  have gn := BendingSublevel.curvature_fourth_moment c μ avg
  change 3*I₄^2≤V^3*c.curvatureGradientSquare at gn
  obtain ⟨cub,vir⟩ := c.bending_moment_inputs rp.le mean rms bad
  change 2*(∫ s in 0..L,c.curvature s^3)≤B*(μ+R) at cub
  rw [m3,bend,←rs] at cub
  have cub' : 2*(L*μ^3+3*μ*V+I₃)≤(L*μ^2+V)*μ*(1+σ) := by linarith only [cub]
  change 4*Real.pi^2*B≤2*L^2*J at vir
  rw [←tSq] at vir
  have jlow : μ^2*B≤2*J := by
    apply le_of_mul_le_mul_left (a:=L^2) _ (sq_pos_of_pos lp)
    linarith only [vir]
  have jexact := c.curvature_gradient_identity
  change c.curvatureGradientSquare=(∫ s in 0..L,c.curvature s^4)/2-J at jexact
  rw [m4] at jexact
  rw [bend] at jlow
  exact BendingSublevel.incompatible_nondecreasing_slice dcap mp s1 vp qp ratio mass variance cub'
    (by linarith only [jlow,jexact]) gn

end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.bending_one_turn_strict
