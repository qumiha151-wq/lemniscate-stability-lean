import LengthGrowth.ActualFlow.DefectQuantitative

noncomputable section
open MeasureTheory
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

theorem normalized_positive_turn_quadratic (len : c.period=2*Real.pi)
    (turn : (∫ s in 0..c.period,c.curvature s)=c.period)
    (above : 4*Real.pi^2<2*c.energy*c.period) (cap : 2*c.energy*c.period≤4*Real.pi^2+36) :
    ((2*c.energy-c.period)^2)/1000000 ≤
      c.period*c.dissipation-c.energy*(∫ s in 0..c.period,c.curvature s*c.force s) := by
  let P := c.period
  let B := 2*c.energy
  let J := ∫ s in 0..P,c.curvature s*c.force s
  let e := P*c.dissipation-c.energy*J
  let σ := Real.sqrt (B/P)
  let b := c.energy/(2*P)
  let u := fun s => c.curvature s-1
  let V := ∫ s in 0..P,u s^2
  let d := B*P-4*Real.pi^2
  let C := ∫ s in 0..P,c.curvature s^3
  let I₃ := ∫ s in 0..P,u s^3
  let I₄ := ∫ s in 0..P,u s^4
  have pp : 0<P := c.period_pos
  have ep : 0<c.energy := c.energy_pos
  have bp : 0<B := by dsimp only [B]; positivity
  have sp : 0<σ := Real.sqrt_pos_of_pos (div_pos bp pp)
  have bpos : 0≤b := by dsimp [b]; positivity
  have e0 : 0≤e := (sub_pos.mpr (c.bending_sublevel_strict above cap)).le
  have eb : 2*b*P=c.energy := by dsimp [b]; field_simp
  have scale : P*σ^2=B := by
    dsimp only [σ]; rw [Real.sq_sqrt (div_nonneg bp.le pp.le)]; field_simp
  have p2 : P^2=4*Real.pi^2 := by change c.period^2=_; rw [len]; ring
  have mc : (∫ s in 0..c.period,c.curvature s)=P*1 := by simpa only [mul_one] using turn
  obtain ⟨avg,m2,m3,m4⟩ := BendingSublevel.centered_moments c.curvature_continuous mc
  change (∫ s in 0..P,u s)=0 at avg
  change (∫ s in 0..P,c.curvature s^2)=P*1^2+V at m2
  change C=P*1^3+3*1*V+I₃ at m3
  change (∫ s in 0..P,c.curvature s^4)=P*1^4+6*1^2*V+4*1*I₃+I₄ at m4
  norm_num at m2 m3 m4
  have mass : B=P+V := by change 2*((∫ s in 0..P,c.curvature s^2)/2)=_; linarith only [m2]
  have v0 : 0≤V := intervalIntegral.integral_nonneg_of_forall pp.le (fun s => sq_nonneg (u s))
  have variance : V=P*(σ^2-1) := by linarith only [scale,mass]
  have s1 : 1≤σ := by
    by_contra! bad
    have ss : σ^2<1 := by nlinarith only [mul_pos (sub_pos.mpr bad) (show 0<σ+1 by linarith)]
    linarith only [variance,v0,mul_lt_mul_of_pos_left ss pp]
  have ratio : 4*Real.pi^2*(σ^2-1)=d := by dsimp only [d]; rw [←p2,←scale]; ring
  have dV : 2*Real.pi*V=d*1 := by
    change 2*Real.pi*V=(B*P-4*Real.pi^2)*1
    rw [←p2,mass,←len]; change P*V=((P+V)*P-P^2)*1; ring
  have dc : d≤36 := by change 2*c.energy*c.period-4*Real.pi^2≤36; linarith
  obtain ⟨coef,vc⟩ := BendingSublevel.sublevel_constants dc s1 (by norm_num : (0:ℝ)<1) ratio dV
  simp only [mul_one] at vc
  have bc : 2≤B := by
    have pp2 : 2≤P := by change 2≤c.period; rw [len]; linarith [Real.pi_gt_three]
    linarith only [mass,v0,pp2]
  have g := BendingSublevel.curvature_fourth_moment c 1 avg
  change 3*I₄^2≤V^3*c.curvatureGradientSquare at g
  have g0 := c.curvature_gradient_nonneg
  have src := c.growthResidual_square
  change (∫ s in 0..P,c.growthResidual s^2)= c.dissipation-2*b*J+b^2*B at src
  have cs := interval_integral_mul_sq_le (f:=fun _ : ℝ => (1:ℝ)) continuous_const
    c.growthResidual_continuous pp.le
  have sc : (∫ s in 0..P,c.growthResidual s)^2 ≤ P*(∫ s in 0..P,c.growthResidual s^2) := by
    simpa using cs
  have meanResidual : (∫ s in 0..P,c.growthResidual s)=C/2-b*P := by
    unfold growthResidual
    rw [intervalIntegral.integral_sub (c.force_continuous.intervalIntegrable ..)
      ((c.curvature_continuous.const_mul _).intervalIntegrable ..),
      intervalIntegral.integral_const_mul,turn,c.bending_force_mean]
  rw [meanResidual,src] at sc
  have rhs : P*(c.dissipation-2*b*J+b^2*B)=e+(b*P*σ)^2 := by
    dsimp only [e]; rw [←scale,←eb]; ring
  rw [rhs] at sc
  have rt := Real.sqrt_nonneg e
  have re := Real.sq_sqrt e0
  have cub : 2*(P+3*V+I₃)≤B*(1+σ)+4*Real.sqrt e := by
    have up : C/2-b*P≤Real.sqrt e+b*P*σ := by
      apply le_of_sq_le_sq _ (by positivity)
      nlinarith only [sc,re,mul_nonneg rt (show 0≤b*P*σ by positivity)]
    rw [←m3]
    change 2*C≤(2*c.energy)*(1+σ)+4*Real.sqrt e
    rw [←eb]; linarith only [up]
  have virial := c.sharp_virial
  change 4*Real.pi^2*c.energy^2≤c.dissipation*P^3 at virial
  rw [←p2] at virial
  have vir : c.energy^2≤P*c.dissipation := by
    apply le_of_mul_le_mul_left (a:=P^2) _ (sq_pos_of_pos pp)
    linarith only [virial]
  have jlow : B-4*e/B≤2*J := by
    apply sub_le_iff_le_add.mpr
    apply le_of_mul_le_mul_right (a:=B) _ bp
    rw [add_mul,div_mul_cancel₀ _ bp.ne']
    dsimp only [B,e]; linarith only [vir]
  have jexact := c.curvature_gradient_identity
  change c.curvatureGradientSquare=(∫ s in 0..P,c.curvature s^4)/2-J at jexact
  rw [m4] at jexact
  have rate := BendingSublevel.quadratic_rate e0 g0 v0 s1 mass variance bc vc coef cub
    (by linarith only [jlow,jexact]) g
  change (B-P)^2/1000000≤e
  rwa [show B-P=V by linarith only [mass]]

end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.normalized_positive_turn_quadratic
