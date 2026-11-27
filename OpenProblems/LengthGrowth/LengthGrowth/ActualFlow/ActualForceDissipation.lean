import LengthGrowth.ActualFlow.ForceDissipationVariation
import LengthGrowth.ActualFlow.ForceRateSpatial
import LengthGrowth.ActualFlow.ForceRateSlope

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- A physical differential inequality for elastic force dissipation on every
smooth closed normal free elastic flow. Its coefficients use only the energy
and force dissipation of the same slice. -/
theorem actual_force_dissipation_rate (flow : c.IsNormalFEF) {t : ℝ} (ht : 0<t) :
    deriv c.dissipation t+c.forceSecondMass t ≤
      (2500000*(c.energy t*c.dissipation t)^(2/3:ℝ)+
        32*c.energy t^(1/4:ℝ)*c.dissipation t^(3/4:ℝ))*c.dissipation t := by
  let x := c.position t
  let p := c.regularPositionAt ht.le
  have sm : ContDiff ℝ ∞ x := p.smooth
  have reg : ∀u,deriv x u≠0 := p.regular
  have per : Function.Periodic x c.period := p.periodic
  have nonempty : (Icc (0:ℝ) c.period).Nonempty := nonempty_Icc.mpr c.period_pos.le
  obtain ⟨i,_,imax⟩ := isCompact_Icc.exists_isMaxOn nonempty (curvature_smooth sm reg).continuous.abs.continuousOn
  obtain ⟨j,_,jmax⟩ := isCompact_Icc.exists_isMaxOn nonempty
    (curvatureGradient_smooth sm reg).continuous.abs.continuousOn
  let M := |curvature x i|
  let S := |curvatureGradient x j|
  have bound := force_rate_spatial (M:=M) (S:=S) c.period_pos.le sm reg per
    (fun u hu => imax hu) (fun u hu => jmax hu)
  have var := (c.interior.force_dissipation_variation (c.interior_isNormalFEF flow) ht).deriv
  have whole : deriv c.dissipation t+c.forceSecondMass t ≤ (36*M^4+8*S^2)*c.dissipation t := by
    change deriv c.interior.dissipation t+_ ≤ _
    rw [var]
    exact bound
  apply whole.trans
  apply mul_le_mul_of_nonneg_right _ (c.dissipation_nonneg t)
  have grad := (c.curvature_gradient_and_fourth_rate_bound ht.le j).1
  have curv := (c.curvature_gradient_and_fourth_rate_bound ht.le i).2
  dsimp only [M,S,x]
  rw [sq_abs,show |curvature (c.position t) i|^4 = (curvature (c.position t) i)^4 by
    simpa using (Even.pow_abs (show Even 4 by decide) (curvature (c.position t) i))]
  linarith only [grad,curv,Real.rpow_nonneg (mul_nonneg (c.energy_nonneg t) (c.dissipation_nonneg t)) (2/3:ℝ)]

theorem small_dissipation_rate (flow : c.IsNormalFEF) {t : ℝ} (ht : 0<t)
    (e : c.energy t≤1) (d : c.dissipation t≤1) :
    deriv c.dissipation t+c.forceSecondMass t ≤ 2500032*c.dissipation t^(5/3:ℝ) := by
  have dn := c.dissipation_nonneg t
  have x := Real.rpow_le_rpow (mul_nonneg (c.energy_nonneg t) dn)
    (show c.energy t*c.dissipation t≤c.dissipation t by nlinarith only [mul_le_mul_of_nonneg_right e dn]) (by norm_num : (0:ℝ)≤2/3)
  have E : c.energy t^(1/4:ℝ)≤1 := Real.rpow_le_one (c.energy_nonneg t) e (by norm_num)
  have D := Real.rpow_le_rpow_of_exponent_ge_of_imp dn d
    (by norm_num : (2/3:ℝ)≤3/4) (by norm_num)
  have m := mul_le_mul E D (Real.rpow_nonneg dn _) zero_le_one
  have pow : c.dissipation t^(2/3:ℝ)*c.dissipation t=c.dissipation t^(5/3:ℝ) := by
    rw [←Real.rpow_add_one (c.force_dissipation_pos ht.le).ne']
    norm_num
  apply (c.actual_force_dissipation_rate flow ht).trans
  rw [←pow]
  nlinarith only [mul_le_mul_of_nonneg_right x dn,mul_le_mul_of_nonneg_right m dn]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.actual_force_dissipation_rate
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.small_dissipation_rate
