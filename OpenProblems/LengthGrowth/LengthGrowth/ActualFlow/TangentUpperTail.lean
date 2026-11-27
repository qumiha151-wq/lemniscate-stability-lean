import LengthGrowth.ActualFlow.TangentFlowRecord
import LengthGrowth.ActualFlow.TangentTail
namespace LengthGrowth.ActualFlow.ForwardImmersion
noncomputable section
open Set MeasureTheory Real TangentSpectrum
variable (c : ForwardImmersion)

theorem tangent_second_at_every_time {t : ℝ} (ht : 0≤t) :
    let T:=(c.regularPositionAt ht).closedFrenetCurve.unitT
    HasSum (fun n=>|omega n|^2*TangentSpectrum.energy T n) (2*c.normalizedProduct t) := by
  let p:=c.regularPositionAt ht
  let a:=p.closedFrenetCurve
  let L:=c.length t
  let E:=c.energy t
  have lp : 0<L:=c.length_pos ht
  have m2:=p.scaledArclengthCurvature_moment lp (by norm_num : (0:ℝ)<1)
    (show L*1=p.length by rw [mul_one];rfl) 2 0
  simp only [pow_zero,mul_one,div_one] at m2
  change (∫u in 0..1,a.unitK u^2)=L^2/L*(∫s in 0..p.period,curvature p.position s^2*speed p.position s) at m2
  have en : (∫s in 0..p.period,curvature p.position s^2*speed p.position s)=2*E := by
    change _=2*(1/2*(∫s in 0..p.period,curvature p.position s^2*speed p.position s));ring
  have value : (∫u in 0..1,a.unitK u^2)=2*c.normalizedProduct t := by
    change _=2*(E*L);rw [m2,en];field_simp [lp.ne']
  have cv : Continuous a.unitV := continuous_iff_continuousAt.mpr fun u=>(a.unitV_der u).continuousAt
  have pt : a.unitT 1=a.unitT 0 := by simp [ClosedFrenetCurve.unitT,a.tangent_periodic.eq]
  have vn (u : ℝ) : ‖a.unitV u‖^2=a.unitK u^2 := by
    simp only [ClosedFrenetCurve.unitV,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,ClosedFrenetCurve.unitT,a.tangent_unit,sq_abs]
  have hp := parseval a.unitV cv
  change HasSum (fun n => TangentSpectrum.energy a.unitV n) _ at hp
  simpa only [energy_der a.unitT_der cv pt,vn,value] using hp

theorem one_tail_upper {t W : ℝ} (ht : 0≤t) (hw : 1≤W) (pos : Bool) :
    tail W pos (c.regularPositionAt ht).closedFrenetCurve.unitT≤2*c.normalizedProduct t/W := by
  let T:=(c.regularPositionAt ht).closedFrenetCurve.unitT
  let b:=TangentSpectrum.energy T
  have wp : 0<W := by linarith only [hw]
  have sm:=c.tangent_second_at_every_time ht
  have major := sm.div_const W
  have nn (n : ℤ) : 0≤halfEnergy pos T n := by
    unfold halfEnergy cut;split <;> first | exact sq_nonneg _ | exact le_rfl
  have le (n : ℤ) : halfEnergy pos T n≤b n := by
    unfold halfEnergy cut;split <;> first | exact sq_nonneg _ | exact le_rfl
  have posd (n : ℤ) : 0≤tailDensity W pos T n := by
    unfold tailDensity;split <;> first | exact mul_nonneg (sqrt_nonneg _) (nn n) | exact le_rfl
  have cmp (n : ℤ) : tailDensity W pos T n≤(|omega n|^2*b n)/W := by
    unfold tailDensity;split
    next hz =>
      let w:=|omega n|
      have w1 : 1≤w := hw.trans hz.le
      have sr : √w≤w := by
        apply (sq_le_sq₀ (sqrt_nonneg _) (abs_nonneg _)).mp
        rw [Real.sq_sqrt (abs_nonneg _)]
        nlinarith only [mul_nonneg (sub_nonneg.mpr w1) (abs_nonneg (omega n))] 
      have factor : Real.sqrt w*W≤w^2 := (mul_le_mul sr hz.le wp.le (abs_nonneg _)).trans_eq (by ring)
      apply (le_div_iff₀ wp).mpr
      calc
        _ = (Real.sqrt w*W)*halfEnergy pos T n := by ring
        _ ≤ w^2*halfEnergy pos T n := mul_le_mul_of_nonneg_right factor (nn n)
        _ ≤ _ := mul_le_mul_of_nonneg_left (le n) (sq_nonneg _)
    next => exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) wp.le
  have sum:=Summable.of_nonneg_of_le posd cmp major.summable
  exact hasSum_le cmp sum.hasSum major

end
end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.one_tail_upper
