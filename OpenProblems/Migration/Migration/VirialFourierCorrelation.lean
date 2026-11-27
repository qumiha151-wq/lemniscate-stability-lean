import Migration.LowDefectSecondHarmonic
import Migration.LowDefectMaterialCorrection

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.LowDefect.Correlation

def mean : C(ℝ,ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫x in (0:ℝ)..1,f x
  map_add' f g := intervalIntegral.integral_add (f.continuous.intervalIntegrable ..)
    (g.continuous.intervalIntegrable ..)
  map_smul' a f := by
    change (∫x in (0:ℝ)..1,a • f x)=_
    rw [intervalIntegral.integral_smul];rfl

def cn (a : ℂ) : C(ℝ,ℂ) := ContinuousMap.const ℝ a
theorem mean_const (a : ℂ) : mean (cn a)=a := by simp [mean,cn]
theorem mean_cn (a : ℂ) (f : C(ℝ,ℂ)) : mean (cn a*f)=a*mean f := by
  change mean (a • f)=a*mean f
  rw [map_smul,smul_eq_mul]
theorem mean_star (f : C(ℝ,ℂ)) : mean (star f)=conj (mean f) :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm (μ:=volume)
    (a:=0) (b:=1) (f.continuous.intervalIntegrable ..)

def mass (f : C(ℝ,ℂ)) := ∫x in (0:ℝ)..1,‖f x‖^2
theorem mass_re (f : C(ℝ,ℂ)) : mass f=(mean (f*star f)).re := by
  have cf := f.continuous.mul (Complex.continuous_conj.comp f.continuous)
  have q := Complex.reCLM.intervalIntegral_comp_comm (a:=0) (b:=1) (μ:=volume) (cf.intervalIntegrable ..)
  change (∫x in (0:ℝ)..1,(f x*conj (f x)).re)=(mean (f*star f)).re at q
  simpa only [mass,Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_re,←Complex.ofReal_pow] using q

private theorem unit_product (e : C(ℝ,ℂ)) (unit : ∀x,‖e x‖=1) : e*star e=1 := by
  ext x
  change e x*conj (e x)=1
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,unit];norm_num

theorem residual_mass (f e : C(ℝ,ℂ)) (unit : ∀x,‖e x‖=1) :
    mass (f-cn (mean (star e*f))*e)=mass f-‖mean (star e*f)‖^2 := by
  let A:=mean (star e*f)
  let v:=f-cn A*e
  have ee:=unit_product e unit
  have rev : mean (e*star f)=conj A := by simpa [A,mul_comm] using mean_star (star e*f)
  have prod : v*star v=f*star f-cn (conj A)*(star e*f)-cn A*(e*star f)+cn (A*conj A) := by
    dsimp only [v]
    rw [star_sub,star_mul',show star (cn A)=cn (conj A) from rfl,
      show cn (A*conj A)=cn A*cn (conj A) from rfl]
    linear_combination (cn A*cn (conj A))*ee
  change mass v=mass f-‖A‖^2
  rw [mass_re,mass_re,prod,map_add,map_sub,map_sub,mean_cn,mean_cn,mean_const,rev]
  change (mean (f*star f)-conj A*A-A*conj A+A*conj A).re=(mean (f*star f)).re-‖A‖^2
  rw [show conj A*A=A*conj A from mul_comm ..,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  simp [-Complex.ofReal_pow]

/-- Orthogonality cancels both first-order terms in the cubic position/tangent correlation. -/
theorem cubic_bound (G T e : C(ℝ,ℂ)) (eu : ∀x,‖e x‖=1) (tu : ∀x,‖T x‖=1)
    (e0 : mean e=0) (t0 : mean T=0) (gm : mass G≤1)
    (phase : mean (star e*G) = -Complex.I*mean (star e*T)) :
    ‖mean (star G*T^2)‖ ≤ 3*(1-‖mean (star e*T)‖^2)+‖mean ((star e)^2*G)‖ := by
  let A:=mean (star e*T)
  let B:=mean (star e*G)
  let t:=cn A*e
  let g:=cn B*e
  let v:=T-t
  let w:=G-g
  let W:=1-‖A‖^2
  have ee:=unit_product e eu
  have tm : mass T=1 := by simp [mass,tu]
  have vm : mass v=W := by simpa only [v,t,A,W,tm] using residual_mass T e eu
  have Bn : ‖B‖=‖A‖ := by simp [B,A,phase]
  have wm : mass w≤W := by
    change mass (G-cn B*e)≤_
    rw [show B=mean (star e*G) from rfl,residual_mass G e eu]
    change mass G-‖B‖^2≤1-‖A‖^2
    rw [Bn];linarith
  have masspos : 0≤mass v := intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun x=>sq_nonneg _)
  have an : ‖A‖≤1 := by dsimp only [W] at vm;nlinarith only [masspos,vm,norm_nonneg A]
  have vu : mean v=0 := by change mean (T-cn A*e)=_;rw [map_sub,mean_cn,e0,t0];ring
  have gr : star g=cn (conj B)*star e := by dsimp only [g];rw [star_mul'];rfl
  have gt : star g*t=cn (conj B*A) := by
    rw [gr, show cn (conj B*A)=cn (conj B)*cn A from rfl]
    dsimp only [t]
    linear_combination (cn (conj B)*cn A)*ee
  have e2 : mean (star G*e^2)=conj (mean ((star e)^2*G)) := by
    rw [←mean_star,star_mul,star_pow,star_star]
  have exact0 : mean (star G*T^2)=
      mean (star g*v^2)+(A^2)*conj (mean ((star e)^2*G))+mean (star w*(T^2-t^2)) := by
    have alg : star G*T^2=star g*v^2+cn (A^2)*(star G*e^2)+star w*(T^2-t^2)+
        cn (2*(conj B*A))*v := by
      have h : cn (2*(conj B*A))*v=2*(star g*t)*v := by rw [gt];rfl
      rw [h]
      dsimp only [w,v,t]
      rw [star_sub,show cn (A^2)=cn A^2 from rfl];ring
    rw [alg,map_add,map_add,map_add,mean_cn,mean_cn,e2,vu];ring
  have tnorm (x : ℝ) : ‖t x‖≤1 := by change ‖A*e x‖≤1;simpa only [norm_mul,eu,mul_one] using an
  have gnorm (x : ℝ) : ‖g x‖≤1 := by change ‖B*e x‖≤1;simpa only [norm_mul,eu,mul_one,Bn] using an
  have norm_mean (f : C(ℝ,ℂ)) := intervalIntegral.norm_integral_le_integral_norm
    (μ:=volume) (f:=fun x : ℝ=>f x) (by norm_num : (0:ℝ)≤1)
  have V : ‖mean (star g*v^2)‖≤W := by
    rw [←vm]
    apply (norm_mean _).trans
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((star g*v^2).continuous.norm.intervalIntegrable ..) ((v.continuous.norm.pow 2).intervalIntegrable ..)
    intro x _
    change ‖conj (g x)*(v x)^2‖≤‖v x‖^2
    simpa only [norm_mul,norm_pow,Complex.norm_conj,one_mul] using mul_le_mul_of_nonneg_right (gnorm x) (sq_nonneg ‖v x‖)
  have R : ‖mean (star w*(T^2-t^2))‖≤2*W := by
    apply (norm_mean _).trans
    have intb : (∫x in (0:ℝ)..1,‖(star w*(T^2-t^2)) x‖)≤mass w+mass v := by
      unfold mass
      rw [←intervalIntegral.integral_add (f:=fun x=>‖w x‖^2) (g:=fun x=>‖v x‖^2)
        ((w.continuous.norm.pow 2).intervalIntegrable ..) ((v.continuous.norm.pow 2).intervalIntegrable ..)]
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((star w*(T^2-t^2)).continuous.norm.intervalIntegrable ..)
        (((w.continuous.norm.pow 2).add (v.continuous.norm.pow 2)).intervalIntegrable ..)
      intro x _
      have fact : T x^2-t x^2=v x*(T x+t x) := by change _=(T x-t x)*_;ring
      have sum := (norm_add_le (T x) (t x)).trans (by linarith [tu x,tnorm x] : ‖T x‖+‖t x‖≤2)
      change ‖conj (w x)*(T x^2-t x^2)‖≤_
      rw [fact,norm_mul,norm_mul,Complex.norm_conj]
      change ‖w x‖*(‖v x‖*‖T x+t x‖)≤‖w x‖^2+‖v x‖^2
      nlinarith only [sq_nonneg (‖w x‖-‖v x‖),mul_le_mul_of_nonneg_left sum (mul_nonneg (norm_nonneg (w x)) (norm_nonneg (v x)))]
    linarith only [intb,wm,vm]
  have C := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg A) an 2) (norm_nonneg (mean ((star e)^2*G)))
  rw [exact0]
  apply (norm_add_le _ _).trans
  have pair:=norm_add_le (mean (star g*v^2)) (A^2*conj (mean ((star e)^2*G)))
  rw [norm_mul,norm_pow,Complex.norm_conj] at pair
  change _≤3*W+_
  nlinarith only [V,R,C,pair]

end MigrationGeometry.Flow.LowDefect.Correlation
#print axioms MigrationGeometry.Flow.LowDefect.Correlation.cubic_bound

