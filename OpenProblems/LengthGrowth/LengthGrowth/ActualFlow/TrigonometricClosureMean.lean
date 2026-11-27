import LengthGrowth.ActualFlow.TrigonometricClosureCos
import Mathlib.Topology.ContinuousMap.Algebra

noncomputable section
open Real Set MeasureTheory
namespace LengthGrowth.Multicover.Outward.TrigonometricClosure

abbrev RFn := C(ℝ,ℝ)
def average (f : ℝ→ℝ) := (∫s in (0:ℝ)..2*Real.pi,f s)/(2*Real.pi)
def J (z : ℝ) := average (fun s=>cos (z*sin s))

private def linearMean : RFn →ₗ[ℝ] ℝ where
  toFun f := average f
  map_add' f g := by
    simp only [average,ContinuousMap.coe_add,Pi.add_apply,intervalIntegral.integral_add
      (f.continuous.intervalIntegrable ..) (g.continuous.intervalIntegrable ..),add_div]
  map_smul' r f := by
    change ((∫s in (0:ℝ)..2*Real.pi,r*f s)/(2*Real.pi))=r*_
    rw [intervalIntegral.integral_const_mul];unfold average;ring

theorem average_mono {f g : ℝ→ℝ} (cf : Continuous f) (cg : Continuous g)
    (h : ∀x∈Icc 0 (2*Real.pi), f x≤g x) : average f≤average g :=
  div_le_div_of_nonneg_right (intervalIntegral.integral_mono_on (by positivity)
    (cf.intervalIntegrable ..) (cg.intervalIntegrable ..) h) (by positivity)

private def S : RFn := ⟨sin,continuous_sin⟩

private theorem powers :
    linearMean 1=1 ∧ linearMean (S^2)=1/2 ∧ linearMean (S^4)=3/8 ∧
    linearMean (S^6)=5/16 ∧ linearMean (S^8)=35/128 := by
  have pos : (2:ℝ)*Real.pi≠0 := by positivity
  have m2 : (∫s in (0:ℝ)..2*Real.pi,sin s^2)=Real.pi := by
    rw [integral_sin_sq];simp [sin_two_pi]
  have m4 := integral_sin_pow (a:=0) (b:=2*Real.pi) 2
  have m6 := integral_sin_pow (a:=0) (b:=2*Real.pi) 4
  have m8 := integral_sin_pow (a:=0) (b:=2*Real.pi) 6
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat,sin_zero,sin_two_pi,zero_pow (by decide : (3:ℕ) ≠ 0),zero_pow (by decide : (5:ℕ) ≠ 0),zero_pow (by decide : (7:ℕ) ≠ 0),
    zero_mul,sub_zero,zero_div,zero_add] at m4 m6 m8
  change ((∫_s in (0:ℝ)..2*Real.pi,(1:ℝ))/(2*Real.pi)=1) ∧
    ((∫s in (0:ℝ)..2*Real.pi,sin s^2)/(2*Real.pi)=1/2) ∧
    ((∫s in (0:ℝ)..2*Real.pi,sin s^4)/(2*Real.pi)=3/8) ∧
    ((∫s in (0:ℝ)..2*Real.pi,sin s^6)/(2*Real.pi)=5/16) ∧
    ((∫s in (0:ℝ)..2*Real.pi,sin s^8)/(2*Real.pi)=35/128)
  rw [m8,m6,m4,m2,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one]
  field_simp [pos,Real.pi_ne_zero];norm_num

theorem J_endpoints : 2/9≤J 2 ∧ J 3≤ -4199/16384 := by
  let lo : RFn := 1-(2:ℝ) • S^2+(2/3:ℝ) • S^4-(4/45:ℝ) • S^6
  let hi : RFn := 1-(9/2:ℝ) • S^2+(27/8:ℝ) • S^4-(81/80:ℝ) • S^6+(729/4480:ℝ) • S^8
  have lower : average lo ≤ J 2 := by
    apply average_mono lo.continuous (continuous_cos.comp (continuous_const.mul continuous_sin))
    intro s _
    change 1-2*(sin s)^2+(2/3)*(sin s)^4-(4/45)*(sin s)^6≤cos (2*sin s)
    linarith only [(cos_bounds (2*sin s)).1]
  have upper : J 3≤average hi := by
    apply average_mono (continuous_cos.comp (continuous_const.mul continuous_sin)) hi.continuous
    intro s _
    change cos (3*sin s)≤1-(9/2)*(sin s)^2+(27/8)*(sin s)^4-(81/80)*(sin s)^6+(729/4480)*(sin s)^8
    linarith only [(cos_bounds (3*sin s)).2]
  obtain ⟨v0,v2,v4,v6,v8⟩ := powers
  change linearMean lo≤_ at lower
  change _≤linearMean hi at upper
  simp only [lo,hi,map_sub,map_add,map_smul,smul_eq_mul,v0,v2,v4,v6,v8] at lower upper
  constructor <;> linarith

end LengthGrowth.Multicover.Outward.TrigonometricClosure
#print axioms LengthGrowth.Multicover.Outward.TrigonometricClosure.J_endpoints
