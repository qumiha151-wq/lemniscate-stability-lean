import LengthGrowth.ActualFlow.SharpWirtinger
import LengthGrowth.ActualFlow.MacroscopicTangentChord

noncomputable section
open MeasureTheory
namespace LengthGrowth.BendingSublevel

/-- A unit spinor whose square has zero mean has centered second moment
at least half the period. All averages use the actual interval measure. -/
theorem spinor_variance {L : ℝ} (hL : 0<L) {S : ℝ → ℂ} (cs : Continuous S)
    (unit : ∀s, ‖S s‖=1) (square : (∫ s in 0..L,S s^2)=0) :
    let m := (∫ s in 0..L,S s)/(L:ℂ)
    L≤2*(∫ s in 0..L, ‖S s-m‖^2) := by
  let m := (∫ s in 0..L,S s)/(L:ℂ)
  let h := fun s => S s-m
  have ch : Continuous h := cs.sub continuous_const
  have lm : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
  have avg : (∫ s in 0..L,h s)=0 := by
    dsimp only [h]
    rw [intervalIntegral.integral_sub (cs.intervalIntegrable 0 L)
      (continuous_const.intervalIntegrable 0 L),intervalIntegral.integral_const]
    simp only [sub_zero,Complex.real_smul,m]
    field_simp
    ring
  have ih : (∫ s in 0..L,inner ℝ m (h s))=0 := by
    change (∫ s in 0..L,(innerSL ℝ m) (h s))=0
    rw [ContinuousLinearMap.intervalIntegral_comp_comm _ (ch.intervalIntegrable ..),avg,map_zero]
  have sum (s : ℝ) : m+h s=S s := by dsimp [h]; ring
  have npoint (s : ℝ) : (1:ℝ)=‖m‖^2+2*inner ℝ m (h s)+‖h s‖^2 := by
    rw [←norm_add_sq_real,sum,unit]; norm_num
  have nint := congrArg (fun f : ℝ → ℝ => ∫ s in 0..L, f s) (funext npoint)
  change (∫ _ in 0..L,(1:ℝ))=∫ s in 0..L,‖m‖^2+2*inner ℝ m (h s)+‖h s‖^2 at nint
  have ci : Continuous (fun s => inner ℝ m (h s)) := continuous_const.inner ch
  rw [intervalIntegral.integral_add (f:=fun s => ‖m‖^2+2*inner ℝ m (h s))
    (g:=fun s => ‖h s‖^2) ((continuous_const.add (ci.const_mul 2)).intervalIntegrable ..)
    ((ch.norm.pow 2).intervalIntegrable ..),intervalIntegral.integral_add
    (f:=fun _ : ℝ => ‖m‖^2) (g:=fun s => 2*inner ℝ m (h s)) (continuous_const.intervalIntegrable ..)
    ((ci.const_mul 2).intervalIntegrable ..),intervalIntegral.integral_const_mul,ih] at nint
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one,mul_zero,add_zero] at nint
  have ppoint (s : ℝ) : S s^2=m^2+(2*m)*h s+(h s)^2 := by rw [←sum s]; ring
  have pint := congrArg (fun f : ℝ → ℂ => ∫ s in 0..L,f s) (funext ppoint)
  change (∫ s in 0..L,S s^2)=∫ s in 0..L,m^2+(2*m)*h s+(h s)^2 at pint
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) ..)
    [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,avg,square,Complex.real_smul] at pint
  have eq : (∫ s in 0..L,(h s)^2)= -((L:ℂ)*m^2) := by linear_combination -pint
  have triangle := intervalIntegral.norm_integral_le_integral_norm (μ:=volume) (f:=fun s => (h s)^2) hL.le
  rw [eq,norm_neg,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL] at triangle
  simp only [norm_pow] at triangle
  change L≤2*(∫ s in 0..L,‖h s‖^2)
  linarith only [nint,triangle]

end LengthGrowth.BendingSublevel
#print axioms LengthGrowth.BendingSublevel.spinor_variance
