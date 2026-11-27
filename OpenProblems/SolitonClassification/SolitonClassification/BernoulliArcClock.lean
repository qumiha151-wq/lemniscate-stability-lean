import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Real Set Function Filter MeasureTheory
open scoped Topology Interval
namespace ClosedSimilarity.BernoulliGeometry

def root (u : ℝ) := Real.sqrt (1+Real.cos u^2)
def speed (u : ℝ) := (root u)⁻¹
def arc (u : ℝ) := ∫ x in 0..u,speed x

theorem root_pos (u : ℝ) : 0<root u := by unfold root; positivity
theorem root_sq (u : ℝ) : root u^2=1+Real.cos u^2 :=
  Real.sq_sqrt (by positivity)
theorem speed_pos (u : ℝ) : 0<speed u := inv_pos.mpr (root_pos u)

theorem speed_continuous : Continuous speed := by
  unfold speed root
  exact (Real.continuous_sqrt.comp (continuous_const.add (Real.continuous_cos.pow 2))).inv₀
    (fun u=>(root_pos u).ne')

theorem arc_deriv (u : ℝ) : HasDerivAt arc (speed u) u :=
  intervalIntegral.integral_hasDerivAt_right (speed_continuous.intervalIntegrable _ _)
    (speed_continuous.stronglyMeasurableAtFilter _ _) speed_continuous.continuousAt

@[simp] theorem arc_zero : arc 0=0 := by simp [arc]

theorem arc_strictMono : StrictMono arc := strictMono_of_deriv_pos
  (fun u=>by rw [(arc_deriv u).deriv];exact speed_pos u)

private theorem speed_lower (u : ℝ) : (1:ℝ)/2≤speed u := by
  have rt := root_pos u
  have sq := root_sq u
  have cs := Real.sin_sq_add_cos_sq u
  have ub : root u≤2 := by nlinarith [sq_nonneg (Real.sin u)]
  change 1/2≤(root u)⁻¹
  rw [←one_div,le_div_iff₀ rt]
  linarith

theorem arc_surjective : Surjective arc := by
  have diff : Differentiable ℝ arc := fun u=>(arc_deriv u).differentiableAt
  have growth {x y : ℝ} (xy : x≤y) : 1/2*(y-x)≤arc y-arc x :=
    mul_sub_le_image_sub_of_le_deriv diff
      (fun u=>by rw [(arc_deriv u).deriv];exact speed_lower u) xy
  intro x
  let R := 2*|x|+1
  have rp : 0≤R := by dsimp [R];positivity
  have lo := growth (x:= -R) (y:=0) (by linarith)
  have hi := growth (x:=0) (y:=R) rp
  rw [arc_zero] at lo hi
  apply intermediate_value_univ (-R) R diff.continuous
  dsimp only [R] at lo hi
  exact ⟨by linarith [neg_abs_le x],by linarith [le_abs_self x]⟩

/-- Change from geometric arclength to the trigonometric lemniscate angle. -/
def arcIso : ℝ ≃o ℝ := arc_strictMono.orderIsoOfSurjective arc arc_surjective
def angle (s : ℝ) : ℝ := arcIso.symm s

@[simp] theorem arc_angle (s : ℝ) : arc (angle s)=s := arcIso.apply_symm_apply s
@[simp] theorem angle_arc (s : ℝ) : angle (arc s)=s := arcIso.symm_apply_apply s
@[simp] theorem angle_zero : angle 0=0 := by simpa only [arc_zero] using angle_arc 0

theorem angle_deriv (s : ℝ) : HasDerivAt angle (root (angle s)) s := by
  have h := (arc_deriv (angle s)).of_local_left_inverse (g:=angle)
    (arcIso.symm.continuous.continuousAt) (speed_pos _).ne'
    (Eventually.of_forall arc_angle)
  simpa only [speed,inv_inv] using h

theorem arc_period (u : ℝ) : arc (u+2*Real.pi)=arc u+arc (2*Real.pi) := by
  have per : Periodic speed (2*Real.pi) := fun t=>by simp [speed,root]
  simpa only [zero_add,arc] using per.intervalIntegral_add_eq_add 0 u
    (fun x y=>speed_continuous.intervalIntegrable x y)

theorem arc_nat_period (n : ℕ) : arc ((n:ℝ)*(2*Real.pi))=(n:ℝ)*arc (2*Real.pi) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.cast_succ,add_mul,one_mul,arc_period,ih]

end ClosedSimilarity.BernoulliGeometry
