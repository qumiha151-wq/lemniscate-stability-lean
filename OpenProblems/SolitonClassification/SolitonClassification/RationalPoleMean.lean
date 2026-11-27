import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section
open Function MeasureTheory ComplexConjugate
open scoped ComplexConjugate
namespace ClosedSimilarity.RationalArclength

def unitPhase (s : ℝ) := Complex.exp ((s:ℂ)*Complex.I)

theorem unitPhase_add (x y : ℝ) : unitPhase (x+y) = unitPhase x*unitPhase y := by
  unfold unitPhase
  rw [Complex.ofReal_add,add_mul,Complex.exp_add]

theorem unitPhase_norm (s : ℝ) : ‖unitPhase s‖=1 := by simp [unitPhase,Complex.norm_exp]

theorem unitPhase_ne (s : ℝ) : unitPhase s ≠ 0 := Complex.exp_ne_zero _

theorem unitPhase_neg (s : ℝ) : unitPhase (-s)=conj (unitPhase s) := by
  simp [unitPhase,←Complex.exp_conj]

theorem unitPhase_periodic : Periodic unitPhase (2*Real.pi) := by
  intro s
  rw [unitPhase_add]
  simp [unitPhase,Complex.exp_two_pi_mul_I]

theorem odd_period_integral {f : ℝ→ℝ} (per : Periodic f (2*Real.pi)) (odd : ∀s,f (-s)= -f s) :
    (∫ s in (0:ℝ)..2*Real.pi,f s) = 0 := by
  have sym : (fun s => f (2*Real.pi-s)) = (fun s => -f s) := by
    funext s; rw [show 2*Real.pi-s= -s+2*Real.pi by ring,per,odd]
  have z := intervalIntegral.integral_comp_sub_left (f:=f) (a:=(0:ℝ)) (b:=2*Real.pi) (2*Real.pi)
  rw [sym,intervalIntegral.integral_neg,sub_self,sub_zero] at z
  linarith

/-- A single pole contributes zero mean imaginary part to the full angular average.
The statement is used only for poles outside the real profile's unit circle. -/
theorem pole_imaginary_average (α : ℂ) :
    (∫ s in (0:ℝ)..2*Real.pi,(α/(unitPhase s-α)).im)=0 := by
  let f := fun s : ℝ => (α/(unitPhase s-α)).im
  let g := fun s : ℝ => ((‖α‖:ℂ)/(unitPhase s-(‖α‖:ℂ))).im
  have gf : Periodic g (2*Real.pi) := fun s => by dsimp [g];rw [unitPhase_periodic s]
  have ff : Periodic f (2*Real.pi) := fun s => by dsimp [f];rw [unitPhase_periodic s]
  have odd : ∀s,g (-s)= -g s := by
    intro s
    change ((‖α‖:ℂ)/(unitPhase (-s)-(‖α‖:ℂ))).im = _
    rw [unitPhase_neg]
    have eq : (‖α‖:ℂ)/(conj (unitPhase s)-(‖α‖:ℂ)) =
        conj ((‖α‖:ℂ)/(unitPhase s-(‖α‖:ℂ))) := by simp
    rw [eq];rfl
  have shift (s : ℝ) : f (s+Complex.arg α) = g s := by
    have polar : (‖α‖:ℂ)*unitPhase (Complex.arg α) = α := Complex.norm_mul_exp_arg_mul_I α
    change (α/(unitPhase (s+Complex.arg α)-α)).im = _
    rw [unitPhase_add]
    calc
      _ = ((↑‖α‖*unitPhase α.arg)/(unitPhase s*unitPhase α.arg-↑‖α‖*unitPhase α.arg)).im :=
        congrArg (fun z : ℂ => (z/(unitPhase s*unitPhase α.arg-z)).im) polar.symm
      _ = _ := by rw [←sub_mul, mul_div_mul_right _ _ (unitPhase_ne (Complex.arg α))]
  have hz := odd_period_integral gf odd
  have op := intervalIntegral.integral_comp_add_right (a:=(0:ℝ)) (b:=2*Real.pi) f (Complex.arg α)
  simp only [shift,zero_add] at op
  rw [hz,add_comm (2*Real.pi),ff.intervalIntegral_add_eq (Complex.arg α) 0,zero_add] at op
  exact op.symm

end ClosedSimilarity.RationalArclength
#print axioms ClosedSimilarity.RationalArclength.pole_imaginary_average

