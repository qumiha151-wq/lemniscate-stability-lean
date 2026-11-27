import SolitonClassification.ForceWindingPhase
import SolitonClassification.SupportODE
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

noncomputable section
open Function
namespace ClosedSimilarity.ForceWinding

def liftedPoint (θ F H:ℝ→ℝ) (s:ℝ) : ℂ :=
  (‖rect (F s) (H s)‖:ℂ)*(Circle.exp (θ s+(rect (F s) (H s)).arg):ℂ)

theorem liftedPoint_eq (θ F H:ℝ→ℝ) (s:ℝ) :
    liftedPoint θ F H s = rect (F s) (H s)*(Circle.exp (θ s):ℂ) := by
  let z := rect (F s) (H s)
  have pol : (‖z‖:ℂ)*(Circle.exp z.arg:ℂ)=z := by
    rw [Circle.coe_exp];exact Complex.norm_mul_exp_arg_mul_I z
  change (‖z‖:ℂ)*(Circle.exp (θ s+z.arg):ℂ)=z*(Circle.exp (θ s):ℂ)
  rw [Circle.exp_add]
  change (‖z‖:ℂ)*((Circle.exp (θ s):ℂ)*(Circle.exp z.arg:ℂ))=_
  calc
    _ = ((‖z‖:ℂ)*(Circle.exp z.arg:ℂ))*(Circle.exp (θ s):ℂ) := by ring
    _ = _ := by rw [pol]

/-- The lifted complex point differs from the actual reconstructed plane
position by the fixed nonzero rotation-dilation -b+i*a. -/
theorem liftedPoint_physical (a b:ℝ) (p q θ:ℝ→ℝ) (s:ℝ) :
    liftedPoint θ (fun t=> -a*p t-b*q t) (fun t=>a*q t-b*p t) s =
    rect (-b) a * rect (profileX p q θ s) (profileY p q θ s) := by
  rw [liftedPoint_eq,Circle.coe_exp,Complex.exp_mul_I]
  apply Complex.ext <;>
    simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.I_re,Complex.I_im,rect_re,rect_im,Complex.cos_ofReal_re,
      Complex.cos_ofReal_im,Complex.sin_ofReal_re,Complex.sin_ofReal_im,profileX,profileY] <;> ring

theorem duplicate_phase {a b:ℝ} {θ F H:ℝ→ℝ} {s t:ℝ}
    (nc : F t≠0 ∨ H t≠0) (eq:liftedPoint θ F H s=liftedPoint θ F H t) :
    supportMass F H s=supportMass F H t ∧ ∃j:ℤ,
      spiralAngle a b θ F H t=spiralAngle a b θ F H s+j*(2*Real.pi) := by
  let z := fun u=>rect (F u) (H u)
  have e : (‖z s‖:ℂ)*(Circle.exp (θ s+(z s).arg):ℂ)=(‖z t‖:ℂ)*(Circle.exp (θ t+(z t).arg):ℂ) := eq
  have n : ‖z s‖=‖z t‖ := by simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),Circle.norm_coe,mul_one] using congrArg norm e
  have nz : z t≠0 := by
    intro zero
    rcases nc with x|x
    · exact x (by simpa [z] using congrArg Complex.re zero)
    · exact x (by simpa [z] using congrArg Complex.im zero)
  have np : (‖z t‖:ℂ)≠0 := by exact_mod_cast norm_ne_zero_iff.mpr nz
  rw [n] at e
  have ce : Circle.exp (θ t+(z t).arg)=Circle.exp (θ s+(z s).arg) := Subtype.ext (mul_left_cancel₀ np e).symm
  obtain ⟨j,hj⟩ := Circle.exp_eq_exp.mp ce
  have mass (u:ℝ) : supportMass F H u=‖z u‖^2 := by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply];simp only [z,rect_re,rect_im,supportMass];ring
  have em := (mass s).trans ((congrArg (fun x:ℝ=>x^2) n).trans (mass t).symm)
  refine ⟨em,j,?_⟩
  change θ t+(z t).arg-_ = θ s+(z s).arg-_+_
  rw [hj,em]
  ring

end ClosedSimilarity.ForceWinding
#print axioms ClosedSimilarity.ForceWinding.duplicate_phase
