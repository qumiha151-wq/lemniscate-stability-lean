import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open Set MeasureTheory
namespace ClosedSimilarity.ForceWinding

def rect (x y : ℝ) : ℂ := (x:ℂ)+(y:ℂ)*Complex.I
@[simp] theorem rect_re (x y:ℝ) : (rect x y).re=x := by simp [rect]
@[simp] theorem rect_im (x y:ℝ) : (rect x y).im=y := by simp [rect]

theorem argumentD {x y:ℝ→ℝ} {s u v:ℝ}
    (dx : HasDerivAt x u s) (dy : HasDerivAt y v s)
    (slit : 0<x s ∨ y s≠0) :
    HasDerivAt (fun t=>(rect (x t) (y t)).arg)
      ((x s*v-y s*u)/((x s)^2+(y s)^2)) s := by
  let z := fun t=>rect (x t) (y t)
  have plane : z s ∈ Complex.slitPlane := by simpa [Complex.mem_slitPlane_iff,z] using slit
  have dz : HasDerivAt z (rect u v) s := dx.ofReal_comp.add (dy.ofReal_comp.mul_const Complex.I)
  have dl := (Complex.hasDerivAt_log plane).comp s dz
  have di := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s dl
  change HasDerivAt (fun t=>(z t).log.im) _ s at di
  simp only [Complex.log_im] at di
  apply di.congr_deriv
  change ((z s)⁻¹*rect u v).im=_
  rw [mul_comm,←div_eq_mul_inv,Complex.div_im,Complex.normSq_apply]
  simp only [z,rect_re,rect_im]
  ring

end ClosedSimilarity.ForceWinding
#print axioms ClosedSimilarity.ForceWinding.argumentD
