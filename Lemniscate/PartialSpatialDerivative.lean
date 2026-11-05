import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-! Spatial derivatives remain smooth up to a closed time boundary.
Only the spatial variable is differentiated in the resulting slices. -/
noncomputable section
namespace Lemniscate
open Set
open scoped ContDiff

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def spatialDerivativeWithin (U : Set P) (O : Set E) (f : P × E → F)
    (z : P × E) : E →L[ℝ] F :=
  (fderivWithin ℝ f (U ×ˢ O) z).comp (ContinuousLinearMap.inr ℝ P E)

/-- On a product with an open spatial domain, the spatial part of the
within derivative is the genuine derivative of each spatial slice.
Its smoothness includes parameters on a boundary such as initial time. -/
theorem spatial_derivative_within_smooth
    (U : Set P) (O : Set E) (hU : UniqueDiffOn ℝ U) (hO : IsOpen O)
    (f : P × E → F) (hf : ContDiffOn ℝ ∞ f (U ×ˢ O)) :
    ContDiffOn ℝ ∞ (spatialDerivativeWithin U O f) (U ×ˢ O) ∧
      ∀ p ∈ U, ∀ x ∈ O, HasFDerivAt (fun y : E => f (p,y))
        (spatialDerivativeWithin U O f (p,x)) x := by
  have hs : UniqueDiffOn ℝ (U ×ˢ O) := hU.prod hO.uniqueDiffOn
  have hd := (contDiffOn_infty_iff_fderivWithin hs).mp hf
  constructor
  · exact hd.2.clm_comp contDiffOn_const
  · intro p hp x hx
    have hfd := (hd.1 (p,x) ⟨hp,hx⟩).hasFDerivWithinAt
    have hslice := hfd.comp x
      (hasFDerivAt_prodMk_right p x).hasFDerivWithinAt
      (fun y hy => (show (p,y) ∈ U ×ˢ O from ⟨hp,hy⟩))
    exact hslice.hasFDerivAt (hO.mem_nhds hx)

end Lemniscate
