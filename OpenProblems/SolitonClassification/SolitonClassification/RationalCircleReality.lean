import SolitonClassification.RationalRealOrigin
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.Algebra.Polynomial

noncomputable section
open Polynomial
open scoped Polynomial
namespace ClosedSimilarity.RationalArclength

private theorem complex_polynomial_splits (B : ℂ[X]) : B.Splits := by
  let : IsAlgClosed ℂ := IsAlgClosed.of_exists_root ℂ (fun q _ irreducible => by
    by_contra! nowhere
    have escape := q.tendsto_norm_atTop (degree_pos_of_irreducible irreducible) tendsto_norm_cobounded_atTop
    have inv_limit := Filter.tendsto_inv₀_cobounded.comp ((tendsto_norm_atTop_iff_cobounded).mp escape)
    rw [Metric.cobounded_eq_cocompact (α:=ℂ)] at inv_limit
    have vanishes := (q.differentiable.inv nowhere).apply_eq_of_tendsto_cocompact 0 inv_limit
    exact inv_ne_zero (nowhere 0) vanishes)
  exact IsAlgClosed.splits B

/-- The origin of a bounded rational curvature is real whenever it is real on the
unit circle and its normalized simple-pole residues are real. -/
theorem real_origin_of_unit_circle {A B : ℂ[X]} (bn : B≠0) (b0 : B.eval 0≠0)
    (deg : A.degree≤B.degree) (simple : ∀ α, B.eval α=0 → B.rootMultiplicity α=1)
    (residue : ∀ α, B.eval α=0 → ∃r : ℝ, A.eval α/B.derivative.eval α=(r:ℂ)*α)
    (safe : ∀s, B.eval (unitPhase s)≠0)
    (reality : ∀s, (A.eval (unitPhase s)/B.eval (unitPhase s)).im=0) :
    (A.eval 0/B.eval 0).im=0 :=
  real_origin_of_unit_circle_of_splits bn (complex_polynomial_splits B) b0 deg simple residue safe reality

end ClosedSimilarity.RationalArclength
#print axioms ClosedSimilarity.RationalArclength.real_origin_of_unit_circle

