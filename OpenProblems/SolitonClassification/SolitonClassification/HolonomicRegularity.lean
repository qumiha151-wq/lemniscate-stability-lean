import SolitonClassification.NoClosedTranslators
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open scoped ContDiff
namespace ClosedSimilarity.ClosedUnitFrenetCurve

/-- The finite-regularity Frenet data bootstrap to a smooth curvature from the position law. -/
theorem similarity_curvature_smooth (c : ClosedUnitFrenetCurve) (a b vx vy : ℝ)
    (law : ∀ s, c.positionForce s = -a*c.normalSupport s-b*c.tangentSupport s+vx*c.ty s-vy*c.tx s) :
    ContDiff ℝ ∞ c.k := by
  have acceleration : c.w = fun s => -a*(-c.x s*c.ty s+c.y s*c.tx s) -
      b*(c.x s*c.tx s+c.y s*c.ty s)+vx*c.ty s-vy*c.tx s-(c.k s)^3/2 := by
    funext s
    have h := law s
    rw [c.positionForce_eq] at h
    unfold force normalSupport tangentSupport at h
    linarith only [h]
  have regular (n : ℕ) : ContDiff ℝ n c.x ∧ ContDiff ℝ n c.y ∧
      ContDiff ℝ n c.tx ∧ ContDiff ℝ n c.ty ∧ ContDiff ℝ n c.k ∧ ContDiff ℝ n c.v := by
    induction n with
    | zero =>
      have base {f g : ℝ→ℝ} (h : ∀s, HasDerivAt f (g s) s) : ContDiff ℝ 0 f :=
        contDiff_zero.mpr (continuous_iff_continuousAt.mpr (fun s => (h s).continuousAt))
      exact ⟨base c.dx, base c.dy, base c.dtx, base c.dty, base c.dk, base c.dv⟩
    | succ n ih =>
      obtain ⟨x,y,tx,ty,k,v⟩ := ih
      have lift {f g : ℝ→ℝ} (h : ∀s, HasDerivAt f (g s) s) (regular : ContDiff ℝ n g) :
          ContDiff ℝ (n+1:ℕ) f := by
        rw [Nat.cast_add, Nat.cast_one]
        apply contDiff_succ_iff_deriv.mpr
        refine ⟨fun s => (h s).differentiableAt, by simp, ?_⟩
        rwa [show deriv f=g from funext fun s => (h s).deriv]
      refine ⟨lift c.dx tx, lift c.dy ty, lift c.dtx (k.neg.mul ty),
        lift c.dty (k.mul tx), lift c.dk v, lift c.dv ?_⟩
      rw [acceleration]
      fun_prop
  exact contDiff_infty.mpr (fun n => (regular n).2.2.2.2.1)

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.similarity_curvature_smooth

