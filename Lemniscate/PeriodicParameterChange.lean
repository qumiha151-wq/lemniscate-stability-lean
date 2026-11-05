import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Hom.Set

/-! A smooth orientation-preserving periodic parameter lift has a genuine
smooth inverse. Bounded displacement supplies both limits at infinity;
the intermediate value theorem supplies surjectivity. No diffeomorphism
or inverse smoothness is assumed.  -/
noncomputable section
namespace Lemniscate
open Filter Set
open scoped Topology ContDiff

/-- Construct the order isomorphism of the real line underlying a smooth
orientation-preserving parameter lift, including its smooth inverse and
both deck relations for the given positive period. -/
theorem periodic_parameter_change
    (P : ℝ) (hP : 0 < P) (χ : ℝ → ℝ) (R : ℝ)
    (hχ : ContDiff ℝ ∞ χ)
    (hdeck : ∀ s : ℝ, χ (s+P) = χ s+P)
    (hpositive : ∀ s : ℝ, 0 < deriv χ s)
    (hbound : ∀ s : ℝ, |χ s-s| ≤ R) :
    ∃ e : ℝ ≃o ℝ,
      (∀ s : ℝ, e s = χ s) ∧
      ContDiff ℝ ∞ (e : ℝ → ℝ) ∧ ContDiff ℝ ∞ (e.symm : ℝ → ℝ) ∧
      (∀ s : ℝ, e (s+P) = e s+P) ∧
      ∀ s : ℝ, e.symm (s+P) = e.symm s+P := by
  have hmono : StrictMono χ := strictMono_of_deriv_pos hpositive
  have htop : Tendsto χ atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b+R)] with s hs
    have hl := (abs_le.mp (hbound s)).1
    linarith only [hs,hl]
  have hbot : Tendsto χ atBot atBot := by
    apply tendsto_atBot.2
    intro b
    filter_upwards [eventually_le_atBot (b-R)] with s hs
    have hu := (abs_le.mp (hbound s)).2
    linarith only [hs,hu]
  have hsurj : Function.Surjective χ := hχ.continuous.surjective htop hbot
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective χ hmono hsurj
  have he : ∀ s : ℝ, e s = χ s := fun _ => rfl
  have hsmooth : ContDiff ℝ ∞ (e : ℝ → ℝ) := hχ
  have hderiv : ∀ s : ℝ, HasDerivAt (e.toHomeomorph : ℝ → ℝ) (deriv χ s) s := by
    intro s
    change HasDerivAt χ (deriv χ s) s
    exact (hχ.differentiable (by simp) s).hasDerivAt
  have hinverse : ContDiff ℝ ∞ (e.symm : ℝ → ℝ) :=
    e.toHomeomorph.contDiff_symm_deriv (fun s => (hpositive s).ne') hderiv hsmooth
  have hedeck : ∀ s : ℝ, e (s+P) = e s+P := hdeck
  refine ⟨e,he,hsmooth,hinverse,hedeck,?_⟩
  intro s
  apply e.injective
  calc
    e (e.symm (s+P)) = s+P := e.apply_symm_apply _
    _ = e (e.symm s)+P := congrArg (fun x : ℝ => x+P) (e.apply_symm_apply s).symm
    _ = e (e.symm s+P) := (hedeck (e.symm s)).symm

end Lemniscate
