import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

/-! Variation of constants with an actual fundamental solution and actual
inverse. A bounded inverse is used directly; no exponential replacement is
introduced. This is a generic bridge, not a claim that numerical matrices
already equal the true fundamental solution. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set MeasureTheory
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
set_option backward.isDefEq.respectTransparency false

def variationSolution (P Q : ℝ → E →L[ℝ] E) (g : ℝ → E) (v₀ : E) (t : ℝ) : E :=
  P t (v₀+∫s in (0:ℝ)..t,Q s (g s))

/-- Differentiate the actual fundamental-matrix integral. Only continuity
of Q is needed: no unproved differentiability of matrix inversion is used. -/
theorem variationSolution_hasDerivAt
    {A P Q : ℝ → E →L[ℝ] E} {g : ℝ → E} {v₀ : E} {t : ℝ}
    (hQ : Continuous Q) (hg : Continuous g)
    (hP : HasDerivAt P ((A t).comp (P t)) t)
    (hPQ : (P t).comp (Q t)=ContinuousLinearMap.id ℝ E) :
    HasDerivAt (variationSolution P Q g v₀)
      (A t (variationSolution P Q g v₀ t)+g t) t := by
  have hc : Continuous (fun s => Q s (g s)) := hQ.clm_apply hg
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd := hP.clm_apply (hi.const_add v₀)
  convert! hd using 1
  change A t (P t (v₀+∫s in (0:ℝ)..t,Q s (g s)))+g t=
    ((A t).comp (P t)) (v₀+∫s in (0:ℝ)..t,Q s (g s))+P t (Q t (g t))
  rw [←ContinuousLinearMap.comp_apply (P t) (Q t),hPQ]
  rfl

/-- The variation-of-constants identity follows from the actual ODE and
uniqueness. In particular it is not assumed as a formula for the solution. -/
theorem variation_of_constants
    {A P Q : ℝ → E →L[ℝ] E} {g v : ℝ → E} {T : ℝ} {L : ℝ≥0}
    (hQ : Continuous Q) (hg : Continuous g)
    (hA : ∀t∈Icc 0 T,‖A t‖≤(L:ℝ))
    (hP : ∀t∈Icc 0 T,HasDerivAt P ((A t).comp (P t)) t)
    (hPQ : ∀t∈Icc 0 T,(P t).comp (Q t)=ContinuousLinearMap.id ℝ E)
    (hP0 : P 0=ContinuousLinearMap.id ℝ E)
    (hv : ∀t∈Icc 0 T,HasDerivAt v (A t (v t)+g t) t) :
    ∀t∈Icc 0 T,v t=variationSolution P Q g (v 0) t := by
  let y := variationSolution P Q g (v 0)
  have hy : ∀t∈Icc 0 T,HasDerivAt y (A t (y t)+g t) t := by
    intro t ht
    exact variationSolution_hasDerivAt hQ hg (hP t ht) (hPQ t ht)
  have hLip : ∀t∈Ico 0 T,LipschitzOnWith L (fun x => A t x+g t) (univ : Set E) := by
    intro t ht
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm,add_sub_add_right_eq_sub,←map_sub]
    exact ((A t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hA t (Ico_subset_Icc_self ht)) (norm_nonneg _))
  have he := ODE_solution_unique_of_mem_Icc_right (v:=fun t x => A t x+g t)
    (s:=fun _ => univ) hLip
    (HasDerivAt.continuousOn hv)
    (fun t ht => (hv t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (by intros; trivial)
    (HasDerivAt.continuousOn hy)
    (fun t ht => (hy t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (by intros; trivial)
    (show v 0=y 0 by simp [y,variationSolution,hP0])
  exact he

/-- A non-exponential forcing bound using the true fundamental matrix and
its inverse. This is the estimate needed for the certificate's sharp second
variation budget once the actual variational equations have been derived. -/
theorem variation_of_constants_norm_bound
    {A P Q : ℝ → E →L[ℝ] E} {g v : ℝ → E} {T K I ε : ℝ} {L : ℝ≥0}
    (hK : 0≤K) (hI : 0≤I)
    (hQ : Continuous Q) (hg : Continuous g)
    (hA : ∀t∈Icc 0 T,‖A t‖≤(L:ℝ))
    (hP : ∀t∈Icc 0 T,HasDerivAt P ((A t).comp (P t)) t)
    (hPQ : ∀t∈Icc 0 T,(P t).comp (Q t)=ContinuousLinearMap.id ℝ E)
    (hP0 : P 0=ContinuousLinearMap.id ℝ E)
    (hv : ∀t∈Icc 0 T,HasDerivAt v (A t (v t)+g t) t)
    (hPbound : ∀t∈Icc 0 T,‖P t‖≤K)
    (hQbound : ∀t∈Icc 0 T,‖Q t‖≤I)
    (hgBound : ∀t∈Icc 0 T,‖g t‖≤ε) :
    ∀t∈Icc 0 T,‖v t‖≤K*(‖v 0‖+I*ε*t) := by
  intro t ht
  have hi : ‖∫s in (0:ℝ)..t,Q s (g s)‖≤I*ε*t := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=0) (b:=t) (C:=I*ε) (f:=fun s => Q s (g s)) (by
        intro s hs
        have hs' : s∈Icc 0 T := by
          rw [uIoc_of_le ht.1] at hs
          exact ⟨hs.1.le,hs.2.trans ht.2⟩
        exact ((Q s).le_opNorm _).trans
          (mul_le_mul (hQbound s hs') (hgBound s hs') (norm_nonneg _) hI))
    simpa only [sub_zero,abs_of_nonneg ht.1] using h
  rw [variation_of_constants hQ hg hA hP hPQ hP0 hv t ht,variationSolution]
  exact ((P t).le_opNorm _).trans
    (mul_le_mul (hPbound t ht) ((norm_add_le _ _).trans (add_le_add le_rfl hi))
      (norm_nonneg _) hK)

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating variation-of-constants audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating variation-of-constants audit passed for {count} declarations."
