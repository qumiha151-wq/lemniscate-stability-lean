import SolitonClassification.Rotating.VariationConstants

/-! Closed-interval variation of constants, using actual right derivatives
at the initial endpoint. This version matches the derived first variational
ODE and needs continuity of the inverse only on the certified interval. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_right_derivative_of_continuousOn {g : ℝ → E} {T t : ℝ}
    (hg : ContinuousOn g (Icc 0 T)) (ht : t∈Ico 0 T) :
    HasDerivWithinAt (fun u => ∫s in (0:ℝ)..u,g s) (g t) (Ici t) t := by
  have hn : Icc (0:ℝ) T∈𝓝[Ici t] t :=
    Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (fun _ hs => ⟨ht.1.trans hs.1,hs.2⟩)
  have hn' : Icc (0:ℝ) T∈𝓝[Ioi t] t := nhdsWithin_mono t Ioi_subset_Ici_self hn
  have hi : IntervalIntegrable g volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    apply hg.mono
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2.le
  exact intervalIntegral.integral_hasDerivWithinAt_right (s:=Ici t) (t:=Ioi t) hi
    ⟨Icc 0 T,hn',hg.aestronglyMeasurable measurableSet_Icc⟩
    ((hg t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin hn')

theorem variation_of_constants_within
    {A P Q : ℝ → E →L[ℝ] E} {g v : ℝ → E} {T : ℝ} {L : ℝ≥0}
    (hT : 0≤T) (hQc : ContinuousOn Q (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hA : ∀t∈Icc 0 T,‖A t‖≤(L:ℝ))
    (hPc : ContinuousOn P (Icc 0 T))
    (hP : ∀t∈Ico 0 T,HasDerivWithinAt P ((A t).comp (P t)) (Ici t) t)
    (hPQ : ∀t∈Icc 0 T,(P t).comp (Q t)=ContinuousLinearMap.id ℝ E)
    (hP0 : P 0=ContinuousLinearMap.id ℝ E)
    (hvc : ContinuousOn v (Icc 0 T))
    (hv : ∀t∈Ico 0 T,HasDerivWithinAt v (A t (v t)+g t) (Ici t) t) :
    ∀t∈Icc 0 T,v t=variationSolution P Q g (v 0) t := by
  let y := variationSolution P Q g (v 0)
  have hc : ContinuousOn (fun s => Q s (g s)) (Icc 0 T) := hQc.clm_apply hgc
  have hic : ContinuousOn (fun t => ∫s in (0:ℝ)..t,Q s (g s)) (Icc 0 T) := by
    have h := intervalIntegral.continuousOn_primitive_interval
      (show IntegrableOn (fun s => Q s (g s)) (uIcc 0 T) volume by
        simpa only [uIcc_of_le hT] using hc.integrableOn_Icc)
    simpa only [uIcc_of_le hT] using h
  have hyc : ContinuousOn y (Icc 0 T) := hPc.clm_apply (continuousOn_const.add hic)
  have hy : ∀t∈Ico 0 T,HasDerivWithinAt y (A t (y t)+g t) (Ici t) t := by
    intro t ht
    have hd := (hP t ht).clm_apply ((integral_right_derivative_of_continuousOn hc ht).const_add (v 0))
    convert! hd using 1
    change A t (P t (v 0+∫s in (0:ℝ)..t,Q s (g s)))+g t=
      ((A t).comp (P t)) (v 0+∫s in (0:ℝ)..t,Q s (g s))+P t (Q t (g t))
    rw [←ContinuousLinearMap.comp_apply (P t) (Q t),hPQ t (Ico_subset_Icc_self ht)]
    rfl
  have hLip : ∀t∈Ico 0 T,LipschitzOnWith L (fun x => A t x+g t) (univ : Set E) := by
    intro t ht
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm,add_sub_add_right_eq_sub,←map_sub]
    exact ((A t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hA t (Ico_subset_Icc_self ht)) (norm_nonneg _))
  exact ODE_solution_unique_of_mem_Icc_right (v:=fun t x => A t x+g t)
    (s:=fun _ => univ) hLip hvc hv (by intros; trivial) hyc hy (by intros; trivial)
    (show v 0=y 0 by simp [y,variationSolution,hP0])

theorem variation_of_constants_within_norm_bound
    {A P Q : ℝ → E →L[ℝ] E} {g v : ℝ → E} {T K I ε : ℝ} {L : ℝ≥0}
    (hT : 0≤T) (hK : 0≤K) (hI : 0≤I)
    (hQc : ContinuousOn Q (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hA : ∀t∈Icc 0 T,‖A t‖≤(L:ℝ))
    (hPc : ContinuousOn P (Icc 0 T))
    (hP : ∀t∈Ico 0 T,HasDerivWithinAt P ((A t).comp (P t)) (Ici t) t)
    (hPQ : ∀t∈Icc 0 T,(P t).comp (Q t)=ContinuousLinearMap.id ℝ E)
    (hP0 : P 0=ContinuousLinearMap.id ℝ E)
    (hvc : ContinuousOn v (Icc 0 T))
    (hv : ∀t∈Ico 0 T,HasDerivWithinAt v (A t (v t)+g t) (Ici t) t)
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
  rw [variation_of_constants_within hT hQc hgc hA hPc hP hPQ hP0 hvc hv t ht,variationSolution]
  exact ((P t).le_opNorm _).trans
    (mul_le_mul (hPbound t ht) ((norm_add_le _ _).trans (add_le_add le_rfl hi)) (norm_nonneg _) hK)

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating closed-interval variation audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating closed-interval variation audit passed for {count} declarations."
