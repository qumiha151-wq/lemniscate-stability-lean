import SolitonClassification.Rotating.FlowFoundation

/-! Original-field local existence from the actual globally chosen clipped
flow. Coordinate displacement estimates avoid assuming tube confinement. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set

def coordinateSpeed : Fin 6 → ℝ := ![36,40,75,75,0,17/2]

theorem coordinateSpeed_nonneg (i : Fin 6) : 0≤coordinateSpeed i := by
  fin_cases i <;> norm_num [coordinateSpeed]

theorem clippedField_coordinate_bound (a : State) (i : Fin 6) :
    |clippedField a i|≤coordinateSpeed i := by
  have ha := clipState_mem a
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  fin_cases i
  · change |8*clipState a 1|≤36
    rw [abs_mul]; norm_num; linarith
  · change |-(clipState a 0)^3/16-clipState a 2/8-clipState a 4*clipState a 3/8|≤40
    calc
      _ ≤ |-(clipState a 0)^3/16-clipState a 2/8|+|clipState a 4*clipState a 3/8| := abs_sub _ _
      _ ≤ (|-(clipState a 0)^3/16|+|clipState a 2/8|)+|clipState a 4*clipState a 3/8| := by
        gcongr; apply abs_sub
      _ = |clipState a 0|^3/16+|clipState a 2|/8+|clipState a 4| * |clipState a 3|/8 := by
        simp [abs_div,abs_mul,abs_pow]
      _ ≤ (17/2)^3/16+(17/2)/8+(1/50)*(17/2)/8 := by gcongr
      _ ≤ 40 := by norm_num
  · exact (coordinate_bound (clippedField a) 2).trans (clippedField_bound a)
  · exact (coordinate_bound (clippedField a) 3).trans (clippedField_bound a)
  · simp [clippedField,field,coordinateSpeed]
  · exact h0

theorem supportFlow_coordinate_displacement (σ : ℝ) (hσ : |σ|≤1)
    (a : State) (t : ℝ) (i : Fin 6) :
    |supportFlow σ hσ t a i-a i|≤coordinateSpeed i*|t| := by
  have hd (s : ℝ) : HasDerivAt (fun t=>supportFlow σ hσ t a i)
      (signedClippedField σ (supportFlow σ hσ s a) i) s :=
    hasDerivAt_pi.mp (supportFlow_derivative σ hσ a s) i
  have hb (s : ℝ) : ‖signedClippedField σ (supportFlow σ hσ s a) i‖≤coordinateSpeed i := by
    change |σ*clippedField (supportFlow σ hσ s a) i|≤_
    rw [abs_mul]
    calc
      _ ≤ 1*coordinateSpeed i := mul_le_mul hσ
        (clippedField_coordinate_bound _ i) (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have h := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _=>(hd s).hasDerivWithinAt) (fun s _=>hb s)
    (x:=0) (y:=t) (mem_univ _) (mem_univ _)
  simpa only [supportFlow_zero,Real.norm_eq_abs,sub_zero] using h

def innerTube : Set State := {a | |a 0|≤407/50 ∧ |a 1|≤33/8 ∧
  |a 2|≤731/100 ∧ |a 3|≤731/100 ∧ |a 4|≤1/100}

theorem supportFlow_short_mem_outerTube (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {t : ℝ} (ht : 0≤t) (hT : t≤1/125) :
    supportFlow σ hσ t a∈outerTube := by
  have h (i : Fin 6) : |supportFlow σ hσ t a i|≤coordinateSpeed i*t+|a i| := by
    have hd := supportFlow_coordinate_displacement σ hσ a t i
    rw [abs_of_nonneg ht] at hd
    calc
      _ = |(supportFlow σ hσ t a i-a i)+a i| := by rw [sub_add_cancel]
      _ ≤ |supportFlow σ hσ t a i-a i|+|a i| := abs_add_le _ _
      _ ≤ _ := by linarith
  rcases ha with ⟨a0,a1,a2,a3,a4⟩
  have h0:=h 0; have h1:=h 1; have h2:=h 2; have h3:=h 3; have h4:=h 4
  norm_num [coordinateSpeed] at h0 h1 h2 h3 h4
  change |supportFlow σ hσ t a 2|≤75*t+|a 2| at h2
  change |supportFlow σ hσ t a 3|≤75*t+|a 3| at h3
  change |supportFlow σ hσ t a 4|≤0*t+|a 4| at h4
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem supportFlow_short_original (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {t : ℝ} (ht : 0≤t) (hT : t≤1/125) :
    HasDerivAt (fun s=>supportFlow σ hσ s a)
      (σ • field (supportFlow σ hσ t a)) t :=
  supportFlow_original_derivative σ hσ a t (supportFlow_short_mem_outerTube σ hσ ha ht hT)

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.supportFlow_short_original
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Actual short original-flow tube audit passed."
