module

public import SolitonClassification.Rotating.FlowBootstrapCoordinates

@[expose] public section

/-! A first-threshold argument for the actual globally existing clipped
flow. The original-field comparison is used only before the threshold;
the strict radius budget then proves tube confinement as a conclusion. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem bootstrap_from_derivative_before_threshold
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {w w' : ℝ → V} {l r R C : ℝ}
    (hC : 0≤C) (hc : ContinuousOn w (Icc l r))
    (hd : ∀t∈Ico l r,‖w t‖<R → HasDerivWithinAt w (w' t) (Ici t) t)
    (hb : ∀t∈Ico l r,‖w t‖<R → ‖w' t‖≤C)
    (hstrict : ‖w l‖+C*(r-l)<R) :
    ∀t∈Icc l r,‖w t‖<R ∧ ‖w t‖≤‖w l‖+C*(t-l) := by
  have hsmall : ∀t∈Icc l r,‖w t‖<R := by
    by_contra hnot
    push Not at hnot
    obtain ⟨s,hs,hlarge,hbefore⟩ := bootstrap_exists_first_threshold hc.norm hnot
    have hsub : Icc l s⊆Icc l r := Icc_subset_Icc_right hs.2
    have hds : ∀t∈Ico l s,HasDerivWithinAt w (w' t) (Ici t) t :=
      fun t ht => hd t ⟨ht.1,ht.2.trans_le hs.2⟩ (hbefore t ht)
    have hbs : ∀t∈Ico l s,‖w' t‖≤0*‖w t‖+C := by
      intro t ht
      simpa only [zero_mul,zero_add] using hb t ⟨ht.1,ht.2.trans_le hs.2⟩ (hbefore t ht)
    have he := norm_le_gronwallBound_of_norm_deriv_right_le (hc.mono hsub) hds
      (le_refl ‖w l‖) hbs s ⟨hs.1,le_rfl⟩
    simp only [gronwallBound_K0] at he
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 l) hC
    linarith
  have he := norm_le_gronwallBound_of_norm_deriv_right_le (K:=0) (ε:=C) hc
    (fun t ht => hd t ht (hsmall t (Ico_subset_Icc_self ht))) (le_refl ‖w l‖)
    (fun t ht => by simpa only [zero_mul,zero_add] using hb t ht (hsmall t (Ico_subset_Icc_self ht)))
  intro t ht
  exact ⟨hsmall t ht,by simpa only [gronwallBound_K0] using he t ht⟩

def bootstrapForcing (K I R ρ δ : ℝ) : ℝ := I*(2*K^2*R^2+ρ*R+δ)

theorem bootstrap_reference_segment (σ : ℝ) (hσ : |σ|≤1) (a : State)
    {l r K I R ρ δ : ℝ} {X rx : ℝ → State} {M Z : ℝ → FlowEnd}
    (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hX : ContinuousOn X (Icc l r)) (hM : ContinuousOn M (Icc l r))
    (hu : ∀t∈Icc l r,IsUnit (M t))
    (hXd : ∀t∈Ico l r,HasDerivWithinAt X (σ • field (X t)+rx t) (Ici t) t)
    (hMd : ∀t∈Ico l r,HasDerivWithinAt M ((σ • fderiv ℝ field (X t))*M t+Z t) (Ici t) t)
    (hMb : ∀t∈Icc l r,‖M t‖≤K) (hIb : ∀t∈Icc l r,‖Ring.inverse (M t)‖≤I)
    (hZ : ∀t∈Icc l r,‖Z t‖≤ρ) (hrx : ∀t∈Icc l r,‖rx t‖≤δ)
    (hmargin : ∀t∈Icc l r,outerTubeMargin (X t) (K*R))
    (hstrict : ‖bootstrapError σ hσ a X M l‖+bootstrapForcing K I R ρ δ*(r-l)<R) :
    ∀t∈Icc l r,
      supportFlow σ hσ t a∈outerTube ∧
      ‖bootstrapError σ hσ a X M t‖<R ∧
      ‖bootstrapError σ hσ a X M t‖≤
        ‖bootstrapError σ hσ a X M l‖+bootstrapForcing K I R ρ δ*(t-l) ∧
      ‖supportFlow σ hσ t a-X t‖≤K*R := by
  let w := bootstrapError σ hσ a X M
  let v : ℝ → State := fun t => bootstrapVelocity σ (supportFlow σ hσ t a) (X t) (M t) (Z t) (rx t)
  have hc : ContinuousOn w (Icc l r) := bootstrap_error_continuousOn σ hσ a hX hM hu
  have htube {t : ℝ} (ht : t∈Icc l r) (hw : ‖w t‖≤R) : supportFlow σ hσ t a∈outerTube :=
    bootstrap_tube_of_error_bound σ hσ a (hu t ht) hK (hMb t ht) (hmargin t ht) hw
  have hRef {t : ℝ} (ht : t∈Icc l r) : X t∈outerTube :=
    outerTube_of_margin (hmargin t ht) (by simpa using mul_nonneg hK hR)
  have hd : ∀t∈Ico l r,‖w t‖<R → HasDerivWithinAt w (v t) (Ici t) t := by
    intro t ht hw
    exact bootstrap_error_hasDerivWithinAt σ hσ a
      (htube (Ico_subset_Icc_self ht) hw.le) (hu t (Ico_subset_Icc_self ht)) (hXd t ht) (hMd t ht)
  have hb : ∀t∈Ico l r,‖w t‖<R → ‖v t‖≤bootstrapForcing K I R ρ δ := by
    intro t ht hw
    have ht' := Ico_subset_Icc_self ht
    exact bootstrap_velocity_bound σ hσ (htube ht' hw.le) (hRef ht') (hu t ht')
      hK hI hR hρ (hMb t ht') (hIb t ht') (hZ t ht') (hrx t ht') hw.le
  have hC : 0≤bootstrapForcing K I R ρ δ := by dsimp [bootstrapForcing]; positivity
  have hh := bootstrap_from_derivative_before_threshold hC hc hd hb hstrict
  intro t ht
  have h := hh t ht
  exact ⟨htube ht h.1.le,h.1,h.2,bootstrap_physical_error_bound σ hσ a (hu t ht) hK (hMb t ht) h.1.le⟩

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual state first-threshold audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual state first-threshold audit passed for {count} declarations."

end
