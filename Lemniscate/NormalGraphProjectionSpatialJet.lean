import Lemniscate.NormalProjectionVectorField
import Lemniscate.PartialSpatialDerivative
import Lemniscate.ParametricODEFourthJet

/-! Joint continuity of the actual first four spatial derivatives of
normal projection, including a boundary of the parameter set. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff

private theorem projection_parameter_restriction_continuousOn
    {P E F : Type*} [TopologicalSpace P] [TopologicalSpace E] [TopologicalSpace F]
    (U : Set P) (O : Set E) (f : P × E → F)
    (hf : ContinuousOn f (U ×ˢ O)) :
    ContinuousOn (fun z : U × E => f ((z.1:P),z.2)) (univ ×ˢ O) := by
  have hi : Continuous (fun z : U × E => ((z.1:P),z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  simpa only [Function.comp_def] using
    hf.comp hi.continuousOn (fun z hz => ⟨z.1.property,hz.2⟩)

/-- The normal-projection spatial ODE gives a genuine continuous fourth
spatial derivative jet up to a parameter boundary. No higher regularity
of the trajectory is assumed, and only the state variable is
differentiated when constructing the vector-field derivatives. -/
theorem normal_graph_projection_spatial_jet
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (U : Set P) (hU : UniqueDiffOn ℝ U) (V : P × ℝ → ℂ)
    (hV : ContDiffOn ℝ ∞ V (U ×ˢ (univ : Set ℝ)))
    (T : ℝ → ℂ) (κ : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (hκ : ContDiff ℝ ∞ κ)
    (hTd : ∀ s, HasDerivAt T (I*(κ s:ℂ)*T s) s)
    (hunit : ∀ s, ‖T s‖=1)
    (δ K r : ℝ) (hK : 0≤K) (hsmall : δ+K*r<1)
    (hcurvature : ∀ s, |κ s|≤K)
    (hclose : ∀ p ∈ U, ∀ x : ℝ, ‖V (p,x)-T x‖≤δ)
    (y : U → ℝ → NormalProjectionState)
    (hy : Continuous (fun z : U × ℝ => y z.1 z.2))
    (hdisplacement : ∀ p s, |(y p s).2.1|<r)
    (hODE : ∀ p s, HasDerivAt (y p)
      (normalProjectionVectorField T κ V ((p:P),y p s)) s) :
    Continuous (fun z : U × ℝ =>
      fun j : Fin 5 => iteratedDeriv j.val (y z.1) z.2) := by
  let E₁ := NormalProjectionState →L[ℝ] NormalProjectionState
  letI : NormedAddCommGroup E₁ := inferInstance
  letI : NormedSpace ℝ E₁ := inferInstance
  let E₂ := NormalProjectionState →L[ℝ] E₁
  letI : NormedAddCommGroup E₂ := inferInstance
  letI : NormedSpace ℝ E₂ := inferInstance
  let E₃ := NormalProjectionState →L[ℝ] E₂
  letI : NormedAddCommGroup E₃ := inferInstance
  letI : NormedSpace ℝ E₃ := inferInstance
  let O : Set NormalProjectionState := {z | |z.2.1|<r}
  let G₀ : P × NormalProjectionState → NormalProjectionState :=
    normalProjectionVectorField T κ V
  let G₁ : P × NormalProjectionState → (NormalProjectionState →L[ℝ] NormalProjectionState) :=
    spatialDerivativeWithin U O G₀
  let G₂ : P × NormalProjectionState →
      (NormalProjectionState →L[ℝ] (NormalProjectionState →L[ℝ] NormalProjectionState)) :=
    spatialDerivativeWithin U O G₁
  let G₃ : P × NormalProjectionState →
      (NormalProjectionState →L[ℝ] (NormalProjectionState →L[ℝ]
        (NormalProjectionState →L[ℝ] NormalProjectionState))) :=
    spatialDerivativeWithin U O G₂
  have hfield := normal_projection_vector_field_smooth U V hV T κ hT hκ hTd hunit
    δ K r hK hsmall hcurvature hclose
  have hO : IsOpen O := hfield.1
  have hG₀ : ContDiffOn ℝ ∞ G₀ (U ×ˢ O) := hfield.2.2
  have hD₀ := spatial_derivative_within_smooth U O hU hO G₀ hG₀
  have hG₁ : ContDiffOn ℝ ∞ G₁ (U ×ˢ O) := hD₀.1
  have hD₁ := spatial_derivative_within_smooth U O hU hO G₁ hG₁
  have hG₂ : ContDiffOn ℝ ∞ G₂ (U ×ˢ O) := hD₁.1
  have hD₂ := spatial_derivative_within_smooth U O hU hO G₂ hG₂
  have hG₃ : ContDiffOn ℝ ∞ G₃ (U ×ˢ O) := hD₂.1
  exact parametric_ode_fourth_jet O
    (fun (p : U) x => G₀ ((p:P),x)) (fun (p : U) x => G₁ ((p:P),x))
    (fun (p : U) x => G₂ ((p:P),x)) (fun (p : U) x => G₃ ((p:P),x))
    (projection_parameter_restriction_continuousOn U O G₀ hG₀.continuousOn)
    (projection_parameter_restriction_continuousOn U O G₁ hG₁.continuousOn)
    (projection_parameter_restriction_continuousOn U O G₂ hG₂.continuousOn)
    (projection_parameter_restriction_continuousOn U O G₃ hG₃.continuousOn)
    (fun p x hx => hD₀.2 p.val p.property x hx)
    (fun p x hx => hD₁.2 p.val p.property x hx)
    (fun p x hx => hD₂.2 p.val p.property x hx)
    y hy hdisplacement hODE

end Lemniscate
