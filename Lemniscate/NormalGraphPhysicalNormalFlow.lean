import Lemniscate.ElasticFlowNormalization
import Lemniscate.NormalGraphFlowVariation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric

/-! Reconstruction of the actual projected free elastic flow from the
rotating normal-graph equation and the physical-time normalization. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ComplexConjugate

/-- The true physical normal-velocity equation is equivalent to the
scalar modulated height equation, for the actual reconstructed curve.
The derivative and regularity are proved independently of either PDE;
derivatives within the given time sets include the initial endpoint. -/
theorem normal_graph_physical_velocity_equivalence
    (β t n : ℝ → ℂ) (k : ℝ → ℝ) (H : ℝ → ℝ → ℝ)
    (θ ρ σ : ℝ → ℝ) (S J : Set ℝ)
    (p₀ : ℂ) (t₀ c ω : ℝ) (v h₁ : ℝ → ℝ)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (hn : ∀ s, HasDerivAt n (-(k s:ℂ)*t s) s)
    (hu : ∀ s, ‖t s‖=1) (hN : ∀ s, n s=I*t s)
    (hspace : ∀ s, HasDerivAt (H (σ t₀)) (h₁ s) s)
    (htime : ∀ s, HasDerivWithinAt (fun z => H z s) (v s) J (σ t₀))
    (hθ : HasDerivWithinAt θ ω J (σ t₀)) (hρ : 0<ρ t₀)
    (hρd : HasDerivWithinAt ρ (c*(ρ t₀)⁻¹^3) S t₀)
    (hσd : HasDerivWithinAt σ ((ρ t₀)⁻¹^4) S t₀)
    (hσmap : MapsTo σ S J)
    (hregular : ∀ s, 0<1-k s*H (σ t₀) s)
    :
    let Y : ℝ → ℝ → ℂ := fun z s => p₀+(ρ z:ℂ)*
      (Complex.exp ((θ (σ z):ℂ)*I)*normalGraphCurve β n (H (σ z)) s)
    ∃ Vy : ℝ → ℂ, ∀ s,
      let ν := I*deriv (Y t₀) s/(‖deriv (Y t₀) s‖:ℂ)
      HasDerivWithinAt (fun z => Y z s) (Vy s) S t₀ ∧
      deriv (Y t₀) s≠0 ∧ ‖ν‖=1 ∧
      ((conj (Vy s)*ν).re=-(planarElasticForce (Y t₀) s) ↔
        v s+ω*((conj (t s)*β s).re+
          ((conj (t s)*β s).im+H (σ t₀) s)*h₁ s/(1-k s*H (σ t₀) s))=
          normalGraphFlowRHS β n k (H (σ t₀)) c s) := by
  dsimp only
  let τ := σ t₀
  let R := Complex.exp ((θ τ:ℂ)*I)
  let γ := normalGraphCurve β n (H τ)
  let X : ℝ → ℝ → ℂ := fun z s => Complex.exp ((θ z:ℂ)*I)*normalGraphCurve β n (H z) s
  let V : ℝ → ℂ := fun s => R*(I*(ω:ℂ)*γ s+(v s:ℂ)*n s)
  let F : ℝ → ℝ := fun s => planarElasticForce γ s+c*planarNormalSupport γ s
  have hR : ‖R‖=1 := Complex.norm_exp_ofReal_mul_I (θ τ)
  have hgraph := normal_graph_rotating_velocity_equivalence β t n k H θ J τ ω v h₁ F
    hβ hn hu hN hspace htime hθ hregular
  obtain ⟨Vy,hVy⟩ := elastic_flow_normalization_equivalence γ (fun s => (hgraph.1 s).1)
    R hR X V ρ σ S J p₀ t₀ c (fun _ => rfl) (fun s => (hgraph.2 s).1)
    hρ hρd hσd hσmap
  refine ⟨Vy,?_⟩
  intro s
  have h := hVy s
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  have hheight : (conj (V s)*(R*(I*deriv γ s/(‖deriv γ s‖:ℂ)))).re=
      -(planarElasticForce γ s+c*planarNormalSupport γ s) ↔
      v s+ω*((conj (t s)*β s).re+
        ((conj (t s)*β s).im+H τ s)*h₁ s/(1-k s*H τ s))=
        normalGraphFlowRHS β n k (H τ) c s := by
    simpa only [normalGraphFlowRHS,planarElasticForce,γ,F] using! ((hgraph.2 s).2)
  exact h.2.2.2.trans hheight

end Lemniscate
