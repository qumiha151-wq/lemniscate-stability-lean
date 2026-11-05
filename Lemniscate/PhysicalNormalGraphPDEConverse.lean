import Lemniscate.NormalGraphPhysicalNormalFlow
import Lemniscate.CurveFlowTimeReparametrization

/-! The actual physical free elastic flow gives the scalar height PDE
in any genuine time-dependent normal-graph coordinates. -/
noncomputable section
namespace Lemniscate
open Complex Filter Set
open scoped Topology ContDiff ComplexConjugate

/-- A genuine graph identity on a time germ transfers the actual physical
normal velocity to the reconstructed graph. Reparametrization invariance
and the physical normalization equivalence then give its scalar height
equation, without assuming any height evolution equation. -/
theorem physical_normal_graph_pde_converse
    (Y : ℝ → ℝ → ℂ) (χ : ℝ → ℝ → ℝ) (χdot : ℝ → ℝ)
    (β t n : ℝ → ℂ) (k : ℝ → ℝ) (H : ℝ → ℝ → ℝ)
    (θ ρ σ : ℝ → ℝ) (p₀ : ℂ) (t₀ c ω₀ : ℝ) (v h₁ : ℝ → ℝ)
    (hYspace : ContDiff ℝ ∞ (Y t₀)) (hχspace : ContDiff ℝ ∞ (χ t₀))
    (hYreg : ∀ s, deriv (Y t₀) s≠0) (hχpos : ∀ s, 0<deriv (χ t₀) s)
    (hYjoint : ∀ s, DifferentiableAt ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (t₀,χ t₀ s))
    (hχtime : ∀ s, HasDerivAt (fun z => χ z s) (χdot s) t₀)
    (hYflow : ∀ s,
      (conj (deriv (fun z => Y z s) t₀)*
        (I*deriv (Y t₀) s/(‖deriv (Y t₀) s‖:ℂ))).re=
          -planarElasticForce (Y t₀) s)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (hn : ∀ s, HasDerivAt n (-(k s:ℂ)*t s) s)
    (hu : ∀ s, ‖t s‖=1) (hN : ∀ s, n s=I*t s)
    (hspace : ∀ s, HasDerivAt (H (σ t₀)) (h₁ s) s)
    (htime : ∀ s, HasDerivAt (fun z => H z s) (v s) (σ t₀))
    (hθ : HasDerivAt θ ω₀ (σ t₀)) (hρ : 0<ρ t₀)
    (hρd : HasDerivAt ρ (c*(ρ t₀)⁻¹^3) t₀)
    (hσd : HasDerivAt σ ((ρ t₀)⁻¹^4) t₀)
    (hregular : ∀ s, 0<1-k s*H (σ t₀) s)
    (hgraph : ∀ᶠ z : ℝ in 𝓝 t₀, ∀ s : ℝ,
      Y z (χ z s)=p₀+(ρ z:ℂ)*
        (Complex.exp ((θ (σ z):ℂ)*I)*normalGraphCurve β n (H (σ z)) s)) :
    ∀ s, v s+ω₀*((conj (t s)*β s).re+
      ((conj (t s)*β s).im+H (σ t₀) s)*h₁ s/(1-k s*H (σ t₀) s))=
        normalGraphFlowRHS β n k (H (σ t₀)) c s := by
  let Γ : ℝ → ℝ → ℂ := fun z s => Y z (χ z s)
  let Z : ℝ → ℝ → ℂ := fun z s => p₀+(ρ z:ℂ)*
    (Complex.exp ((θ (σ z):ℂ)*I)*normalGraphCurve β n (H (σ z)) s)
  have hbase : Γ t₀=Z t₀ := funext fun s => hgraph.self_of_nhds s
  have hreparam := curve_flow_time_reparametrization Y χ t₀ χdot
    hYspace hχspace hYreg hχpos hYjoint hχtime
  obtain ⟨V,hV⟩ := normal_graph_physical_velocity_equivalence β t n k H θ ρ σ
    univ univ p₀ t₀ c ω₀ v h₁ hβ hn hu hN hspace
    (fun s => (htime s).hasDerivWithinAt) hθ.hasDerivWithinAt hρ
    hρd.hasDerivWithinAt hσd.hasDerivWithinAt (fun _ _ => mem_univ _) hregular
  intro s
  have hVs := hV s
  have hZderiv : HasDerivAt (fun z => Z z s) (V s) t₀ :=
    hasDerivWithinAt_univ.mp hVs.1
  have hgerm : (fun z => Γ z s) =ᶠ[𝓝 t₀] fun z => Z z s :=
    hgraph.mono (fun z hz => hz s)
  have hΓderiv : HasDerivAt (fun z => Γ z s) (V s) t₀ :=
    hZderiv.congr_of_eventuallyEq hgerm
  have hforce := (hreparam s).2.2.2.2.2
  change planarElasticForce (Γ t₀) s=planarElasticForce (Y t₀) (χ t₀ s) at hforce
  have hnormal : I*deriv (Z t₀) s/(‖deriv (Z t₀) s‖:ℂ)=
      I*deriv (Γ t₀) s/(‖deriv (Γ t₀) s‖:ℂ) :=
    congrArg (fun γ : ℝ → ℂ => I*deriv γ s/(‖deriv γ s‖:ℂ)) hbase.symm
  have hforceZ : planarElasticForce (Γ t₀) s=planarElasticForce (Z t₀) s :=
    congrArg (fun γ : ℝ → ℂ => planarElasticForce γ s) hbase
  have hΓflow :
      (conj (deriv (fun z => Γ z s) t₀)*
        (I*deriv (Γ t₀) s/(‖deriv (Γ t₀) s‖:ℂ))).re=
          -planarElasticForce (Γ t₀) s :=
    ((hreparam s).2.2.2.2.1).trans
      ((hYflow (χ t₀ s)).trans (congrArg Neg.neg hforce.symm))
  apply hVs.2.2.2.mp
  calc
    (conj (V s)*(I*deriv (Z t₀) s/(‖deriv (Z t₀) s‖:ℂ))).re =
        (conj (deriv (fun z => Γ z s) t₀)*
          (I*deriv (Γ t₀) s/(‖deriv (Γ t₀) s‖:ℂ))).re := by
      rw [hnormal,hΓderiv.deriv]
    _ = -planarElasticForce (Γ t₀) s := hΓflow
    _ = -planarElasticForce (Z t₀) s := congrArg Neg.neg hforceZ

end Lemniscate
