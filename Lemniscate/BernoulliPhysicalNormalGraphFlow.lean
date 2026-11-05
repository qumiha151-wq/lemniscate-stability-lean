import Lemniscate.BernoulliGlobalInitialEquation
import Lemniscate.NormalGraphPhysicalNormalFlow
import Lemniscate.PhysicalNormalization

/-! A small actual global MR solution reconstructs a physical free elastic
flow, including its initial right derivative and the exact expanding scale. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped Topology NNReal ComplexConjugate

private theorem physical_graph_radius {P : ℝ → Prop} {Q : Prop}
    (h : ∃ δ>0, P δ) (k : ∀ δ, 0<δ → P δ → Q) : Q := by
  obtain ⟨δ,hδ,hP⟩ := h
  exact k δ hδ hP

variable (T : ℝ) [Fact (0<T)]

set_option maxHeartbeats 1200000 in
/-- The actual normal-height evolution gives a physical curve flow with
its actual time derivative. No geometric flow equation is assumed. -/
theorem bernoulli_physical_normal_graph_flow
    (e : ℝ ≃o ℝ)
    (he : ∀ u, e u=∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    (q p : C(AddCircle T,ℂ))
    (hq : ∀ x : ℝ, q (x:AddCircle T)=(bernoulliProfileQ (e.symm x):ℂ))
    (hp : ∀ x : ℝ, p (x:AddCircle T)=(bernoulliProfileP (e.symm x):ℂ))
    (ψ : CircleL2 T) :
    ∃ δ>0, ∀ τ : ℝ, ∀ hτ : 0<τ,
      ∀ u : C(ℝ≥0,CircleSobolevSpace T 2), ∀ U : ℕ → CircleParabolicSpace T τ,
      ∀ w : C(Ioi (0:ℝ),CircleSobolevSpace T 5),
      ∀ W₀ : C(unitInterval,CircleSobolevSpace T 5),
      ∀ ω : ℝ → ℝ, ∀ Ω₀ : C(unitInterval,ℝ), ∀ θ : ℝ → ℝ,
      (∀ m, ‖circleParabolicCurve T τ (U m)‖<δ) →
      (∀ m r, u (circleParabolicSegmentTime τ hτ m r)=circleParabolicCurve T τ (U m) r) →
      (∀ t : ℝ≥0, 0<t → ∃ (m : ℕ) (r : unitInterval),
        0<(r:ℝ) ∧ (r:ℝ)<1 ∧ circleParabolicSegmentTime τ hτ m r=t) →
      (∀ t : Ioi (0:ℝ), circleSobolevInclusion T 2
        (circleSobolevInclusion T 3 (circleSobolevInclusion T 4 (w t)))=
          u ⟨(t:ℝ),t.property.le⟩) →
      (∀ r : unitInterval, circleSobolevInclusion T 2
        (circleSobolevInclusion T 3 (circleSobolevInclusion T 4 (W₀ r)))=
          circleParabolicCurve T τ (U 0) r) →
      (∀ t : ℝ≥0, circleSobolevConjugation T 2 (u t)=u t) →
      ContinuousOn ω (Ioi (0:ℝ)) →
      (∀ t : Ioi (0:ℝ), (ω t:ℂ)=circleNormalGraphAngularVelocity T
        (circleBernoulliBackground T q p) (15/2) ψ (circleSobolevInclusion T 4 (w t))) →
      (∀ r : unitInterval, (Ω₀ r:ℂ)=circleNormalGraphAngularVelocity T
        (circleBernoulliBackground T q p) (15/2) ψ (circleSobolevInclusion T 4 (W₀ r))) →
      ω 0=Ω₀ 0 →
      (∀ m, ∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ (U m) r=
        circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
          (circleParabolicH4 T τ (U m) r)) →
      (∀ σ : ℝ, 0≤σ → HasDerivWithinAt θ (ω σ) (Ici (0:ℝ)) σ) →
      ∀ a : ℝ, 0<a → ∀ p₀ : ℂ,
      let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
      let β := bernoulliCurve ∘ φ
      let ν := fun s : ℝ => I*(bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ))
      let h : ℝ → ℝ → ℝ := fun σ s => (circleSobolevH1Embedding T
        (circleSobolevInclusion T 1 (u (Real.toNNReal σ))) ((Real.sqrt 2*s):AddCircle T)).re
      ∃ ρ : ℝ → ℝ, ρ 0=a ∧
        (∀ t : ℝ, 0≤t → 0<ρ t ∧ ρ t=(a^4+30*t)^(1/4:ℝ)) ∧
        Tendsto ρ atTop atTop ∧
        let Y : ℝ → ℝ → ℂ := fun t s => p₀+(ρ t:ℂ)*
          (Complex.exp ((θ (normalizedTime a t):ℂ)*I)*normalGraphCurve β ν (h (normalizedTime a t)) s)
        (∀ s, Y 0 s=p₀+(a:ℂ)*(Complex.exp ((θ 0:ℂ)*I)*normalGraphCurve β ν (h 0) s)) ∧
        ∀ t : ℝ, 0≤t → ∃ V : ℝ → ℂ, ∀ s : ℝ,
          let n := I*deriv (Y t) s/(‖deriv (Y t) s‖:ℂ)
          HasDerivWithinAt (fun z => Y z s) (V s) (Ici (0:ℝ)) t ∧
          deriv (Y t) s≠0 ∧ ‖n‖=1 ∧
          (((conj (V s)*n).re:ℂ)*n)=
            -((arclengthDerivative (Y t)
              (arclengthDerivative (Y t) (planarSignedCurvature (Y t))) s+
              (1/2:ℝ)*(planarSignedCurvature (Y t) s)^3:ℝ):ℂ)*n := by
  refine physical_graph_radius (bernoulli_global_initial_equation T e he q p hq hp ψ) ?_
  intro δ hδ hheight
  refine ⟨δ,hδ,?_⟩
  intro τ hτ u U w W₀ ω Ω₀ θ hU hrep hcover hw hW₀ hreal hωc hω hΩ₀ hω₀ hPDE hθ a ha p₀
  dsimp only
  have heq := hheight τ hτ u U w W₀ ω Ω₀ hU hrep hcover hw hW₀ hreal hωc hω hΩ₀ hω₀ hPDE
  dsimp only at heq
  obtain ⟨ρ,hρ₀,hσ₀,hρ,hρtop,_⟩ := physical_normalization a ha
  let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
  let β := bernoulliCurve ∘ φ
  let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
  let ν := fun s : ℝ => I*t s
  let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
  let h : ℝ → ℝ → ℝ := fun σ s => (circleSobolevH1Embedding T
    (circleSobolevInclusion T 1 (u (Real.toNNReal σ))) ((Real.sqrt 2*s):AddCircle T)).re
  let d₀ := fun s : ℝ => Real.sqrt 2*
    (circleSobolevClassicalJet T 4 (W₀ 0) 1 ((Real.sqrt 2*s):AddCircle T)).re
  let d : ℝ → ℝ → ℝ := fun σ s => if hs : 0<σ then Real.sqrt 2*
    (circleSobolevClassicalJet T 4 (w ⟨σ,hs⟩) 1 ((Real.sqrt 2*s):AddCircle T)).re else d₀ s
  let v : ℝ → ℝ → ℝ := fun σ s => normalGraphFlowRHS β ν k (h σ) (15/2) s-
    ω σ*((conj (t s)*β s).re+((conj (t s)*β s).im+h σ s)*d σ s/(1-k s*h σ s))
  let Y : ℝ → ℝ → ℂ := fun t s => p₀+(ρ t:ℂ)*
    (Complex.exp ((θ (normalizedTime a t):ℂ)*I)*normalGraphCurve β ν (h (normalizedTime a t)) s)
  have hframe := bernoulli_arclength_frame e he
  dsimp only at hframe
  have hmap : MapsTo (normalizedTime a) (Ici (0:ℝ)) (Ici (0:ℝ)) :=
    fun t ht => (hρ t ht).2.2.1
  refine ⟨ρ,hρ₀,fun t ht => ⟨(hρ t ht).1,(hρ t ht).2.1⟩,hρtop,?_,?_⟩
  · intro s
    change Y 0 s=_
    simp only [Y,hρ₀,hσ₀,β,ν,t,φ,h]
  · intro t₀ ht₀
    let σ := normalizedTime a t₀
    have hσ : 0≤σ := (hρ t₀ ht₀).2.2.1
    obtain ⟨Vy,hVy⟩ := normal_graph_physical_velocity_equivalence β t ν k h θ ρ (normalizedTime a)
      (Ici (0:ℝ)) (Ici (0:ℝ)) p₀ t₀ (15/2) (ω σ) (v σ) (d σ)
      (fun s => (hframe s).1) (fun s => (hframe s).2.2.2.1)
      (fun s => (hframe s).2.1) (fun _ => rfl)
      (fun s => (heq σ hσ s).1) (fun s => (heq σ hσ s).2.2)
      (hθ σ hσ) (hρ t₀ ht₀).1
      (hρ t₀ ht₀).2.2.2.2.1.hasDerivWithinAt
      (hρ t₀ ht₀).2.2.2.2.2.hasDerivWithinAt hmap
      (fun s => (heq σ hσ s).2.1)

    refine ⟨Vy,?_⟩
    intro s
    have hdata := hVy s
    refine ⟨hdata.1,hdata.2.1,hdata.2.2.1,?_⟩
    have hscalar := hdata.2.2.2.mpr (by dsimp only [v]; ring)
    have hvector := congrArg (fun a : ℝ => (a:ℂ)*
      (I*deriv (Y t₀) s/(‖deriv (Y t₀) s‖:ℂ))) hscalar
    simpa only [planarElasticForce,Complex.ofReal_neg] using! hvector

end Lemniscate
