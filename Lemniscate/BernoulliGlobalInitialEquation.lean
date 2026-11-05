import Lemniscate.BernoulliGlobalClassicalEquation
import Lemniscate.PeriodicParabolicInitialClassicalTime

/-! The actual classical height equation includes its initial right
derivative. The same global H2 curve is used at every time. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Set
open scoped Topology NNReal ComplexConjugate

private theorem initial_equation_radius {P : ℝ → Prop} {Q : Prop}
    (h : ∃ δ>0, P δ) (k : ∀ δ, 0<δ → P δ → Q) : Q := by
  obtain ⟨δ,hδ,hP⟩ := h
  exact k δ hδ hP

variable (T : ℝ) [Fact (0<T)]

set_option maxHeartbeats 1200000 in
/-- Continuous H5 regularity of the first segment supplies the initial
right derivative of the same global classical normal-height equation. -/
theorem bernoulli_global_initial_equation
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
      ∀ ω : ℝ → ℝ, ∀ Ω₀ : C(unitInterval,ℝ),
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
      let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
      let β := bernoulliCurve ∘ φ
      let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
      let n := fun s : ℝ => I*t s
      let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
      let h : ℝ → ℝ → ℝ := fun σ s => (circleSobolevH1Embedding T
        (circleSobolevInclusion T 1 (u (Real.toNNReal σ))) ((Real.sqrt 2*s):AddCircle T)).re
      let d₀ : ℝ → ℝ := fun s => Real.sqrt 2*
        (circleSobolevClassicalJet T 4 (W₀ 0) 1 ((Real.sqrt 2*s):AddCircle T)).re
      let h₁ : ℝ → ℝ → ℝ := fun σ s => if hs : 0<σ then Real.sqrt 2*
        (circleSobolevClassicalJet T 4 (w ⟨σ,hs⟩) 1 ((Real.sqrt 2*s):AddCircle T)).re else d₀ s
      ∀ σ : ℝ, 0≤σ → ∀ s : ℝ,
        HasDerivAt (h σ) (h₁ σ s) s ∧ 0<1-k s*h σ s ∧
        HasDerivWithinAt (fun z : ℝ => h z s)
          (normalGraphFlowRHS β n k (h σ) (15/2) s-
            ω σ*((conj (t s)*β s).re+
              ((conj (t s)*β s).im+h σ s)*h₁ σ s/(1-k s*h σ s))) (Ici (0:ℝ)) σ := by
  refine initial_equation_radius (bernoulli_global_classical_equation T e he q p hq hp ψ) ?_
  intro δg hδg hglobal
  refine initial_equation_radius (bernoulli_parabolic_classical_equation T e he q p hq hp ψ) ?_
  intro δl hδl hlocal
  refine ⟨min δg δl,lt_min hδg hδl,?_⟩
  intro τ hτ u U w W₀ ω Ω₀ hU hrep hcover hw hW₀ hreal hωc hω hΩ₀ hω₀ hPDE
  dsimp only
  let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
  let β := bernoulliCurve ∘ φ
  let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
  let n := fun s : ℝ => I*t s
  let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
  let value : CircleSobolevSpace T 2 → ℝ → ℝ := fun f s =>
    (circleSobolevH1Embedding T (circleSobolevInclusion T 1 f) ((Real.sqrt 2*s):AddCircle T)).re
  let h : ℝ → ℝ → ℝ := fun σ => value (u (Real.toNNReal σ))
  let d₀ : ℝ → ℝ := fun s => Real.sqrt 2*
    (circleSobolevClassicalJet T 4 (W₀ 0) 1 ((Real.sqrt 2*s):AddCircle T)).re
  let h₁ : ℝ → ℝ → ℝ := fun σ s => if hs : 0<σ then Real.sqrt 2*
    (circleSobolevClassicalJet T 4 (w ⟨σ,hs⟩) 1 ((Real.sqrt 2*s):AddCircle T)).re else d₀ s
  have hpos := hglobal τ hτ u U w ω
    (fun m => (hU m).trans_le (min_le_left δg δl)) hrep hcover hw hreal hωc hω hPDE
  have hR₀ (r : unitInterval) :
      circleSobolevConjugation T 2 (circleParabolicCurve T τ (U 0) r)=
        circleParabolicCurve T τ (U 0) r :=
    (congrArg (circleSobolevConjugation T 2) (hrep 0 r).symm).trans
      ((hreal _).trans (hrep 0 r))
  have hloc := hlocal τ hτ (U 0) ((hU 0).trans_le (min_le_right δg δl))
    0 le_rfl zero_lt_one W₀ hW₀ hR₀ Ω₀ hΩ₀ (hPDE 0)
  dsimp only at hpos hloc
  have htime₀ : circleParabolicSegmentTime τ hτ 0 0=0 := by
    apply Subtype.ext
    norm_num [circleParabolicSegmentTime]
  have hu₀ : circleParabolicCurve T τ (U 0) 0=u 0 :=
    (hrep 0 0).symm.trans (congrArg u htime₀)
  have hclip : projIcc (0:ℝ) 1 zero_le_one 0=(0:unitInterval) :=
    projIcc_of_mem zero_le_one ⟨le_rfl,zero_le_one⟩
  let H₀ : ℝ → ℝ := fun s => value (circleParabolicCurve T τ (U 0)
    (projIcc (0:ℝ) 1 zero_le_one 0)) s
  have hH₀ : H₀=h 0 := by
    dsimp only [H₀,h]
    rw [hclip,hu₀]
    simp only [Real.toNNReal_zero]
  have hD₀ (s : ℝ) : Real.sqrt 2*(circleSobolevClassicalJet T 4
      (W₀ (projIcc (0:ℝ) 1 zero_le_one 0)) 1 ((Real.sqrt 2*s):AddCircle T)).re=d₀ s := by
    rw [hclip]
  have hΩzero : Ω₀ (projIcc (0:ℝ) 1 zero_le_one 0)=ω 0 :=
    (congrArg Ω₀ hclip).trans hω₀.symm
  have hinitial (s : ℝ) :
      HasDerivAt (h 0) (d₀ s) s ∧ 0<1-k s*h 0 s ∧
      HasDerivWithinAt (fun z : ℝ => h z s)
        (normalGraphFlowRHS β n k (h 0) (15/2) s-
          ω 0*((conj (t s)*β s).re+((conj (t s)*β s).im+h 0 s)*d₀ s/(1-k s*h 0 s)))
        (Ici (0:ℝ)) 0 := by
    have hs := hloc 0 le_rfl zero_le_one s
    have hspace : HasDerivAt (h 0) (d₀ s) s := by
      simpa only [← hH₀,← hD₀ s,H₀,value] using! hs.1
    have hreg : 0<1-k s*h 0 s := by
      simpa only [← hH₀,H₀,value,k,φ] using! hs.2.1
    let F : (ℝ → ℝ) → ℝ → ℝ → ℝ := fun H D A =>
      normalGraphFlowRHS β n k H (15/2) s-
        A*((conj (t s)*β s).re+((conj (t s)*β s).im+H s)*D/(1-k s*H s))
    let D := Real.sqrt 2*(circleSobolevClassicalJet T 4
      (W₀ (projIcc (0:ℝ) 1 zero_le_one 0)) 1 ((Real.sqrt 2*s):AddCircle T)).re
    let A := Ω₀ (projIcc (0:ℝ) 1 zero_le_one 0)
    have hscalar : F H₀ D A=F (h 0) (d₀ s) (ω 0) :=
      (congrArg (fun H => F H D A) hH₀).trans
        ((congrArg (fun D => F (h 0) D A) (hD₀ s)).trans
          (congrArg (F (h 0) (d₀ s)) hΩzero))
    have htime : HasDerivWithinAt
        (fun r : ℝ => value (circleParabolicCurve T τ (U 0)
          (projIcc (0:ℝ) 1 zero_le_one r)) s)
        (τ • F (h 0) (d₀ s) (ω 0)) (Icc (0:ℝ) 1) 0 := by
      apply hs.2.2.congr_deriv
      exact congrArg (τ*·) hscalar
    exact ⟨hspace,hreg,circle_initial_classical_time_derivative τ hτ
      (fun f => value f s) u (circleParabolicCurve T τ (U 0))
      (F (h 0) (d₀ s) (ω 0)) (hrep 0) htime⟩
  intro σ hσ s
  rcases eq_or_lt_of_le hσ with hz | ht
  · subst σ
    simpa only [h₁,dif_neg (lt_irrefl (0:ℝ))] using! hinitial s
  · have hp := hpos σ ht s
    have hd : HasDerivWithinAt (fun z : ℝ => h z s)
        (normalGraphFlowRHS β n k (h σ) (15/2) s-
          ω σ*((conj (t s)*β s).re+((conj (t s)*β s).im+h σ s)*h₁ σ s/(1-k s*h σ s)))
        (Ici (0:ℝ)) σ := by
      simpa only [h,h₁,value,dif_pos ht,β,n,k,t,φ] using! hp.2.2.hasDerivWithinAt
    exact ⟨by simpa only [h,h₁,value,dif_pos ht] using! hp.1,
      by simpa only [h,value,k,φ] using! hp.2.1,hd⟩

end Lemniscate
