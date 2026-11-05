import Lemniscate.BernoulliParabolicClassicalEquation
import Lemniscate.PeriodicParabolicGlobalClassicalTime

/-! The classical height equation on the whole positive normalized-time
axis, obtained from the actual overlapping parabolic solutions. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Set
open scoped Topology NNReal ComplexConjugate

private theorem global_classical_radius {P : ℝ → Prop} {Q : Prop}
    (h : ∃ δ>0, P δ) (k : ∀ δ, 0<δ → P δ → Q) : Q := by
  obtain ⟨δ,hδ,hP⟩ := h
  exact k δ hδ hP

variable (T : ℝ) [Fact (0<T)]

set_option maxHeartbeats 1200000 in
/-- The global MR solution satisfies the actual classical Bernoulli
normal-height equation at every positive normalized time. -/
theorem bernoulli_global_classical_equation
    (e : ℝ ≃o ℝ)
    (he : ∀ u, e u=∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    (q p : C(AddCircle T,ℂ))
    (hq : ∀ x : ℝ, q (x:AddCircle T)=(bernoulliProfileQ (e.symm x):ℂ))
    (hp : ∀ x : ℝ, p (x:AddCircle T)=(bernoulliProfileP (e.symm x):ℂ))
    (ψ : CircleL2 T) :
    ∃ δ>0, ∀ τ : ℝ, ∀ hτ : 0<τ,
      ∀ u : C(ℝ≥0,CircleSobolevSpace T 2),
      ∀ U : ℕ → CircleParabolicSpace T τ,
      ∀ w : C(Ioi (0:ℝ),CircleSobolevSpace T 5), ∀ ω : ℝ → ℝ,
      (∀ n, ‖circleParabolicCurve T τ (U n)‖<δ) →
      (∀ n r, u (circleParabolicSegmentTime τ hτ n r)=circleParabolicCurve T τ (U n) r) →
      (∀ t : ℝ≥0, 0<t → ∃ (n : ℕ) (r : unitInterval),
        0<(r:ℝ) ∧ (r:ℝ)<1 ∧ circleParabolicSegmentTime τ hτ n r=t) →
      (∀ t : Ioi (0:ℝ), circleSobolevInclusion T 2
        (circleSobolevInclusion T 3 (circleSobolevInclusion T 4 (w t)))=
          u ⟨(t:ℝ),t.property.le⟩) →
      (∀ t : ℝ≥0, circleSobolevConjugation T 2 (u t)=u t) →
      ContinuousOn ω (Ioi (0:ℝ)) →
      (∀ t : Ioi (0:ℝ), (ω t:ℂ)=circleNormalGraphAngularVelocity T
        (circleBernoulliBackground T q p) (15/2) ψ (circleSobolevInclusion T 4 (w t))) →
      (∀ n, ∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ (U n) r=
        circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
          (circleParabolicH4 T τ (U n) r)) →
      let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
      let β := bernoulliCurve ∘ φ
      let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
      let n := fun s : ℝ => I*t s
      let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
      let h : ℝ → ℝ → ℝ := fun σ s => (circleSobolevH1Embedding T
        (circleSobolevInclusion T 1 (u (Real.toNNReal σ))) ((Real.sqrt 2*s):AddCircle T)).re
      let h₁ : ℝ → ℝ → ℝ := fun σ s => if hs : 0<σ then Real.sqrt 2*
        (circleSobolevClassicalJet T 4 (w ⟨σ,hs⟩) 1 ((Real.sqrt 2*s):AddCircle T)).re else 0
      ∀ σ : ℝ, 0<σ → ∀ s : ℝ,
        HasDerivAt (h σ) (h₁ σ s) s ∧ 0<1-k s*h σ s ∧
        HasDerivAt (fun z : ℝ => h z s)
          (normalGraphFlowRHS β n k (h σ) (15/2) s-
            ω σ*((conj (t s)*β s).re+
              ((conj (t s)*β s).im+h σ s)*h₁ σ s/(1-k s*h σ s))) σ := by
  refine global_classical_radius
    (bernoulli_parabolic_classical_equation T e he q p hq hp ψ) ?_
  intro δ hδ hlocal
  refine ⟨δ,hδ,?_⟩
  intro τ hτ u U w ω hU hrep hcover hw hreal hωcont hω hPDE
  dsimp only
  let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
  let β := bernoulliCurve ∘ φ
  let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
  let n := fun s : ℝ => I*t s
  let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
  let value : CircleSobolevSpace T 2 → ℝ → ℝ := fun f s =>
    (circleSobolevH1Embedding T (circleSobolevInclusion T 1 f)
      ((Real.sqrt 2*s):AddCircle T)).re
  let h : ℝ → ℝ → ℝ := fun σ => value (u (Real.toNNReal σ))
  let h₁ : ℝ → ℝ → ℝ := fun σ s => if hs : 0<σ then Real.sqrt 2*
    (circleSobolevClassicalJet T 4 (w ⟨σ,hs⟩) 1 ((Real.sqrt 2*s):AddCircle T)).re else 0
  let v : ℝ → ℝ → ℝ := fun σ s => normalGraphFlowRHS β n k (h σ) (15/2) s-
    ω σ*((conj (t s)*β s).re+((conj (t s)*β s).im+h σ s)*h₁ σ s/(1-k s*h σ s))
  have hchart (m : ℕ) (r : unitInterval) (hr0 : 0<(r:ℝ)) (hr1 : (r:ℝ)<1) :
      (∀ s : ℝ, HasDerivAt (h (circleParabolicSegmentTime τ hτ m r))
        (h₁ (circleParabolicSegmentTime τ hτ m r) s) s ∧
          0<1-k s*h (circleParabolicSegmentTime τ hτ m r) s) ∧
      (∀ s : ℝ, HasDerivAt
        (fun z : ℝ => value (circleParabolicCurve T τ (U m)
          (projIcc (0:ℝ) 1 zero_le_one z)) s)
        (τ*v (circleParabolicSegmentTime τ hτ m r) s) (r:ℝ)) := by
    let r₀ : ℝ := (r:ℝ)/2
    have hr₀ : 0<r₀ := half_pos hr0
    have hr₀r : r₀<(r:ℝ) := by dsimp only [r₀]; linarith only [hr0]
    have hr₀1 : r₀<1 := hr₀r.trans hr1
    let unitTime : Icc r₀ (1:ℝ) → unitInterval := fun z =>
      ⟨(z:ℝ),(hr₀.trans_le z.property.1).le,z.property.2⟩
    let chart : Icc r₀ (1:ℝ) → Ioi (0:ℝ) := fun z =>
      ⟨τ*((m:ℝ)/2+(z:ℝ)),mul_pos hτ
        (add_pos_of_nonneg_of_pos (by positivity) (hr₀.trans_le z.property.1))⟩
    have hchartcont : Continuous chart := by
      apply Continuous.subtype_mk
      exact continuous_const.mul (continuous_const.add continuous_subtype_val)
    let W : C(Icc r₀ (1:ℝ),CircleSobolevSpace T 5) := w.comp ⟨chart,hchartcont⟩
    let Ω : C(Icc r₀ (1:ℝ),ℝ) :=
      ⟨fun z => ω (chart z),
        (continuousOn_iff_continuous_domRestrict.mp hωcont).comp hchartcont⟩
    have hW (z : Icc r₀ (1:ℝ)) : circleSobolevInclusion T 2
        (circleSobolevInclusion T 3 (circleSobolevInclusion T 4 (W z)))=
          circleParabolicCurve T τ (U m) (unitTime z) :=
      (hw (chart z)).trans (hrep m (unitTime z))
    have hR (z : unitInterval) :
        circleSobolevConjugation T 2 (circleParabolicCurve T τ (U m) z)=
          circleParabolicCurve T τ (U m) z :=
      (congrArg (circleSobolevConjugation T 2) (hrep m z).symm).trans
        ((hreal _).trans (hrep m z))
    have hΩ (z : Icc r₀ (1:ℝ)) : (Ω z:ℂ)=circleNormalGraphAngularVelocity T
        (circleBernoulliBackground T q p) (15/2) ψ (circleSobolevInclusion T 4 (W z)) :=
      hω (chart z)
    have hL := hlocal τ hτ (U m) (hU m) r₀ hr₀.le hr₀1 W hW hR Ω hΩ (hPDE m)
    dsimp only at hL
    let σ : ℝ := circleParabolicSegmentTime τ hτ m r
    have hσ : 0<σ := mul_pos hτ
      (add_pos_of_nonneg_of_pos (by positivity) hr0)
    have hheight : (fun s : ℝ => value (circleParabolicCurve T τ (U m)
        (projIcc (0:ℝ) 1 zero_le_one (r:ℝ))) s)=h σ := by
      rw [projIcc_of_mem zero_le_one r.property]
      change value (circleParabolicCurve T τ (U m) r)=value (u (Real.toNNReal σ))
      exact congrArg value ((hrep m r).symm.trans (congrArg u (Subtype.ext
        (Real.coe_toNNReal σ hσ.le).symm)))
    have hjet (s : ℝ) : Real.sqrt 2*(circleSobolevClassicalJet T 4
        (W (projIcc r₀ 1 hr₀1.le (r:ℝ))) 1 ((Real.sqrt 2*s):AddCircle T)).re=h₁ σ s := by
      rw [projIcc_of_mem hr₀1.le ⟨hr₀r.le,r.property.2⟩]
      simp only [h₁,dif_pos hσ]
      rfl
    have hangle : Ω (projIcc r₀ 1 hr₀1.le (r:ℝ))=ω σ := by
      rw [projIcc_of_mem hr₀1.le ⟨hr₀r.le,r.property.2⟩]
      rfl
    constructor
    · intro s
      have hs := hL (r:ℝ) hr₀r.le hr1.le s
      have hspace : HasDerivAt (h σ) (h₁ σ s) s := by
        simpa only [← hheight,← hjet s,value] using! hs.1
      have hreg : 0<1-k s*h σ s := by
        simpa only [← hheight,value,k,φ] using! hs.2.1
      exact ⟨hspace,hreg⟩
    · intro s
      have hs := ((hL (r:ℝ) hr₀r.le hr1.le s).2.2).hasDerivAt (Icc_mem_nhds hr₀r hr1)
      apply hs.congr_deriv
      let F : (ℝ → ℝ) → ℝ → ℝ → ℝ := fun H D A =>
        τ*(normalGraphFlowRHS β n k H (15/2) s-
          A*((conj (t s)*β s).re+((conj (t s)*β s).im+H s)*D/(1-k s*H s)))
      let H := fun x : ℝ => value (circleParabolicCurve T τ (U m)
        (projIcc (0:ℝ) 1 zero_le_one (r:ℝ))) x
      let D := Real.sqrt 2*(circleSobolevClassicalJet T 4
        (W (projIcc r₀ 1 hr₀1.le (r:ℝ))) 1 ((Real.sqrt 2*s):AddCircle T)).re
      let A := Ω (projIcc r₀ 1 hr₀1.le (r:ℝ))
      change F H D A=F (h σ) (h₁ σ s) (ω σ)
      exact (congrArg (fun H => F H D A) hheight).trans
        ((congrArg (fun D => F (h σ) D A) (hjet s)).trans
          (congrArg (F (h σ) (h₁ σ s)) hangle))
  have htime (σ : ℝ) (hσ : 0<σ) (s : ℝ) : HasDerivAt (fun z => h z s) (v σ s) σ := by
    apply circle_global_classical_time_derivative τ hτ (fun f => value f s) u
      (fun m => circleParabolicCurve T τ (U m)) (fun z => v z s) hrep hcover
        (fun m r hr0 hr1 => (hchart m r hr0 hr1).2 s) σ hσ
  intro σ hσ s
  obtain ⟨m,r,hr0,hr1,hr⟩ := hcover (Real.toNNReal σ) (Real.toNNReal_pos.mpr hσ)
  have heq : (circleParabolicSegmentTime τ hτ m r:ℝ)=σ :=
    (congrArg (fun x : ℝ≥0 => (x:ℝ)) hr).trans (Real.coe_toNNReal σ hσ.le)
  have hs := (hchart m r hr0 hr1).1 s
  rw [heq] at hs
  exact ⟨hs.1,hs.2,htime σ hσ s⟩

end Lemniscate
