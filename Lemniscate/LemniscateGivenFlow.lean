import Lemniscate.BernoulliRestartLocalFlowChart
import Lemniscate.BernoulliNormalizedFlowFamilies
import Lemniscate.BernoulliGlobalFlowIdentification

/-! Identification of a given geometric flow with the actual global
normal graph. The common radius is chosen from the profile first. -/
noncomputable section
namespace Lemniscate
open Complex Set Filter MeasureTheory CoarseArithmetic
open scoped ContDiff Topology NNReal ENNReal ComplexConjugate

private theorem oriented_normalization_iff
    (γ ζ : ℝ → ℂ) (P Q : ℝ) (p r : ℂ) (hr : r≠0) :
    OrientedCurveEquivalent (fun s => (γ s-p)/r) (fun s => (ζ s-p)/r) P Q ↔
      OrientedCurveEquivalent γ ζ P Q := by
  constructor
  · rintro ⟨χ,hχ,hi,hd,he⟩
    refine ⟨χ,hχ,hi,hd,?_⟩
    intro s
    have hh : γ (χ s)-p=ζ s-p := (div_left_inj' hr).mp (he s)
    calc
      γ (χ s)=(γ (χ s)-p)+p := (sub_add_cancel _ _).symm
      _=(ζ s-p)+p := congrArg (fun w : ℂ => w+p) hh
      _=ζ s := sub_add_cancel _ _
  · rintro ⟨χ,hχ,hi,hd,he⟩
    refine ⟨χ,hχ,hi,hd,?_⟩
    intro s
    exact congrArg (fun z : ℂ => (z-p)/r) (he s)

private theorem given_flow_affine_division (p r z : ℂ) (hr : r≠0) :
    (p+r*z-p)/r=z := by
  field_simp [hr]
  ring

private abbrev GivenFlowConclusion
    (S : ℝ) [Fact (0<S)] (e : ℝ ≃o ℝ) (q p : C(AddCircle S,ℂ)) (ψ : CircleL2 S)
    (η : ℝ) : Prop :=
  ∀ τ : ℝ,∀ hτ : 0<τ,∀ x₀ : CircleSobolevSpace S 2,
    ∀ D : BernoulliNormalGraphEvolution S q p ψ τ hτ η x₀,
    ∀ h₀ : ℝ → ℝ,∀ hh₀ : ContDiff ℝ ∞ h₀,∀ hp₀ : Function.Periodic h₀ S,
    circleSobolevCoordinate S 2 0 x₀=circleContinuousL2 S
      (periodicCircleFunction S (fun x : ℝ => (h₀ x:ℂ))
        (fun x => congrArg Complex.ofReal (hp₀ x))
        (Complex.continuous_ofReal.comp hh₀.continuous)) →
    ∀ a : ℝ,0<a → ∀ p₀ : ℂ,∀ α : ℝ,∀ ρ : ℝ → ℝ,
    (∀ t : ℝ,0≤t → 0<ρ t ∧ ρ t=(a^4+30*t)^(1/4:ℝ)) →
    let β := fun s : ℝ => bernoulliCurve (e.symm (Real.sqrt 2*s))
    let ν := fun s : ℝ => I*(bernoulliVelocity (e.symm (Real.sqrt 2*s))/
      (‖bernoulliVelocity (e.symm (Real.sqrt 2*s))‖:ℂ))
    let h := fun σ s : ℝ => (circleSobolevH1Embedding S
      (circleSobolevInclusion S 1 (D.u (Real.toNNReal σ))))
        ((Real.sqrt 2*s):AddCircle S) |>.re
    let Core := fun t s : ℝ => p₀+(ρ t:ℂ)*
      (Complex.exp (((α+D.theta (normalizedTime a t)):ℂ)*I)*
        normalGraphCurve β ν (h (normalizedTime a t)) s)
    (∀ t : ℝ,0≤t → ContDiff ℝ ∞ (Core t)) → IsFreeElasticFlow Core →
    ∀ P : ℝ,0<P → ∀ Y : ℝ → ℝ → ℂ,
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Y z.1 z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) →
    (∀ t : ℝ,0≤t → Function.Periodic (Y t) P) → IsFreeElasticFlow Y →
    OrientedCurveEquivalent (Y 0) (Core 0) P (S/Real.sqrt 2) →
    ∀ t : ℝ,0≤t → OrientedCurveEquivalent (Y t) (Core t) P (S/Real.sqrt 2)

variable (T S : ℝ) [Fact (0<T)] [Fact (0<S)]

set_option maxHeartbeats 1200000 in
/-- A single profile-dependent radius identifies every given smooth
free elastic flow with the constructed physical normal graph at all
times. All local charts and the required low-H2 uniqueness are supplied
by the actual restart theorem, rather than assumed of the given flow. -/
theorem lemniscate_given_flow_identification
    (e : ℝ ≃o ℝ)
    (he : ∀ u,e u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    (hT : T=e (2*Real.pi)) (q p : C(AddCircle T,ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (hE : ∀ x,2*(p x)^2+(q x)^4=1)
    (hqlift : ∀ x : ℝ,q (x:AddCircle T)=(bernoulliProfileQ (e.symm x):ℂ))
    (hplift : ∀ x : ℝ,p (x:AddCircle T)=(bernoulliProfileP (e.symm x):ℂ))
    (hqreal : ∀ x,conj (q x)=q x) (hpreal : ∀ x,conj (p x)=p x)
    (hs : ∀ n : ℤ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (-n)=
      fourierCoeff (q^2:C(AddCircle T,ℂ)) n)
    (hc : ∀ j : ℕ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (2*(j:ℤ))=
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (2*n+1)=0)
    (hr : (2*Real.pi/T)^2=lemniscateFrequencySquared)
    (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p)=1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ=0)
    (M : ℕ) (hM : 0<M) (hS : S=(M:ℝ)*T) :
    let Q := circlePeriodicExtension T S M hS q
    let P := circlePeriodicExtension T S M hS p
    let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
    ∃ η>0,GivenFlowConclusion S e Q P (Ψ:CircleL2 S) η := by
  dsimp only
  let Q := circlePeriodicExtension T S M hS q
  let R := circlePeriodicExtension T S M hS p
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  have hdata := (paper_periodic_cover_modulated_tame_data T S q p hq hp hE
    hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS).2.2
  obtain ⟨hB,hBper,hN,hNper⟩ := bernoulli_reference_profile_geometry T S e he hT
    q p hq hqlift M hS (Ψ:CircleL2 S) hdata.2.1
  obtain ⟨η,hη,hRestart⟩ := bernoulli_restart_local_flow_chart T S e he hT q p hq hp hE
    hqlift hplift hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS
  refine ⟨η,hη,?_⟩
  intro τ hτ x₀ D h₀ hh₀ hp₀ hvalue a ha p₀ α ρ hρ
  dsimp only
  intro hCoreSmooth hCoreFlow P hP Y hY hYper hFlow hInitial
  let β := fun s : ℝ => bernoulliCurve (e.symm (Real.sqrt 2*s))
  let ν := fun s : ℝ => I*(bernoulliVelocity (e.symm (Real.sqrt 2*s))/
    (‖bernoulliVelocity (e.symm (Real.sqrt 2*s))‖:ℂ))
  let h := fun σ s : ℝ => (circleSobolevH1Embedding S
    (circleSobolevInclusion S 1 (D.u (Real.toNNReal σ))))
      ((Real.sqrt 2*s):AddCircle S) |>.re
  let Core := fun t s : ℝ => p₀+(ρ t:ℂ)*
    (Complex.exp (((α+D.theta (normalizedTime a t)):ℂ)*I)*
      normalGraphCurve β ν (h (normalizedTime a t)) s)
  have hβ : ContDiff ℝ ∞ β := hB.comp (contDiff_const.mul contDiff_id)
  have hν : ContDiff ℝ ∞ ν := hN.comp (contDiff_const.mul contDiff_id)
  have hβper : Function.Periodic β (S/Real.sqrt 2) := by
    simpa only [β,div_eq_mul_inv,mul_comm] using! hBper.const_mul (Real.sqrt 2)
  have hνper : Function.Periodic ν (S/Real.sqrt 2) := by
    simpa only [ν,div_eq_mul_inv,mul_comm] using! hNper.const_mul (Real.sqrt 2)
  have htime (σ : ℝ≥0) : 0≤physicalTime a (σ:ℝ) :=
    ((physical_time_inverse a ha).2.1 (σ:ℝ)).2.2.1 σ.property
  have hscale (σ : ℝ≥0) : 0<ρ (physicalTime a (σ:ℝ)) := (hρ _ (htime σ)).1
  have hYreg (t : ℝ) (ht : 0≤t) (s : ℝ) : deriv (Y t) s≠0 :=
    (Classical.choose_spec (hFlow t ht s)).2.1
  have hCreg (t : ℝ) (ht : 0≤t) (s : ℝ) : deriv (Core t) s≠0 :=
    (Classical.choose_spec (hCoreFlow t ht s)).2.1
  let X : ℝ≥0 × ℝ → ℂ := fun z =>
    (Y (physicalTime a (z.1:ℝ)) z.2-p₀)/(ρ (physicalTime a (z.1:ℝ)):ℂ)
  let Z : ℝ≥0 × ℝ → ℂ := fun z => Complex.exp (((α+D.theta (z.1:ℝ)):ℂ)*I)*
    (β z.2+((circleSobolevH1Embedding S (circleSobolevInclusion S 1 (D.u z.1))
      ((Real.sqrt 2*z.2):AddCircle S)).re:ℂ)*ν z.2)
  have hphysical (σ : ℝ≥0) (s : ℝ) : Core (physicalTime a (σ:ℝ)) s=
      p₀+(ρ (physicalTime a (σ:ℝ)):ℂ)*Z (σ,s) := by
    have hc := ((physical_time_inverse a ha).2.1 (σ:ℝ)).1
    dsimp only [Core,h,normalGraphCurve,Z]
    rw [hc,Real.toNNReal_coe]
  have hnormalized (σ : ℝ≥0) (s : ℝ) :
      (Core (physicalTime a (σ:ℝ)) s-p₀)/(ρ (physicalTime a (σ:ℝ)):ℂ)=Z (σ,s) := by
    rw [hphysical]
    exact given_flow_affine_division _ _ _ (Complex.ofReal_ne_zero.mpr (hscale σ).ne')
  obtain ⟨hX,hXv,hXs,hXreg,hXper⟩ := normalized_physical_flow_family_regularity a ha ρ
    (fun t ht => (hρ t ht).2) (fun z : ℝ × ℝ => Y z.1 z.2) hY hYreg P hYper p₀
  obtain ⟨hZ,hZv,hZs,hZreg,hZper⟩ := bernoulli_normal_graph_family_regularity S Q R
    (Ψ:CircleL2 S) τ hτ η x₀ D a ha α ρ p₀ hscale β ν hβ hν hβper hνper
      Core hCoreSmooth hCreg hphysical
  have hInitialNormalized : OrientedCurveEquivalent (fun s => X (0,s))
      (fun s => Z (0,s)) P (S/Real.sqrt 2) := by
    have ht₀ : physicalTime a 0=0 := (physical_time_inverse a ha).1
    have hx₀ : (fun s => X (0,s))=(fun s => (Y 0 s-p₀)/(ρ 0:ℂ)) := by
      funext s
      simp only [X,NNReal.coe_zero,ht₀]
    have hz₀ : (fun s => Z (0,s))=(fun s => (Core 0 s-p₀)/(ρ 0:ℂ)) := by
      funext s
      simpa only [NNReal.coe_zero,ht₀] using (hnormalized 0 s).symm
    rw [hx₀,hz₀]
    exact (oriented_normalization_iff (Y 0) (Core 0) P (S/Real.sqrt 2)
      p₀ (ρ 0:ℂ) (Complex.ofReal_ne_zero.mpr (hρ 0 le_rfl).1.ne')).mpr hInitial
  have hAll : ∀ σ : ℝ≥0,OrientedCurveEquivalent (fun s => X (σ,s)) (fun s => Z (σ,s))
      P (S/Real.sqrt 2) := by
    apply bernoulli_global_flow_identification S e Q R (Ψ:CircleL2 S) τ hτ η x₀ D
      a ha α ρ p₀ Y P hP X Z hX hZ hXv hZv hXs hZs hXreg hZreg hXper hZper hscale
      (fun _ _ => rfl) (fun _ _ => rfl) hRestart.2.2.2.1 ?_ hInitialNormalized
    intro σ₀ χ₀ hχ hi hd heq
    apply hRestart.2.2.2.2 τ hτ x₀ D h₀ hh₀ hp₀ hvalue a ha α ρ hρ p₀ P Y hY hYper
      hFlow σ₀ χ₀ hχ hi hd
    intro s
    exact heq s
  intro t ht
  have hσ : 0≤normalizedTime a t := by
    obtain ⟨_,_,_,hclock,_,_⟩ := physical_normalization a ha
    exact (hclock t ht).2.2.1
  let σ : ℝ≥0 := ⟨normalizedTime a t,hσ⟩
  have hclock : physicalTime a (σ:ℝ)=t := (physical_time_inverse a ha).2.2 t ht
  have hx : (fun s => X (σ,s))=(fun s => (Y t s-p₀)/(ρ t:ℂ)) := by
    funext s
    dsimp only [X]
    rw [hclock]
  have hz : (fun s => Z (σ,s))=(fun s => (Core t s-p₀)/(ρ t:ℂ)) := by
    funext s
    simpa only [hclock] using (hnormalized σ s).symm
  have hh := hAll σ
  rw [hx,hz] at hh
  exact (oriented_normalization_iff (Y t) (Core t) P (S/Real.sqrt 2)
    p₀ (ρ t:ℂ) (Complex.ofReal_ne_zero.mpr (hρ t ht).1.ne')).mp hh

end Lemniscate
