import Lemniscate.BernoulliLocalFlowIdentification
import Lemniscate.OrientedCurveOrbitClosed
import Lemniscate.NormalGraphOrientedParameterChange
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace Lemniscate
open Complex Set Filter MeasureTheory
open scoped ContDiff Topology NNReal ENNReal ComplexConjugate

private theorem normalize_affine_curve
    (y p r z : ℂ) (hr : r≠0) (hy : y=p+r*z) : (y-p)/r=z := by
  rw [hy]
  field_simp [hr]
  <;> ring

variable (T : ℝ) [Fact (0<T)]

set_option maxHeartbeats 1200000 in
/-- The actual local charts and forward parabolic uniqueness identify a
given free elastic flow with the global normal graph at every time, up to
a smooth oriented parameter change. Closedness uses only joint continuity
of positions and spatial velocities, and no backward uniqueness is used. -/
theorem bernoulli_global_flow_identification
    (e : ℝ ≃o ℝ) (q p : C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (τ : ℝ) (hτ : 0<τ) (η : ℝ) (z₀ : CircleSobolevSpace T 2)
    (D : BernoulliNormalGraphEvolution T q p ψ τ hτ η z₀)
    (a : ℝ) (ha : 0<a) (α : ℝ) (ρ : ℝ → ℝ) (p₀ : ℂ)
    (Y : ℝ → ℝ → ℂ) (P : ℝ) (hP : 0<P)
    (X Z : ℝ≥0 × ℝ → ℂ)
    (hX : Continuous X) (hZ : Continuous Z)
    (hXv : Continuous (fun z : ℝ≥0 × ℝ => deriv (fun s => X (z.1,s)) z.2))
    (hZv : Continuous (fun z : ℝ≥0 × ℝ => deriv (fun s => Z (z.1,s)) z.2))
    (hXs : ∀ σ,ContDiff ℝ ∞ (fun s => X (σ,s)))
    (hZs : ∀ σ,ContDiff ℝ ∞ (fun s => Z (σ,s)))
    (hXreg : ∀ σ s,deriv (fun u => X (σ,u)) s≠0)
    (hZreg : ∀ σ s,deriv (fun u => Z (σ,u)) s≠0)
    (hXper : ∀ σ,Function.Periodic (fun s => X (σ,s)) P)
    (hZper : ∀ σ,Function.Periodic (fun s => Z (σ,s)) (T/Real.sqrt 2))
    (hρ : ∀ σ : ℝ≥0,0<ρ (physicalTime a (σ:ℝ)))
    (hXvalue : ∀ σ : ℝ≥0,∀ s,
      X (σ,s)=(Y (physicalTime a (σ:ℝ)) s-p₀)/(ρ (physicalTime a (σ:ℝ)):ℂ))
    (hZvalue : ∀ σ : ℝ≥0,∀ s,
      Z (σ,s)=Complex.exp (((α+D.theta (σ:ℝ)):ℂ)*I)*
        (bernoulliCurve (e.symm (Real.sqrt 2*s))+
          ((circleSobolevH1Embedding T (circleSobolevInclusion T 1 (D.u σ))
            ((Real.sqrt 2*s):AddCircle T)).re:ℂ)*
            (I*bernoulliAuxiliaryTangent e (Real.sqrt 2*s))))
    (hunique : ∀ d : ℝ,0<d → ∀ R V : CircleParabolicSpace T d,
      circleParabolicInitialValue T d R=circleParabolicInitialValue T d V →
      ‖circleParabolicCurve T d R‖<η → ‖circleParabolicCurve T d V‖<η →
      (∀ᵐ r : unitInterval ∂volume,circleParabolicTimeDerivative T d R r=
        circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
          (circleParabolicH4 T d R r)) →
      (∀ᵐ r : unitInterval ∂volume,circleParabolicTimeDerivative T d V r=
        circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
          (circleParabolicH4 T d V r)) → R=V)
    (hchart : ∀ (σ₀ : ℝ≥0) (χ₀ : ℝ ≃o ℝ),
      ContDiff ℝ ∞ (χ₀ : ℝ → ℝ) → ContDiff ℝ ∞ (χ₀.symm : ℝ → ℝ) →
      (∀ s,χ₀ (s+T/Real.sqrt 2)=χ₀ s+P) →
      (∀ s,X (σ₀,χ₀ s)=Z (σ₀,s)) →
      Nonempty (BernoulliLocalFlowChart T e q p ψ η (D.u σ₀)
        a (σ₀:ℝ) (α+D.theta (σ₀:ℝ)) ρ p₀ χ₀ Y))
    (hinitial : OrientedCurveEquivalent (fun s => X (0,s)) (fun s => Z (0,s))
      P (T/Real.sqrt 2)) :
    ∀ σ : ℝ≥0,OrientedCurveEquivalent (fun s => X (σ,s)) (fun s => Z (σ,s))
      P (T/Real.sqrt 2) := by
  have hsqrt : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hℓ : 0<T/Real.sqrt 2 := div_pos Fact.out hsqrt
  have hscale : T=Real.sqrt 2*(T/Real.sqrt 2) := by
    field_simp [hsqrt.ne']
    <;> ring
  let E : Set ℝ≥0 := {σ | OrientedCurveEquivalent
    (fun s => X (σ,s)) (fun s => Z (σ,s)) P (T/Real.sqrt 2)}
  have hclosed : IsClosed E := isClosed_oriented_curve_equivalent
    P (T/Real.sqrt 2) hP hℓ X Z hX hZ hXv hZv hXs hZs hXreg hZreg hXper hZper
  have hforward (σ₀ : ℝ≥0) (hσ₀ : σ₀∈E) :
      ∃ δ : ℝ≥0,0<δ ∧ ∀ σ∈Icc σ₀ (σ₀+δ),σ∈E := by
    refine Exists.elim hσ₀ ?_
    intro χ₀ hχ
    let C := Classical.choice (hchart σ₀ χ₀ hχ.1 hχ.2.1 hχ.2.2.1 hχ.2.2.2)
    refine Exists.elim (bernoulli_local_flow_identification T e q p ψ τ hτ η z₀ D
      σ₀ a (α+D.theta (σ₀:ℝ)) ρ p₀ χ₀ Y C hunique) ?_
    intro d hdata
    have hd : 0<d := hdata.1
    have hdtime : d<C.timeRadius := hdata.2.1.trans C.comparisonShort
    have hidentity := hdata.2.2
    refine ⟨⟨d,hd.le⟩,hd,?_⟩
    intro σ hσ
    let r : ℝ := (σ:ℝ)-(σ₀:ℝ)
    have hr₀ : 0≤r := sub_nonneg.mpr hσ.1
    have hrd : r≤d := by
      have hh : (σ:ℝ)≤(σ₀:ℝ)+d := hσ.2
      dsimp only [r]
      linarith only [hh]
    have hr : r∈Ico (0:ℝ) C.timeRadius := ⟨hr₀,hrd.trans_lt hdtime⟩
    have hclock : (σ₀:ℝ)+r=(σ:ℝ) := by dsimp only [r]; ring
    have hlow : circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (C.high r))=
        D.u σ := by
      have hh := (hidentity r ⟨hr₀,hrd⟩).1
      simpa only [hclock,Real.toNNReal_coe] using! hh
    have hangle : α+D.theta (σ₀:ℝ)+C.angle r=α+D.theta (σ:ℝ) := by
      have hh := (hidentity r ⟨hr₀,hrd⟩).2
      rw [hclock] at hh
      linarith only [hh]
    have hheight : C.jet r 0=circleSobolevH1Embedding T
        (circleSobolevInclusion T 1 (D.u σ)) := by
      apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
      change circleContinuousL2 T (C.jet r 0)=circleContinuousL2 T
        (circleSobolevH1Embedding T (circleSobolevInclusion T 1 (D.u σ)))
      rw [circle_sobolev_h1_embedding_l2]
      exact (C.coordinates r hr 0).symm.trans
        (congrArg (circleSobolevCoordinate T 2 0) hlow)
    have hgraph (s : ℝ) :
        X (σ,χ₀ (C.chiAux ((r,C.angle r),Real.sqrt 2*s)/Real.sqrt 2))=Z (σ,s) := by
      rw [hXvalue,hZvalue]
      have hh := C.physicalGraph r hr s
      have hangleC : ((α+D.theta (σ₀:ℝ):ℝ):ℂ)+(C.angle r:ℂ)=
          (α:ℂ)+(D.theta (σ:ℝ):ℂ) := by
        simpa only [Complex.ofReal_add] using congrArg Complex.ofReal hangle
      rw [hclock,hangleC,hheight] at hh
      exact normalize_affine_curve _ _ _ _
        (Complex.ofReal_ne_zero.mpr (hρ σ).ne') hh
    refine Exists.elim C.chiBound ?_
    intro R hR
    exact normal_graph_oriented_parameter_change T (T/Real.sqrt 2) P (Real.sqrt 2) R
      hℓ hsqrt hscale (fun x => C.chiAux ((r,C.angle r),x)) (C.chiSmooth r hr)
      (C.chiDeck r hr) (C.chiPositive r hr) (hR r hr) χ₀ hχ.1 hχ.2.1 hχ.2.2.1
      (fun s => X (σ,s)) (fun s => Z (σ,s)) hgraph
  intro σ
  change σ∈E
  apply (hclosed.inter isClosed_Icc).mem_of_ge_of_forall_exists_gt hinitial
    (show (0:ℝ≥0)≤σ from zero_le)
  intro t ht
  obtain ⟨δ,hδ,hstep⟩ := hforward t ht.1
  let u : ℝ≥0 := min (t+δ) σ
  have htu : t<u := lt_min (lt_add_of_pos_right t hδ) ht.2.2
  exact ⟨u,hstep u ⟨htu.le,min_le_left _ _⟩,htu,min_le_right _ _⟩

end Lemniscate
