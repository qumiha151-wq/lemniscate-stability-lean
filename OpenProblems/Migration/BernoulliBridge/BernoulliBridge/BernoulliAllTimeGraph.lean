import Lemniscate.LemniscateStability
import BernoulliBridge.BernoulliGraphHeight

noncomputable section
namespace Lemniscate
open Complex Set Filter MeasureTheory CoarseArithmetic
open scoped ContDiff Topology NNReal ENNReal ComplexConjugate

/-- The fixed center is chosen before the input flow. Every matched physical
slice is an oriented, scaled and rotated normal graph of height at most d. -/
def BernoulliAllTimeGraph (e : ℝ ≃o ℝ) : Prop :=
  ∀ M : ℕ,0<M → ∀ d : ℝ,0<d → ∃ ε>0,∀ γ₀ : ℝ → ℂ,
    ContDiff ℝ ∞ γ₀ → Function.Periodic γ₀ (2*Real.pi) →
    (∀ s,deriv γ₀ s≠0) → lemniscateCurvatureDeviation e M γ₀<ε →
    let a := lemniscateInitialScale M γ₀
    0<a ∧ ∃ p₀ : ℂ,∀ Y : ℝ → ℝ → ℂ,
      ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Y z.1 z.2) (Ici (0:ℝ) ×ˢ univ) →
      (∀ t : ℝ,0≤t → Function.Periodic (Y t) (2*Real.pi)) →
      IsFreeElasticFlow Y → (∀ s,Y 0 s=γ₀ s) → ∀ t : ℝ,0≤t →
      ∃ α : ℝ,∃ h : ℝ → ℝ,(∀ s,|h s|≤d) ∧
        OrientedCurveEquivalent (Y t) (fun s => p₀+(((a^4+30*t)^(1/4:ℝ):ℝ):ℂ)*
          (Complex.exp ((α:ℂ)*I)*normalGraphCurve (lemniscateReference e)
            (fun v => I*bernoulliAuxiliaryTangent e (Real.sqrt 2*v)) h s))
          (2*Real.pi) (lemniscateLength M)

private theorem main_radius_transport {P : ℝ → Prop} {Q : Prop}
    (h : ∃ r>0,P r) (k : ∀ r,0<r → P r → Q) : Q := by
  rcases h with ⟨r,hr,hP⟩
  exact k r hr hP

private theorem main_two_radius_transport {P : ℝ → ℝ → Prop} {Q : Prop}
    (h : ∃ r>0,∃ C>0,P r C)
    (k : ∀ r,0<r → ∀ C,0<C → P r C → Q) : Q := by
  rcases h with ⟨r,hr,C,hC,hP⟩
  exact k r hr C hC hP

private theorem main_graph_data_transport
    {G : Type*} {P : ∀ τ : ℝ,0<τ → ℝ → G → G → Prop} {Q : Prop}
    (h : ∃ τ : ℝ,∃ hτ : 0<τ,τ≤1 ∧ ∃ ε>0,∃ A B : G,P τ hτ ε A B)
    (k : ∀ τ : ℝ,∀ hτ : 0<τ,τ≤1 → ∀ ε,0<ε → ∀ A B : G,P τ hτ ε A B → Q) : Q := by
  rcases h with ⟨τ,hτ,hτ₁,ε,hε,A,B,hP⟩
  exact k τ hτ hτ₁ ε hε A B hP

private theorem main_norm_lt_of_profile_bound
    (C ε K N : ℝ) (hC : 0<C) (hε : 0<ε)
    (hK : K<(ε/C)^2) (hN : N≤C*Real.sqrt K) : N<ε := by
  have hs : Real.sqrt K<ε/C := (Real.sqrt_lt' (div_pos hε hC)).mpr hK
  calc
    N≤C*Real.sqrt K := hN
    _<C*(ε/C) := mul_lt_mul_of_pos_left hs hC
    _=ε := by field_simp [hC.ne']

set_option maxHeartbeats 1600000 in
private theorem all_time_graph_from_profile
    (e : ℝ ≃o ℝ)
    (he : ∀ u,e u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    [Fact (0<e (2*Real.pi))] (hlength : e (2*Real.pi)=4*Khalf)
    (q p : C(AddCircle (e (2*Real.pi)),ℂ))
    (hq : HasCircleDeriv (e (2*Real.pi)) q p)
    (hp : HasCircleDeriv (e (2*Real.pi)) p (-(q^3)))
    (hE : ∀ x,2*(p x)^2+(q x)^4=1)
    (hqreal : ∀ x,conj (q x)=q x) (hpreal : ∀ x,conj (p x)=p x)
    (hcurvature : ∀ x : ℝ,(planarSignedCurvature bernoulliCurve (e.symm x):ℂ)=
      3*q (x:AddCircle (e (2*Real.pi))))
    (hqvalue : ∀ x : ℝ,q (x:AddCircle (e (2*Real.pi)))=(bernoulliProfileQ (e.symm x):ℂ))
    (hpvalue : ∀ x : ℝ,p (x:AddCircle (e (2*Real.pi)))=(bernoulliProfileP (e.symm x):ℂ))
    (hs : ∀ n : ℤ,fourierCoeff (q^2:C(AddCircle (e (2*Real.pi)),ℂ)) (-n)=
      fourierCoeff (q^2:C(AddCircle (e (2*Real.pi)),ℂ)) n)
    (hc : ∀ j : ℕ,fourierCoeff (q^2:C(AddCircle (e (2*Real.pi)),ℂ)) (2*(j:ℤ))=
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ,fourierCoeff (q^2:C(AddCircle (e (2*Real.pi)),ℂ)) (2*n+1)=0)
    (hr : (2*Real.pi/e (2*Real.pi))^2=lemniscateFrequencySquared)
    (ψ : circleH4Domain (e (2*Real.pi)))
    (hnorm : inner ℂ (ψ:CircleL2 (e (2*Real.pi)))
      (circleUnitRotation (e (2*Real.pi)) q p)=1)
    (hψzero : circleH4FormalAdjoint (e (2*Real.pi)) (q^2) ((2:ℂ) • (q*p)) ψ=0) :
    BernoulliAllTimeGraph e := by
  intro M hM d hd
  let T := e (2*Real.pi)
  let S := (M:ℝ)*T
  have hSpos : 0<S := mul_pos (Nat.cast_pos.mpr hM) Fact.out
  let : Fact (0<S) := ⟨hSpos⟩
  have hS : S=(M:ℝ)*T := rfl
  let Q := circlePeriodicExtension T S M hS q
  let P := circlePeriodicExtension T S M hS p
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  let ell := S/Real.sqrt 2
  let β := lemniscateReference e
  let ν := fun s : ℝ => I*bernoulliAuxiliaryTangent e (Real.sqrt 2*s)
  have hsqrt : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hell : 0<ell := div_pos hSpos hsqrt
  have hellPaper : ell=lemniscateLength M := by
    dsimp only [ell,S,T,lemniscateLength]
    rw [hlength]
    ring
  have hQvalue (x : ℝ) : Q (x:AddCircle S)=(bernoulliProfileQ (e.symm x):ℂ) :=
    hqvalue x
  let κ := fun s : ℝ => 3*(Q ((Real.sqrt 2*s):AddCircle S)).re
  have hκ : κ=lemniscateReferenceCurvature e := by
    funext s
    rw [lemniscate_reference_curvature e he s]
    dsimp only [κ]
    rw [hQvalue,Complex.ofReal_re]
  have herror (γ : ℝ → ℂ) : normalizedCurvatureProfileError ell (2*Real.pi) γ κ=
      lemniscateCurvatureDeviation e M γ := by
    rw [hellPaper,hκ]
    rfl
  have hcover := (paper_periodic_cover_modulated_tame_data T S q p hq hp hE hqreal hpreal
    hs hc ho hr ψ hnorm hψzero M hM hS).2.2
  have hΨ : circleConjugate S (Ψ:CircleL2 S)=(Ψ:CircleL2 S) := hcover.1
  have hpair : inner ℂ (Ψ:CircleL2 S) (circleContinuousL2 S
      (circleBernoulliBackground S Q P).b)≠0 := hcover.2.1
  refine main_radius_transport
    (lemniscate_given_flow_identification T S e he rfl q p hq hp hE hqvalue hpvalue
      hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS) ?_
  intro η hη hPacket
  have hGiven := hPacket.2.2
  let B := ‖circleSobolevH1Embedding S‖+1
  have hB : 0<B := by dsimp only [B]; positivity
  let ηsmall := min η (d/B)
  have hsmall : 0<ηsmall := lt_min hη (div_pos hd hB)
  refine main_graph_data_transport
    (bernoulli_physical_graph_stability T S e he rfl q p hq hp hE hqvalue hpvalue
      hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS ηsmall hsmall) ?_
  intro τ hτ hτ₁ εGraph hεGraph εGraphRate CGraphRate hGraph
  have hGraphSolve := hGraph.2
  refine main_two_radius_transport
    (bernoulli_initial_normal_graph e he q p hq hcurvature M S hS (Ψ:CircleL2 S) hΨ hpair) ?_
  intro εEntry hεEntry CEntry hCEntry hEntry
  let ε := min εEntry ((εGraph/CEntry)^2)
  have hε : 0<ε := lt_min hεEntry (pow_pos (div_pos hεGraph hCEntry) 2)
  refine ⟨ε,hε,?_⟩
  intro γ₀ hγsmooth hγper hγreg hγsmall
  have hsmallEntry : normalizedCurvatureProfileError ell (2*Real.pi) γ₀ κ<εEntry := by
    rw [herror]
    exact hγsmall.trans_le (min_le_left _ _)
  have hInitial := hEntry (2*Real.pi) (by positivity) γ₀ hγsmooth hγper hγreg hsmallEntry
  have hL := hInitial.1
  refine Exists.elim hInitial.2 ?_
  intro p₀ hpData
  refine Exists.elim hpData ?_
  intro R₀ hRData
  have hR₀ := hRData.1
  refine Exists.elim hRData.2 ?_
  intro e₀ heData
  have he₀ := heData.1
  have he₀i := heData.2.1
  have hdeck := heData.2.2.1
  refine Exists.elim heData.2.2.2.2 ?_
  intro h₀ hhData
  refine Exists.elim hhData ?_
  intro hh₀ hpData
  refine Exists.elim hpData ?_
  intro hp₀ hgData
  have hInitialGraph := hgData.1
  refine Exists.elim hgData.2 ?_
  intro H hHdata
  have hHvalue := hHdata.2.1
  have hHphase := hHdata.2.2.1
  have hHnorm : ‖H‖≤CEntry*Real.sqrt (lemniscateCurvatureDeviation e M γ₀) := by
    have hh : ‖H‖≤CEntry*Real.sqrt
        (normalizedCurvatureProfileError ell (2*Real.pi) γ₀ κ) := hHdata.2.2.2
    rw [herror γ₀] at hh
    exact hh
  have hHsmall : ‖H‖<εGraph := main_norm_lt_of_profile_bound CEntry εGraph
    (lemniscateCurvatureDeviation e M γ₀) ‖H‖ hCEntry hεGraph
      (hγsmall.trans_le (min_le_right _ _)) hHnorm
  refine Exists.elim (hGraphSolve H hHphase hHsmall.le h₀ hh₀ hp₀ hHvalue) ?_
  intro D hD
  let L := ∫ u in (0:ℝ)..(2*Real.pi),‖deriv γ₀ u‖
  let a := L/ell
  have ha : 0<a := div_pos hL hell
  have haScale : a=lemniscateInitialScale M γ₀ := by
    dsimp only [a,lemniscateInitialScale]
    rw [hellPaper]
  let α := Complex.arg R₀
  have hRexp : Complex.exp ((α:ℂ)*I)=R₀ := by
    have hh := Complex.norm_mul_exp_arg_mul_I R₀
    rw [hR₀,Complex.ofReal_one,one_mul] at hh
    exact hh
  refine Exists.elim (hD a ha p₀ α) ?_
  intro ρ hρdata
  have hρall := hρdata.2.1
  have hρformula (t : ℝ) (ht : 0≤t) : ρ t=(a^4+30*t)^(1/4:ℝ) := (hρall t ht).2
  let h := fun σ s : ℝ => (circleSobolevH1Embedding S
    (circleSobolevInclusion S 1 (D.u (Real.toNNReal σ)))) ((Real.sqrt 2*s):AddCircle S) |>.re
  let Core := fun t s : ℝ => p₀+(ρ t:ℂ)*
    (Complex.exp (((α+D.theta (normalizedTime a t)):ℂ)*I)*
      normalGraphCurve β ν (h (normalizedTime a t)) s)
  have hCoreData := hρdata.2.2.2
  have hCoreInitial (s : ℝ) : Core 0 s=p₀+(a:ℂ)*
      (Complex.exp ((α:ℂ)*I)*(β s+(h₀ (Real.sqrt 2*s):ℂ)*ν s)) := hCoreData.2.1 s
  have hCoreSpace : ∀ t : ℝ,0≤t → ContDiff ℝ ∞ (Core t) := hCoreData.2.2.1
  have hCorePoint := hCoreData.2.2.2.1
  have hCoreFlow : IsFreeElasticFlow Core := by
    intro t ht s
    refine Exists.elim (hCorePoint t ht) ?_
    intro V hV
    refine ⟨V s,(hV s).1,(hV s).2.1,?_⟩
    simpa only [planarElasticForce] using! (hV s).2.2.2
  have hCoreInitialExact (s : ℝ) : Core 0 s=γ₀ (e₀ s) := by
    rw [hCoreInitial,hInitialGraph]
    simp only [Complex.real_smul,hRexp]
    rfl
  refine ⟨haScale ▸ ha,p₀,?_⟩
  intro Y hYsmooth hYper hYflow hYinitial t ht
  have hYInitialEq : OrientedCurveEquivalent (Y 0) (Core 0) (2*Real.pi) ell :=
    ⟨e₀,he₀,he₀i,hdeck,fun s => (hYinitial (e₀ s)).trans (hCoreInitialExact s).symm⟩
  let Dwide : BernoulliNormalGraphEvolution S Q P (Ψ:CircleL2 S) τ hτ η H :=
    {D with segmentSmall := fun m => (D.segmentSmall m).trans_le (min_le_left _ _)}
  have hEquivalent : OrientedCurveEquivalent (Y t) (Core t) (2*Real.pi) ell :=
    hGiven τ hτ H Dwide h₀ hh₀ hp₀ hHvalue a ha p₀ α ρ hρall hCoreSpace
      hCoreFlow (2*Real.pi) (by positivity) Y hYsmooth hYper hYflow hYInitialEq t ht
  refine ⟨α+D.theta (normalizedTime a t),h (normalizedTime a t),?_,?_⟩
  · intro s
    have hu := bernoulli_all_time_height_bound S D (normalizedTime a t) s
    exact hu.trans ((mul_le_mul_of_nonneg_left (min_le_right η (d/B)) hB.le).trans_eq
      (by field_simp [hB.ne'] : B*(d/B)=d))
  · simpa only [Core,hρformula t ht,haScale,hellPaper,β,ν,Complex.ofReal_add] using hEquivalent

/-- The initial hypothesis is the intrinsic signed curvature-profile deviation.
The conclusion controls the physical graph also during the first scale time. -/
theorem bernoulli_all_time_graph_from_initial_curvature :
    ∃ e : ℝ ≃o ℝ,(∀ u,e u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖) ∧
      e (2*Real.pi)=4*Khalf ∧ BernoulliAllTimeGraph e := by
  obtain ⟨T,hT,hData⟩ := bernoulli_stability_data_exists
  let : Fact (0<T) := ⟨hT⟩
  let A : BernoulliStabilityData T := Classical.choice hData
  rcases A with ⟨e,he,hperiod,hlength,q,p,hq,hp,hE,hqreal,hpreal,hcurvature,
    hqvalue,hpvalue,hs,hc,ho,hr,ψ,hnorm,hψzero⟩
  subst T
  exact ⟨e,he,hlength,all_time_graph_from_profile e he hlength q p hq hp hE hqreal
    hpreal hcurvature hqvalue hpvalue hs hc ho hr ψ hnorm hψzero⟩

end Lemniscate
