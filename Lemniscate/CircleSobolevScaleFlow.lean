import Lemniscate.CircleClassicalJetFlow
import Lemniscate.CircleSobolevJetCompatibility
import Lemniscate.PeriodicParabolicNormalGraphFlow
import Lemniscate.NormalGraphModulation
import Lemniscate.NormalGraphAngularVelocity

/-! Smooth higher-space realizations of the actual modulated equation.
Five spare spatial derivatives suffice. The open domain is exactly the
pullback of the H2 graph-unit and phase-denominator conditions; no bound on
the higher Sobolev norm is imposed. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff

variable (T : ℝ) [Fact (0 < T)]

private def jetBackgroundValue (m : ℕ)
    (K : BackgroundJetOver (CircleClassicalJetAlgebra T m)) :
    BackgroundJetOver C(AddCircle T,ℂ) :=
  let v := circleClassicalJetValue T m
  ⟨v K.k,v K.ks,v K.kss,v K.ksss,v K.eta,v K.b⟩

private theorem jet_raw_value (m : ℕ)
    (K : BackgroundJetOver (CircleClassicalJetAlgebra T m)) (c : ℝ)
    (z : Fin 5 → CircleClassicalJetAlgebra T m)
    (hu : (fun j => z j.castSucc) ∈ normalGraphCoefficientDomainOver _ K) :
    circleClassicalJetValue T m (circleJetRawFlow T m K c z) =
      normalGraphPrincipalCoefficientOver _ (jetBackgroundValue T m K)
          (fun j => circleClassicalJetValue T m (z j.castSucc))*
          circleClassicalJetValue T m (z 4) +
        normalGraphLowerOrderCoefficientOver _ (jetBackgroundValue T m K) c
          (fun j => circleClassicalJetValue T m (z j.castSucc)) := by
  let e := (circleClassicalJetValue T m).restrictScalars ℝ
  have hi := algebra_map_ring_inverse e
    (graphMetricSquared K ⟨z 0,z 1,z 2,z 3,0⟩) hu.2
  have hlo := rational_flow_algebra_map e K c ⟨z 0,z 1,z 2,z 3,0⟩ hu.1 hu.2
  simp only [e,AlgHom.restrictScalars_apply,graphMetricSquared,graphA,
    map_add,map_pow,map_sub,map_one,map_mul] at hi
  simp only [e,AlgHom.restrictScalars_apply,map_zero] at hlo
  have htwo : (2:Fin 4).castSucc=(2:Fin 5) := rfl
  have hthree : (3:Fin 4).castSucc=(3:Fin 5) := rfl
  simp only [circleJetRawFlow,map_add,map_mul,normalGraphPrincipalCoefficientOver,
    normalGraphLowerOrderCoefficientOver,map_neg,map_pow,Fin.castSucc_zero,
    Fin.castSucc_one,htwo,hthree,hi,hlo,map_zero,
    graphMetricSquared,graphA,jetBackgroundValue]

private theorem jet_rotation_value (m : ℕ)
    (K : BackgroundJetOver (CircleClassicalJetAlgebra T m))
    (z : Fin 5 → CircleClassicalJetAlgebra T m)
    (hu : IsUnit (1-K.k*z 0)) :
    circleClassicalJetValue T m (circleJetRotationField T m K z) =
      (jetBackgroundValue T m K).b +
        ((jetBackgroundValue T m K).eta+circleClassicalJetValue T m (z 0))*
          circleClassicalJetValue T m (z 1)*
          Ring.inverse (1-(jetBackgroundValue T m K).k*
            circleClassicalJetValue T m (z 0)) := by
  have hi := algebra_map_ring_inverse
    ((circleClassicalJetValue T m).restrictScalars ℝ) (1-K.k*z 0) hu
  simp only [AlgHom.restrictScalars_apply,map_sub,map_one,map_mul] at hi
  simp only [circleJetRotationField,map_add,map_mul,hi,jetBackgroundValue]

private theorem lift_background (m : ℕ)
    (K : BackgroundJetOver C(AddCircle T,ℂ))
    (hk : ContDiff ℝ ∞ (fun x : ℝ => K.k (x:AddCircle T)))
    (hks : ContDiff ℝ ∞ (fun x : ℝ => K.ks (x:AddCircle T)))
    (hkss : ContDiff ℝ ∞ (fun x : ℝ => K.kss (x:AddCircle T)))
    (hksss : ContDiff ℝ ∞ (fun x : ℝ => K.ksss (x:AddCircle T)))
    (heta : ContDiff ℝ ∞ (fun x : ℝ => K.eta (x:AddCircle T)))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => K.b (x:AddCircle T))) :
    ∃ L : BackgroundJetOver (CircleClassicalJetAlgebra T m),
      (CircleClassicalJetHolonomic T m L.k ∧
        CircleClassicalJetHolonomic T m L.ks ∧
        CircleClassicalJetHolonomic T m L.kss ∧
        CircleClassicalJetHolonomic T m L.ksss ∧
        CircleClassicalJetHolonomic T m L.eta ∧
        CircleClassicalJetHolonomic T m L.b) ∧ jetBackgroundValue T m L=K := by
  obtain ⟨k,hkhol,hkv⟩ := circle_classical_jet_lift_of_smooth T m K.k hk
  obtain ⟨ks,hkshol,hksv⟩ := circle_classical_jet_lift_of_smooth T m K.ks hks
  obtain ⟨kss,hksshol,hkssv⟩ := circle_classical_jet_lift_of_smooth T m K.kss hkss
  obtain ⟨ksss,hkssshol,hksssv⟩ := circle_classical_jet_lift_of_smooth T m K.ksss hksss
  obtain ⟨eta,hetahol,hetav⟩ := circle_classical_jet_lift_of_smooth T m K.eta heta
  obtain ⟨b,hbhol,hbv⟩ := circle_classical_jet_lift_of_smooth T m K.b hb
  refine ⟨⟨k,ks,kss,ksss,eta,b⟩,⟨hkhol,hkshol,hksshol,hkssshol,hetahol,hbhol⟩,?_⟩
  cases K
  simp_all only [jetBackgroundValue]

/-- Every spatial Sobolev order admits a smooth realization of the actual
modulated normal-graph equation with a fixed loss of five derivatives.
Its domain is determined entirely by the H2 graph and phase conditions. -/
theorem circle_modulated_flow_sobolev_scale
    (K : BackgroundJetOver C(AddCircle T,ℂ)) (c : ℝ) (ψ : CircleL2 T)
    (hk : ContDiff ℝ ∞ (fun x : ℝ => K.k (x:AddCircle T)))
    (hks : ContDiff ℝ ∞ (fun x : ℝ => K.ks (x:AddCircle T)))
    (hkss : ContDiff ℝ ∞ (fun x : ℝ => K.kss (x:AddCircle T)))
    (hksss : ContDiff ℝ ∞ (fun x : ℝ => K.ksss (x:AddCircle T)))
    (heta : ContDiff ℝ ∞ (fun x : ℝ => K.eta (x:AddCircle T)))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => K.b (x:AddCircle T)))
    (m : ℕ) :
    ∃ (O : Set (CircleSobolevSpace T (m+5)))
      (R : CircleSobolevSpace T (m+5) → CircleSobolevSpace T m),
      IsOpen O ∧ ContDiffOn ℝ ∞ R O ∧
      ContDiffOn ℝ ∞ (fun f => circleNormalGraphAngularVelocity T K c ψ
        (circleSobolevTruncation T 4 (m+5) (by omega) f)) O ∧
      (∀ f, f ∈ O ↔
        let f₄ := circleSobolevTruncation T 4 (m+5) (by omega) f
        f₄ ∈ circleNormalGraphDomain T K ∧
          circleNormalGraphRotationFunctional T ψ
            (circleNormalGraphRotationField T K
              (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f₄))) ≠ 0) ∧
      ∀ f ∈ O, circleSobolevCoordinate T m 0 (R f) =
        circleNormalGraphModulatedFlow T K c ψ
          (circleSobolevTruncation T 4 (m+5) (by omega) f) := by
  obtain ⟨L,hLhol,hLv⟩ := lift_background T m K hk hks hkss hksss heta hb
  let Z := circleSobolevPhysicalJetLift T m
  let O : Set (CircleSobolevSpace T (m+5)) := Z ⁻¹' circleJetFlowDomain T m L ψ
  let F : CircleSobolevSpace T (m+5) → CircleClassicalJetAlgebra T m :=
    fun f => circleJetModulatedFlow T m L c ψ (Z f)
  have hFsmooth : ContDiffOn ℝ ∞ F O :=
    ((circle_jet_modulated_flow_smooth T m L c ψ).2.1.restrict_scalars ℝ).comp
      (Z.restrictScalars ℝ).contDiff.contDiffOn (fun _ h => h)
  have hFhol : ∀ f ∈ O, CircleClassicalJetHolonomic T m (F f) := by
    intro f hf
    exact circle_jet_modulated_flow_holonomic T m L c ψ (Z f) hLhol
      (circle_sobolev_physical_jet_lift_holonomic T m f) hf
  obtain ⟨R,hRsmooth,hRcoord⟩ :=
    circle_classical_jet_sobolev_family T m ∞ O F hFsmooth hFhol
  have hunit (f : CircleSobolevSpace T (m+5)) :
      ((fun j => Z f j.castSucc) ∈ normalGraphCoefficientDomainOver _ L) ↔
        circleSobolevTruncation T 4 (m+5) (by omega) f ∈ circleNormalGraphDomain T K := by
    have hlow := (circle_sobolev_physical_jet_compatibility T m f).1
    have hz0 := hlow 0
    have hz1 := hlow 1
    change circleClassicalJetValue T m (Z f 0) = _ at hz0
    change circleClassicalJetValue T m (Z f 1) = _ at hz1
    have hkval : circleClassicalJetValue T m L.k = K.k :=
      congrArg BackgroundJetOver.k hLv
    change (IsUnit (1-L.k*Z f 0) ∧ IsUnit ((1-L.k*Z f 0)^2+(Z f 1)^2)) ↔ _
    rw [circle_classical_jet_isUnit,circle_classical_jet_isUnit]
    change _ ↔ (IsUnit (1-K.k*(circleNormalGraphCoordinates T
      (circleSobolevTruncation T 4 (m+5) (by omega) f) 0)) ∧
      IsUnit ((1-K.k*(circleNormalGraphCoordinates T
        (circleSobolevTruncation T 4 (m+5) (by omega) f) 0))^2+
        (circleNormalGraphCoordinates T
          (circleSobolevTruncation T 4 (m+5) (by omega) f) 1)^2))
    simp only [map_sub,map_one,map_mul,map_add,map_pow,hkval,hz0,hz1]
  have hrotation (f : CircleSobolevSpace T (m+5))
      (hf : (fun j => Z f j.castSucc) ∈ normalGraphCoefficientDomainOver _ L) :
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)
        (circleClassicalJetValue T m (circleJetRotationField T m L (Z f))) =
        circleNormalGraphRotationField T K
          (circleSobolevInclusion T 2 (circleSobolevInclusion T 3
            (circleSobolevTruncation T 4 (m+5) (by omega) f))) := by
    rw [jet_rotation_value T m L (Z f) hf.1,hLv]
    have hlow := (circle_sobolev_physical_jet_compatibility T m f).1
    have hz0 := hlow 0
    have hz1 := hlow 1
    change circleClassicalJetValue T m (Z f 0) = _ at hz0
    change circleClassicalJetValue T m (Z f 1) = _ at hz1
    rw [hz0,hz1]
    have hc0 := circle_normal_graph_coordinates_low T
      (circleSobolevTruncation T 4 (m+5) (by omega) f) 0
    have hc1 := circle_normal_graph_coordinates_low T
      (circleSobolevTruncation T 4 (m+5) (by omega) f) 1
    change circleNormalGraphCoordinates T _ 0 = _ at hc0
    change circleNormalGraphCoordinates T _ 1 = _ at hc1
    rw [hc0,hc1]
    rfl
  have hraw (f : CircleSobolevSpace T (m+5))
      (hf : (fun j => Z f j.castSucc) ∈ normalGraphCoefficientDomainOver _ L) :
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)
        (circleClassicalJetValue T m (circleJetRawFlow T m L c (Z f))) =
        circleNormalGraphFlow T K c (circleSobolevTruncation T 4 (m+5) (by omega) f) := by
    rw [jet_raw_value T m L c (Z f) hf,hLv]
    have hcompat := circle_sobolev_physical_jet_compatibility T m f
    have hZ : (fun j : Fin 4 => circleClassicalJetValue T m (Z f j.castSucc)) =
        circleNormalGraphCoordinates T (circleSobolevTruncation T 4 (m+5) (by omega) f) :=
      funext hcompat.1
    rw [hZ]
    rw [map_add]
    have hm := circle_multiply_l2_continuous T
      (normalGraphPrincipalCoefficientOver _ K
        (circleNormalGraphCoordinates T (circleSobolevTruncation T 4 (m+5) (by omega) f)))
      (circleClassicalJetValue T m (Z f 4))
    simp only [circleContinuousL2] at hm
    rw [← hm]
    have hfourth := hcompat.2
    change (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)
      (circleClassicalJetValue T m (Z f 4)) = _ at hfourth
    rw [hfourth]
    rfl
  refine ⟨O,R,(circle_jet_modulated_flow_smooth T m L c ψ).1.preimage Z.continuous,
    hRsmooth,?_,?_,?_⟩
  · have hΩ : ContDiffOn ℝ ∞
        (fun f => circleJetAngularVelocity T m L c ψ (Z f)) O :=
      ((circle_jet_modulated_flow_smooth T m L c ψ).2.2.restrict_scalars ℝ).comp
        (Z.restrictScalars ℝ).contDiff.contDiffOn (fun _ h => h)
    apply hΩ.congr
    intro f hf
    simp only [circleNormalGraphAngularVelocity,circleJetAngularVelocity,
      circleJetPhaseFunctional,ContinuousLinearMap.comp_apply,
      circle_classical_jet_value_clm,hraw f hf.1,hrotation f hf.1]
  · intro f
    change (_ ∧ _) ↔ _
    constructor
    · intro hf
      refine ⟨(hunit f).mp hf.1,?_⟩
      simpa only [circleJetPhaseFunctional,ContinuousLinearMap.comp_apply,
        circle_classical_jet_value_clm,← hrotation f hf.1] using hf.2
    · intro hf
      have hu := (hunit f).mpr hf.1
      refine ⟨hu,?_⟩
      simpa only [circleJetPhaseFunctional,ContinuousLinearMap.comp_apply,
        circle_classical_jet_value_clm,hrotation f hu] using hf.2
  · intro f hf
    rw [hRcoord f hf 0,circle_classical_jet_coordinate_zero]
    change (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ) (circleClassicalJetValue T m
      (circleJetModulatedFlow T m L c ψ (Z f))) = _
    simp only [circleJetModulatedFlow,circleJetAngularVelocity,map_sub,map_smul,circleJetPhaseFunctional,
      ContinuousLinearMap.comp_apply,circle_classical_jet_value_clm,
      hraw f hf.1,hrotation f hf.1,circleNormalGraphModulatedFlow,
      circleNormalGraphNormalizedRotation,div_eq_mul_inv,smul_smul]

end Lemniscate
