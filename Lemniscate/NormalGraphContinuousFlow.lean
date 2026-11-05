import Lemniscate.NormalGraphClassicalRepresentation
import Lemniscate.NormalGraphRotation
import Lemniscate.PeriodicSobolevClassicalJet

/-! Continuous spatial representatives of the actual normal-graph velocity.
H5 supplies the continuous fourth derivative through the general classical
jet. Continuity of the flow uses the existing quasilinear identity and
coefficient theorem; no new polynomial or geometric calculation is needed.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

/-- The raw normal-graph flow as a continuous function for actual H5 data. -/
def circleNormalGraphContinuousFlow
    (K : BackgroundJetOver C(AddCircle T,ℂ)) (c : ℝ)
    (f : CircleSobolevSpace T 5) : C(AddCircle T,ℂ) :=
  let Z := circleNormalGraphCoordinates T (circleSobolevInclusion T 4 f)
  normalGraphRationalFlow K c
    ⟨Z 0,Z 1,Z 2,Z 3,(4:ℂ) • circleSobolevClassicalJet T 4 f 4⟩

/-- The continuous representative of the existing H2 rotation field. -/
def circleNormalGraphContinuousRotation
    (K : BackgroundJetOver C(AddCircle T,ℂ))
    (h : CircleSobolevSpace T 2) : C(AddCircle T,ℂ) :=
  let z := circleNormalGraphLowCoordinates T h
  K.b+(K.eta+z 0)*z 1*Ring.inverse (1-K.k*z 0)

private theorem continuous_flow_l2
    (K : BackgroundJetOver C(AddCircle T,ℂ)) (c : ℝ)
    (f : CircleSobolevSpace T 5)
    (hf : circleSobolevInclusion T 4 f ∈ circleNormalGraphDomain T K) :
    circleContinuousL2 T (circleNormalGraphContinuousFlow T K c f)=
      circleNormalGraphFlow T K c (circleSobolevInclusion T 4 f) := by
  have hfourth : circleSobolevCoordinate T 4 4 (circleSobolevInclusion T 4 f)=
      circleContinuousL2 T (circleSobolevClassicalJet T 4 f 4) :=
    (circle_sobolev_classical_jet_l2 T 4 f 4).symm
  exact ((circle_normal_graph_flow_classical_representation T K c
    (circleSobolevInclusion T 4 f) (circleSobolevClassicalJet T 4 f 4) hfourth hf).1).symm

private theorem rational_flow_coordinate_split
    {R : Type*} [CommRing R] [Algebra ℝ R]
    (K : BackgroundJetOver R) (c : ℝ) (z : Fin 4 → R) (v : R)
    (hA : IsUnit (1-K.k*z 0)) :
    normalGraphRationalFlow K c ⟨z 0,z 1,z 2,z 3,v⟩=
      normalGraphPrincipalCoefficientOver R K z*v+
        normalGraphLowerOrderCoefficientOver R K c z := by
  exact normal_graph_rational_flow_quasilinear K c _ hA

set_option maxHeartbeats 800000 in
private theorem continuous_flow_on_unit_domain
    (K : BackgroundJetOver C(AddCircle T,ℂ)) (c : ℝ) :
    ContinuousOn (circleNormalGraphContinuousFlow T K c)
      ((circleSobolevInclusion T 4) ⁻¹' circleNormalGraphDomain T K) := by
  let E : CircleSobolevSpace T 5 → Fin 4 → C(AddCircle T,ℂ) :=
    fun f => circleNormalGraphCoordinates T (circleSobolevInclusion T 4 f)
  let V : CircleSobolevSpace T 5 → C(AddCircle T,ℂ) :=
    fun f => (4:ℂ) • circleSobolevClassicalJet T 4 f 4
  have hE : Continuous E :=
    (circleNormalGraphCoordinates T).continuous.comp (circleSobolevInclusion T 4).continuous
  have hV : Continuous V := by
    have hproj : Continuous (fun f : CircleSobolevSpace T 5 =>
        circleSobolevClassicalJet T 4 f 4) :=
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 5 => C(AddCircle T,ℂ)) (4 : Fin 5)).continuous.comp
        (circleSobolevClassicalJet T 4).continuous
    exact (show Continuous (fun _ : CircleSobolevSpace T 5 => (4:ℂ)) from
      continuous_const).smul hproj
  let D := (circleSobolevInclusion T 4) ⁻¹' circleNormalGraphDomain T K
  obtain ⟨_,_,hcoeff⟩ := normal_graph_coefficients_smooth_over C(AddCircle T,ℂ) K c
  have hsplit (f : CircleSobolevSpace T 5) (hf : f ∈ D) :
      circleNormalGraphContinuousFlow T K c f=
        normalGraphPrincipalCoefficient T K (E f)*V f+
          normalGraphLowerOrderCoefficient T K c (E f) := by
    have hA : IsUnit (1-K.k*E f 0) := hf.1
    exact rational_flow_coordinate_split K c (E f) (V f) hA
  have hsum : ContinuousOn (fun f =>
      normalGraphPrincipalCoefficient T K (E f)*V f+
        normalGraphLowerOrderCoefficient T K c (E f)) D := by
    intro f hf
    have hc : ContinuousAt (fun z : CircleSobolevSpace T 5 =>
        (normalGraphPrincipalCoefficient T K (E z),
          normalGraphLowerOrderCoefficient T K c (E z))) f := by
      simpa only [normalGraphPrincipalCoefficient,normalGraphLowerOrderCoefficient,
        Function.comp_def] using ((hcoeff (E f) hf).continuousAt).comp hE.continuousAt
    exact ((hc.fst.mul hV.continuousAt).add hc.snd).continuousWithinAt
  exact hsum.congr hsplit

private theorem continuous_rotation_on_unit_domain
    (K : BackgroundJetOver C(AddCircle T,ℂ)) :
    ContinuousOn (circleNormalGraphContinuousRotation T K)
      ((circleNormalGraphLowCoordinates T) ⁻¹' normalGraphLowerCoefficientDomain T K) := by
  have h₀ : Continuous (fun h : CircleSobolevSpace T 2 =>
      circleNormalGraphLowCoordinates T h 0) :=
    ((ContinuousLinearMap.proj (0 : Fin 2)).comp (circleNormalGraphLowCoordinates T)).continuous
  have h₁ : Continuous (fun h : CircleSobolevSpace T 2 =>
      circleNormalGraphLowCoordinates T h 1) :=
    ((ContinuousLinearMap.proj (1 : Fin 2)).comp (circleNormalGraphLowCoordinates T)).continuous
  have hA : Continuous (fun h : CircleSobolevSpace T 2 =>
      1-K.k*circleNormalGraphLowCoordinates T h 0) :=
    continuous_const.sub (continuous_const.mul h₀)
  intro h hh
  have hu : IsUnit (1-K.k*circleNormalGraphLowCoordinates T h 0) := hh.1
  have hi := NormedRing.inverse_continuousAt hu.unit
  rw [hu.unit_spec] at hi
  have hinv : ContinuousAt (fun z : CircleSobolevSpace T 2 =>
      Ring.inverse (1-K.k*circleNormalGraphLowCoordinates T z 0)) h :=
    ContinuousAt.comp
      (f := fun z : CircleSobolevSpace T 2 => 1-K.k*circleNormalGraphLowCoordinates T z 0)
      (g := (Ring.inverse : C(AddCircle T,ℂ) → C(AddCircle T,ℂ))) hi hA.continuousAt
  exact (continuousAt_const.add
    (((continuousAt_const.add h₀.continuousAt).mul h₁.continuousAt).mul hinv)).continuousWithinAt

set_option maxHeartbeats 800000 in
/-- The H5 continuous flow agrees with the actual H4-to-L2 equation on
its unit domain. Together with the H2 rotation representative it is
continuous on one genuine H2 neighbourhood, independent of higher norms. -/
theorem circle_normal_graph_continuous_representatives
    (K : BackgroundJetOver C(AddCircle T,ℂ)) (c : ℝ) :
    (∀ f : CircleSobolevSpace T 5,
      circleSobolevInclusion T 4 f ∈ circleNormalGraphDomain T K →
      circleContinuousL2 T (circleNormalGraphContinuousFlow T K c f)=
        circleNormalGraphFlow T K c (circleSobolevInclusion T 4 f)) ∧
      (∀ h : CircleSobolevSpace T 2,
        circleContinuousL2 T (circleNormalGraphContinuousRotation T K h)=
          circleNormalGraphRotationField T K h) ∧
      ∃ δ > 0,
        (∀ f : CircleSobolevSpace T 5,
          ‖circleSobolevInclusion T 2
            (circleSobolevInclusion T 3 (circleSobolevInclusion T 4 f))‖ < δ →
          circleSobolevInclusion T 4 f ∈ circleNormalGraphDomain T K) ∧
        ContinuousOn (circleNormalGraphContinuousFlow T K c)
          {f : CircleSobolevSpace T 5 | ‖circleSobolevInclusion T 2
            (circleSobolevInclusion T 3 (circleSobolevInclusion T 4 f))‖ < δ} ∧
        ContinuousOn (circleNormalGraphContinuousRotation T K)
          (Metric.ball (0 : CircleSobolevSpace T 2) δ) := by
  refine ⟨continuous_flow_l2 T K c,fun _ => rfl,?_⟩
  obtain ⟨d,hd,hflowdomain⟩ := circle_normal_graph_h2_small_domain T K
  obtain ⟨hopen,hzero,_⟩ :=
    normal_graph_lower_coefficients_smooth_over C(AddCircle T,ℂ) K 0
  let D := (circleNormalGraphLowCoordinates T) ⁻¹' normalGraphLowerCoefficientDomain T K
  have hopenD : IsOpen D := hopen.preimage (circleNormalGraphLowCoordinates T).continuous
  have hzeroD : (0 : CircleSobolevSpace T 2) ∈ D := by
    change circleNormalGraphLowCoordinates T 0 ∈ normalGraphLowerCoefficientDomain T K
    simpa only [map_zero,normalGraphLowerCoefficientDomain] using hzero
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hopenD.mem_nhds hzeroD)
  let δ := min d r
  have hδ : 0 < δ := lt_min hd hr
  have hflow (f : CircleSobolevSpace T 5)
      (hf : ‖circleSobolevInclusion T 2
        (circleSobolevInclusion T 3 (circleSobolevInclusion T 4 f))‖ < δ) :
      circleSobolevInclusion T 4 f ∈ circleNormalGraphDomain T K :=
    hflowdomain _ (hf.trans_le (min_le_left d r))
  refine ⟨δ,hδ,hflow,?_,?_⟩
  · exact (continuous_flow_on_unit_domain T K c).mono hflow
  · apply (continuous_rotation_on_unit_domain T K).mono
    intro h hh
    apply hball
    have hh' : ‖h‖ < δ := by simpa only [Metric.mem_ball,dist_zero_right] using hh
    simpa only [Metric.mem_ball,dist_zero_right] using hh'.trans_le (min_le_right d r)

end Lemniscate
