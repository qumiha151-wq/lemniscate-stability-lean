import Lemniscate.PeriodicParabolicRotation
import Lemniscate.PeriodicSobolevTranslation
import Lemniscate.NormalGraphRationalIdentities

/-! Spatial covariance used to identify the actual translated solution with
the parameter equation. The background is translated field by field;
the adjoint vector is not translated. 
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

variable (T : ℝ) [Fact (0 < T)]

/-- Pullback of continuous coefficients by x ↦ x+a. -/
def circleCoefficientTranslation (a : AddCircle T) :
    C(AddCircle T, ℂ) →ₐ[ℝ] C(AddCircle T, ℂ) :=
  ContinuousMap.compRightAlgHom ℝ ℂ ⟨fun x => x+a,continuous_id.add_const a⟩

/-- Translate each field of the existing background jet. -/
def circleNormalGraphBackgroundTranslation (a : AddCircle T)
    (K : BackgroundJetOver C(AddCircle T, ℂ)) : BackgroundJetOver C(AddCircle T, ℂ) :=
  let e := circleCoefficientTranslation T a
  ⟨e K.k,e K.ks,e K.kss,e K.ksss,e K.eta,e K.b⟩

private theorem coefficient_translation_smul (a : AddCircle T) (c : ℂ)
    (f : C(AddCircle T, ℂ)) :
    circleCoefficientTranslation T a (c • f) = c • circleCoefficientTranslation T a f := by
  apply ContinuousMap.ext
  intro x
  rfl

private theorem coefficient_translation_isUnit (a : AddCircle T)
    (f : C(AddCircle T, ℂ)) :
    IsUnit (circleCoefficientTranslation T a f) ↔ IsUnit f := by
  constructor
  · intro h
    apply (ContinuousMap.isUnit_iff_forall_ne_zero f).mpr
    intro x
    have hx := (ContinuousMap.isUnit_iff_forall_ne_zero _).mp h (x-a)
    change f ((x-a)+a) ≠ 0 at hx
    simpa only [sub_add_cancel] using hx
  · exact fun h => h.map (circleCoefficientTranslation T a)

private theorem continuous_l2_translation (a : AddCircle T) (f : C(AddCircle T, ℂ)) :
    circleContinuousL2 T (circleCoefficientTranslation T a f) =
      circleL2Translation T a (circleContinuousL2 T f) := by
  have hf := (measurePreserving_add_right AddCircle.haarAddCircle a).quasiMeasurePreserving.ae
    (ContinuousMap.coeFn_toLp (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ) f)
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) AddCircle.haarAddCircle
    (𝕜 := ℂ) (circleCoefficientTranslation T a f),
    circle_l2_translation_ae T a (circleContinuousL2 T f),hf] with x hleft hright hf'
  exact hleft.trans (hf'.symm.trans hright.symm)

private theorem l2_translation_multiply (a : AddCircle T)
    (b : C(AddCircle T, ℂ)) (f : CircleL2 T) :
    circleL2Translation T a (circleMultiplyL2 T b f) =
      circleMultiplyL2 T (circleCoefficientTranslation T a b) (circleL2Translation T a f) := by
  have hm := (measurePreserving_add_right AddCircle.haarAddCircle a).quasiMeasurePreserving.ae
    (circle_multiply_l2_ae T b f)
  apply Lp.ext
  filter_upwards [circle_l2_translation_ae T a (circleMultiplyL2 T b f),hm,
    circle_l2_translation_ae T a f,
    circle_multiply_l2_ae T (circleCoefficientTranslation T a b) (circleL2Translation T a f)]
    with x hleft hm' hf hright
  exact hleft.trans (hm'.trans ((congrArg (fun z : ℂ => b (x+a)*z) hf.symm).trans hright.symm))

private theorem continuous_jet_translation (a : AddCircle T)
    (f : CircleSobolevSpace T 4) (j : Fin 4) :
    circleSobolevContinuousJet T (circleSobolevTranslation T 4 a f) j =
      circleCoefficientTranslation T a (circleSobolevContinuousJet T f j) := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
  change circleContinuousL2 T (circleSobolevContinuousJet T (circleSobolevTranslation T 4 a f) j) =
    circleContinuousL2 T (circleCoefficientTranslation T a (circleSobolevContinuousJet T f j))
  rw [(circle_sobolev_classical_jet_l2 T 3),continuous_l2_translation,
    (circle_sobolev_classical_jet_l2 T 3)]
  rfl

private theorem graph_coordinates_translation (a : AddCircle T) (f : CircleSobolevSpace T 4) :
    circleNormalGraphCoordinates T (circleSobolevTranslation T 4 a f) =
      fun j => circleCoefficientTranslation T a (circleNormalGraphCoordinates T f j) := by
  funext j
  rw [circle_normal_graph_coordinates,circle_normal_graph_coordinates]
  fin_cases j <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',
    continuous_jet_translation,coefficient_translation_smul]

private theorem low_coordinate_l2 (f : CircleSobolevSpace T 2) (j : Fin 2) :
    circleContinuousL2 T (circleNormalGraphLowCoordinates T f j) =
      (![1,((Real.sqrt 2:ℝ):ℂ)] j) • circleSobolevCoordinate T 2 j.castSucc f := by
  have h₀ : circleContinuousL2 T (circleSobolevH1Embedding T (circleSobolevInclusion T 1 f)) =
      circleSobolevCoordinate T 2 0 f := circle_sobolev_h1_embedding_l2 T _
  have h₁ : circleContinuousL2 T (((Real.sqrt 2:ℝ):ℂ) •
      circleSobolevH1Embedding T (circleSobolevDerivative T 1 f)) =
        ((Real.sqrt 2:ℝ):ℂ) • circleSobolevCoordinate T 2 1 f :=
    ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).map_smul ((Real.sqrt 2:ℝ):ℂ)
      (circleSobolevH1Embedding T (circleSobolevDerivative T 1 f))).trans
      (congrArg (((Real.sqrt 2:ℝ):ℂ) • ·) (circle_sobolev_h1_embedding_l2 T _))
  rw [circle_normal_graph_low_coordinates]
  fin_cases j
  · simpa only [Matrix.cons_val_zero',Matrix.cons_val_succ',one_smul] using! h₀
  · simpa only [Matrix.cons_val_zero',Matrix.cons_val_succ'] using! h₁

private theorem low_coordinates_translation (a : AddCircle T) (f : CircleSobolevSpace T 2) :
    circleNormalGraphLowCoordinates T (circleSobolevTranslation T 2 a f) =
      fun j => circleCoefficientTranslation T a (circleNormalGraphLowCoordinates T f j) := by
  funext j
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
  change circleContinuousL2 T (circleNormalGraphLowCoordinates T (circleSobolevTranslation T 2 a f) j) =
    circleContinuousL2 T (circleCoefficientTranslation T a (circleNormalGraphLowCoordinates T f j))
  rw [low_coordinate_l2,continuous_l2_translation,low_coordinate_l2]
  exact ((circleL2Translation T a).map_smul _ _).symm

private theorem translated_unit_pair (a : AddCircle T)
    (k z₀ z₁ : C(AddCircle T, ℂ)) :
    let e := circleCoefficientTranslation T a
    (IsUnit (1-e k*e z₀) ∧ IsUnit ((1-e k*e z₀)^2+(e z₁)^2)) ↔
      (IsUnit (1-k*z₀) ∧ IsUnit ((1-k*z₀)^2+z₁^2)) := by
  let e := circleCoefficientTranslation T a
  have hA : 1-e k*e z₀ = e (1-k*z₀) := by simp only [map_sub,map_one,map_mul]
  have hH : (1-e k*e z₀)^2+(e z₁)^2 = e ((1-k*z₀)^2+z₁^2) := by
    simp only [map_add,map_pow,map_sub,map_one,map_mul]
  change (IsUnit (1-e k*e z₀) ∧ IsUnit ((1-e k*e z₀)^2+(e z₁)^2)) ↔ _
  rw [hH,hA,coefficient_translation_isUnit,coefficient_translation_isUnit]

set_option maxHeartbeats 800000 in
/-- The actual normal-graph equation and rotation field commute with spatial
translation on their common unit domain. Translation carries each actual
Sobolev derivative and every background field; no adjoint vector occurs. -/
theorem circle_normal_graph_translation
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (a : AddCircle T) (c : ℝ)
    (f : CircleSobolevSpace T 4) (h : CircleSobolevSpace T 2) :
    let Ka := circleNormalGraphBackgroundTranslation T a K
    (f ∈ circleNormalGraphDomain T K ↔
      circleSobolevTranslation T 4 a f ∈ circleNormalGraphDomain T Ka) ∧
    (circleNormalGraphLowCoordinates T h ∈ normalGraphLowerCoefficientDomain T K ↔
      circleNormalGraphLowCoordinates T (circleSobolevTranslation T 2 a h) ∈
        normalGraphLowerCoefficientDomain T Ka) ∧
    (f ∈ circleNormalGraphDomain T K →
      circleNormalGraphFlow T Ka c (circleSobolevTranslation T 4 a f) =
        circleL2Translation T a (circleNormalGraphFlow T K c f)) ∧
    (circleNormalGraphLowCoordinates T h ∈ normalGraphLowerCoefficientDomain T K →
      circleNormalGraphRotationField T Ka (circleSobolevTranslation T 2 a h) =
        circleL2Translation T a (circleNormalGraphRotationField T K h)) := by
  let e := circleCoefficientTranslation T a
  let Ka := circleNormalGraphBackgroundTranslation T a K
  let Z := circleNormalGraphCoordinates T f
  let Za : Fin 4 → C(AddCircle T, ℂ) := fun j => e (Z j)
  let z := circleNormalGraphLowCoordinates T h
  let za : Fin 2 → C(AddCircle T, ℂ) := fun j => e (z j)
  have hZ : circleNormalGraphCoordinates T (circleSobolevTranslation T 4 a f) = Za :=
    graph_coordinates_translation T a f
  have hz : circleNormalGraphLowCoordinates T (circleSobolevTranslation T 2 a h) = za :=
    low_coordinates_translation T a h
  have hdomain : f ∈ circleNormalGraphDomain T K ↔
      circleSobolevTranslation T 4 a f ∈ circleNormalGraphDomain T Ka := by
    change (IsUnit (1-K.k*Z 0) ∧ IsUnit ((1-K.k*Z 0)^2+(Z 1)^2)) ↔ _
    change _ ↔ (IsUnit (1-Ka.k*(circleNormalGraphCoordinates T (circleSobolevTranslation T 4 a f) 0)) ∧
      IsUnit ((1-Ka.k*(circleNormalGraphCoordinates T (circleSobolevTranslation T 4 a f) 0))^2+
        (circleNormalGraphCoordinates T (circleSobolevTranslation T 4 a f) 1)^2))
    rw [hZ]
    exact (translated_unit_pair T a K.k (Z 0) (Z 1)).symm
  have hlowdomain : z ∈ normalGraphLowerCoefficientDomain T K ↔
      circleNormalGraphLowCoordinates T (circleSobolevTranslation T 2 a h) ∈
        normalGraphLowerCoefficientDomain T Ka := by
    change (IsUnit (1-K.k*z 0) ∧ IsUnit ((1-K.k*z 0)^2+(z 1)^2)) ↔ _
    change _ ↔ (IsUnit (1-Ka.k*(circleNormalGraphLowCoordinates T (circleSobolevTranslation T 2 a h) 0)) ∧
      IsUnit ((1-Ka.k*(circleNormalGraphLowCoordinates T (circleSobolevTranslation T 2 a h) 0))^2+
        (circleNormalGraphLowCoordinates T (circleSobolevTranslation T 2 a h) 1)^2))
    rw [hz]
    exact (translated_unit_pair T a K.k (z 0) (z 1)).symm
  refine ⟨hdomain,hlowdomain,?_,?_⟩
  · intro hf
    have hunit : IsUnit (graphA K ⟨Z 0,Z 1,Z 2,Z 3,0⟩) ∧
        IsUnit (graphMetricSquared K ⟨Z 0,Z 1,Z 2,Z 3,0⟩) := hf
    have hH : graphMetricSquared Ka ⟨Za 0,Za 1,Za 2,Za 3,0⟩ =
        e (graphMetricSquared K ⟨Z 0,Z 1,Z 2,Z 3,0⟩) := by
      simp only [graphMetricSquared,graphA,Ka,circleNormalGraphBackgroundTranslation,
        Za,map_add,map_pow,map_sub,map_one,map_mul]
      rfl
    have hprincipal : normalGraphPrincipalCoefficient T Ka Za = e (normalGraphPrincipalCoefficient T K Z) := by
      change -(Ring.inverse (graphMetricSquared Ka ⟨Za 0,Za 1,Za 2,Za 3,0⟩))^2 =
        e (-(Ring.inverse (graphMetricSquared K ⟨Z 0,Z 1,Z 2,Z 3,0⟩))^2)
      rw [hH,map_neg,map_pow,algebra_map_ring_inverse e _ hunit.2]
    have hlower : normalGraphLowerOrderCoefficient T Ka c Za = e (normalGraphLowerOrderCoefficient T K c Z) := by
      simpa only [normalGraphLowerOrderCoefficient,normalGraphLowerOrderCoefficientOver,
        Ka,circleNormalGraphBackgroundTranslation,Za,map_zero] using
        (rational_flow_algebra_map e K c ⟨Z 0,Z 1,Z 2,Z 3,0⟩ hunit.1 hunit.2).symm
    have hfourth : (4:ℂ) • circleSobolevCoordinate T 4 4 (circleSobolevTranslation T 4 a f) =
        circleL2Translation T a ((4:ℂ) • circleSobolevCoordinate T 4 4 f) :=
      (((circleL2Translation T a).map_smul (4:ℂ) (circleSobolevCoordinate T 4 4 f)).trans
        (congrArg ((4:ℂ) • ·) (circle_sobolev_translation_coordinate T 4 a f 4).symm)).symm
    change circleNormalGraphFlow T Ka c (circleSobolevTranslation T 4 a f) = _
    simp only [circleNormalGraphFlow,circle_coefficient_multiply_l2_apply,hZ,
      hprincipal,hlower,(circleL2Translation T a).map_add,l2_translation_multiply,
      ← continuous_l2_translation,hfourth]
    rfl
  · intro hh
    have hA : IsUnit (1-K.k*z 0) := hh.1
    have hi := algebra_map_ring_inverse e (1-K.k*z 0) hA
    have hcoeff : Ka.b+(Ka.eta+za 0)*za 1*Ring.inverse (1-Ka.k*za 0) =
        e (K.b+(K.eta+z 0)*z 1*Ring.inverse (1-K.k*z 0)) := by
      simp only [Ka,circleNormalGraphBackgroundTranslation,za,map_add,map_mul,
        hi,map_sub,map_one]
      rfl
    change circleContinuousL2 T (Ka.b+
      (Ka.eta+circleNormalGraphLowCoordinates T (circleSobolevTranslation T 2 a h) 0)*
      circleNormalGraphLowCoordinates T (circleSobolevTranslation T 2 a h) 1*
        Ring.inverse (1-Ka.k*circleNormalGraphLowCoordinates T (circleSobolevTranslation T 2 a h) 0)) = _
    rw [hz,hcoeff,continuous_l2_translation]
    rfl

end Lemniscate
