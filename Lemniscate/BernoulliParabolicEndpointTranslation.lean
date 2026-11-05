import Lemniscate.BernoulliParabolicEndpointBackground
import Lemniscate.BernoulliParabolicTranslationEquation
import Lemniscate.PeriodicParabolicStaticTranslation

/-! The endpoint parameter family is an actual spatial pullback of the
given solution. The initial datum is translated by a, while the physical
velocity has the same transport a/τ as the positive-time family. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set AddCircle
open scoped ENNReal Topology

variable (T : ℝ) [Fact (0 < T)]

/-- The actual pullback x ↦ x+a(r+1) on the full parabolic solution. -/
def circleParabolicEndpointTranslation (τ : ℝ) (hτ : τ ≠ 0) (a : ℝ)
    (U : CircleParabolicSpace T τ) : CircleParabolicSpace T τ :=
  circleParabolicStaticTranslation T τ a (circleParabolicTranslation T τ hτ a U)

private theorem endpoint_shift_sum (a : ℝ) (t : unitInterval) :
    (a:AddCircle T)+((a*(t:ℝ):ℝ):AddCircle T) = ((a*((t:ℝ)+1):ℝ):AddCircle T) := by
  rw [← AddCircle.coe_add]
  congr 1
  ring

private theorem endpoint_l2_shift_add (a b : AddCircle T) (f : CircleL2 T) :
    circleL2Translation T a (circleL2Translation T b f) = circleL2Translation T (a+b) f := by
  apply circle_fourier_ext T
  intro n
  rw [circle_l2_translation_fourier,circle_l2_translation_fourier,circle_l2_translation_fourier]
  simp only [fourier_apply,smul_add,toCircle_add,Circle.coe_mul]
  ring

theorem circle_parabolic_endpoint_translation_curve (τ : ℝ) (hτ : τ ≠ 0)
    (a : ℝ) (U : CircleParabolicSpace T τ) (t : unitInterval) :
    circleParabolicCurve T τ (circleParabolicEndpointTranslation T τ hτ a U) t =
      circleSobolevTranslation T 2 ((a*((t:ℝ)+1):ℝ):AddCircle T)
        (circleParabolicCurve T τ U t) := by
  have hs := circle_parabolic_static_translation_curve T τ a
    (circleParabolicTranslation T τ hτ a U) t
  have hd := circle_parabolic_translation_curve T τ hτ a U t
  exact hs.trans ((congrArg (circleSobolevTranslation T 2 (a:AddCircle T)) hd).trans
    ((circle_sobolev_translation_add T 2 (a:AddCircle T) ((a*(t:ℝ):ℝ):AddCircle T)
      (circleParabolicCurve T τ U t)).trans
        (congrArg (fun b : AddCircle T => circleSobolevTranslation T 2 b
          (circleParabolicCurve T τ U t)) (endpoint_shift_sum T a t))))

set_option maxHeartbeats 800000 in
/-- The genuine translated H4 and velocity representatives, including the
translated initial trace. No new time primitive is postulated. -/
theorem circle_parabolic_endpoint_translation_components (τ : ℝ) (hτ : τ ≠ 0)
    (a : ℝ) (U : CircleParabolicSpace T τ) :
    ((circleParabolicH4 T τ (circleParabolicEndpointTranslation T τ hτ a U) :
      unitInterval → CircleSobolevSpace T 4) =ᵐ[volume] fun t =>
        circleSobolevTranslation T 4 ((a*((t:ℝ)+1):ℝ):AddCircle T)
          (circleParabolicH4 T τ U t)) ∧
    ((circleParabolicTimeDerivative T τ (circleParabolicEndpointTranslation T τ hτ a U) :
      unitInterval → CircleL2 T) =ᵐ[volume] fun t =>
        circleL2Translation T ((a*((t:ℝ)+1):ℝ):AddCircle T)
          (circleParabolicTimeDerivative T τ U t)+
        ((a/τ:ℝ):ℂ) • circleSobolevCoordinate T 4 1
          (circleSobolevTranslation T 4 ((a*((t:ℝ)+1):ℝ):AddCircle T)
            (circleParabolicH4 T τ U t))) ∧
    circleParabolicInitialValue T τ (circleParabolicEndpointTranslation T τ hτ a U) =
      circleSobolevTranslation T 2 (a:AddCircle T) (circleParabolicInitialValue T τ U) := by
  let D := circleParabolicTranslation T τ hτ a U
  have hD := circle_parabolic_translation_components T τ hτ a U
  have hS := circle_parabolic_static_translation_components T τ a D
  constructor
  · filter_upwards [hS.1,hD.1] with t hs hd
    exact hs.trans ((congrArg (circleSobolevTranslation T 4 (a:AddCircle T)) hd).trans
      ((circle_sobolev_translation_add T 4 (a:AddCircle T) ((a*(t:ℝ):ℝ):AddCircle T)
        (circleParabolicH4 T τ U t)).trans
          (congrArg (fun b : AddCircle T => circleSobolevTranslation T 4 b
            (circleParabolicH4 T τ U t)) (endpoint_shift_sum T a t))))
  constructor
  · filter_upwards [hS.2.1,hD.2.1] with t hs hd
    let b : AddCircle T := ((a*(t:ℝ):ℝ):AddCircle T)
    let H := circleSobolevTranslation T 4 b (circleParabolicH4 T τ U t)
    let α : ℂ := ((a/τ:ℝ):ℂ)
    have hcoord : circleL2Translation T (a:AddCircle T) (circleSobolevCoordinate T 4 1 H) =
        circleSobolevCoordinate T 4 1 (circleSobolevTranslation T 4 (a:AddCircle T) H) :=
      (circle_sobolev_translation_coordinate T 4 (a:AddCircle T) H 1).symm
    calc
      circleParabolicTimeDerivative T τ (circleParabolicEndpointTranslation T τ hτ a U) t =
          circleL2Translation T (a:AddCircle T) (circleParabolicTimeDerivative T τ D t) := hs
      _ = circleL2Translation T (a:AddCircle T)
          (circleL2Translation T b (circleParabolicTimeDerivative T τ U t)+
            α • circleSobolevCoordinate T 4 1 H) :=
        congrArg (circleL2Translation T (a:AddCircle T)) hd
      _ = circleL2Translation T ((a:AddCircle T)+b) (circleParabolicTimeDerivative T τ U t)+
          α • circleSobolevCoordinate T 4 1
            (circleSobolevTranslation T 4 ((a:AddCircle T)+b) (circleParabolicH4 T τ U t)) := by
        let S := circleL2Translation T (a:AddCircle T)
        let v := circleL2Translation T b (circleParabolicTimeDerivative T τ U t)
        let d := circleSobolevCoordinate T 4 1 H
        have hlin : S (v+α • d) = S v+α • S d :=
          (S.map_add v (α • d)).trans (congrArg (fun z : CircleL2 T => S v+z) (S.map_smul α d))
        have hH : circleSobolevTranslation T 4 (a:AddCircle T) H =
            circleSobolevTranslation T 4 ((a:AddCircle T)+b) (circleParabolicH4 T τ U t) :=
          circle_sobolev_translation_add T 4 (a:AddCircle T) b (circleParabolicH4 T τ U t)
        exact hlin.trans (congrArg₂ (fun x y : CircleL2 T => x+α • y)
          (endpoint_l2_shift_add T (a:AddCircle T) b (circleParabolicTimeDerivative T τ U t))
          (hcoord.trans (congrArg (circleSobolevCoordinate T 4 1) hH)))
      _ = _ := congrArg (fun c : AddCircle T =>
        circleL2Translation T c (circleParabolicTimeDerivative T τ U t)+
          α • circleSobolevCoordinate T 4 1
            (circleSobolevTranslation T 4 c (circleParabolicH4 T τ U t))) (endpoint_shift_sum T a t)
  · exact hS.2.2.trans (congrArg (circleSobolevTranslation T 2 (a:AddCircle T)) hD.2.2)

private theorem endpoint_radius_transport {P : ℝ → Prop} {Q : Prop}
    (h : ∃ δ > 0, P δ) (k : ∀ δ, 0 < δ → P δ → Q) : Q := by
  obtain ⟨δ,hδ,hP⟩ := h
  exact k δ hδ hP

set_option maxHeartbeats 800000 in
/-- The actual endpoint translation solves the endpoint parameter equation.
The initial parameter is its actual translated smooth initial trace. -/
theorem bernoulli_parabolic_endpoint_translation_equation (q p : C(AddCircle T,ℂ)) :
    ∃ δ > 0, ∀ τ : ℝ, ∀ hτ : τ ≠ 0, ∀ U : CircleParabolicSpace T τ, ‖U‖ < δ →
      ∀ φ : Lp ℂ 2 (volume : Measure unitInterval),
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative T τ U t =
        circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2) (circleParabolicH4 T τ U t)-
          φ t • circleNormalGraphRotationField T (circleBernoulliBackground T q p)
            (circleParabolicCurve T τ U t)) →
      ∀ a : ℝ, circleParabolicTranslatedEquation T τ
        (circleBernoulliParabolicEndpointBackground T q p)
        ((a,circleSobolevTranslation T 2 (a:AddCircle T) (circleParabolicInitialValue T τ U),φ),
          circleParabolicEndpointTranslation T τ hτ a U) = 0 := by
  refine endpoint_radius_transport (bernoulli_parabolic_translated_residual T q p) ?_
  intro δ hδ hresidual
  refine ⟨δ,hδ,?_⟩
  intro τ hτ U hU φ hPDE a
  let V := circleParabolicEndpointTranslation T τ hτ a U
  have hcomp := circle_parabolic_endpoint_translation_components T τ hτ a U
  have h := hresidual τ U hU φ hPDE (circleBernoulliParabolicEndpointBackground T q p a) V
    (fun t => ((a*((t:ℝ)+1):ℝ):AddCircle T)) ((a/τ:ℝ):ℂ)
    (bernoulli_parabolic_endpoint_background_slice T q p a)
    (circle_parabolic_endpoint_translation_curve T τ hτ a U) hcomp.1 hcomp.2.1
  change (circleParabolicInitialValue T τ V-
    circleSobolevTranslation T 2 (a:AddCircle T) (circleParabolicInitialValue T τ U),_) = 0
  exact Prod.ext (sub_eq_zero.mpr hcomp.2.2) h.2

end Lemniscate
