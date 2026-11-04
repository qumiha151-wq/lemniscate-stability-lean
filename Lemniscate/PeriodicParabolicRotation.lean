import Lemniscate.PeriodicParabolicNormalGraphFlow
import Lemniscate.NormalGraphRotation

/-! The actual rotation term in the time normal-graph equation.  The same
continuous coefficient algebra and the same unit domain as the unmodulated
equation are used.  The phase speed is an independent scalar time-L2
variable; no adjoint functional or phase normalization enters this module.

-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped ENNReal Topology

variable (T : ℝ) [Fact (0 < T)]

private def timeScalarLift :
    Lp ℂ 2 (volume : Measure unitInterval) →L[ℂ] CircleTimeL2 T :=
  (ContinuousLinearMap.toSpanSingleton ℂ (circleContinuousL2 T 1)).compLpL 2
    (volume : Measure unitInterval)

/-- Continuous time-space coefficients act bounded bilinearly on a scalar
time-L2 phase speed, with values in the actual circle-valued time-L2 space. -/
def circleTimeScalarCoefficientMultiplyL2 :
    CircleTimeCoefficient T →L[ℂ]
      Lp ℂ 2 (volume : Measure unitInterval) →L[ℂ] CircleTimeL2 T :=
  ((ContinuousLinearMap.compL ℂ
    (Lp ℂ 2 (volume : Measure unitInterval)) (CircleTimeL2 T) (CircleTimeL2 T)).flip
      (timeScalarLift T)).comp (circleTimeCoefficientMultiplyL2 T)

theorem circle_time_scalar_coefficient_multiply_l2_norm_le
    (a : CircleTimeCoefficient T) (φ : Lp ℂ 2 (volume : Measure unitInterval)) :
    ‖circleTimeScalarCoefficientMultiplyL2 T a φ‖ ≤
      ‖circleContinuousL2 T 1‖*‖a‖*‖φ‖ := by
  have hnorm : ‖timeScalarLift T‖ ≤ ‖circleContinuousL2 T 1‖ := by
    simpa only [timeScalarLift,ContinuousLinearMap.norm_toSpanSingleton] using
      (ContinuousLinearMap.toSpanSingleton ℂ (circleContinuousL2 T 1)).norm_compLpL_le
        (p := 2) (μ := (volume : Measure unitInterval))
  have hφ : ‖timeScalarLift T φ‖ ≤ ‖circleContinuousL2 T 1‖*‖φ‖ :=
    ((timeScalarLift T).le_opNorm φ).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg φ))
  change ‖circleTimeCoefficientMultiplyL2 T a (timeScalarLift T φ)‖ ≤ _
  calc
    _ ≤ ‖a‖*‖timeScalarLift T φ‖ :=
      circle_time_coefficient_multiply_l2_norm_le T a _
    _ ≤ ‖a‖*(‖circleContinuousL2 T 1‖*‖φ‖) :=
      mul_le_mul_of_nonneg_left hφ (norm_nonneg a)
    _ = _ := by ring

private theorem time_scalar_coefficient_multiply_ae
    (a : CircleTimeCoefficient T) (φ : Lp ℂ 2 (volume : Measure unitInterval)) :
    (circleTimeScalarCoefficientMultiplyL2 T a φ : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => φ t • circleContinuousL2 T (a.curry t) := by
  have hφ := (ContinuousLinearMap.toSpanSingleton ℂ (circleContinuousL2 T 1)).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) φ
  filter_upwards [circle_time_coefficient_multiply_l2_ae T a (timeScalarLift T φ),hφ]
    with t hm hφt
  have hm' : circleTimeScalarCoefficientMultiplyL2 T a φ t =
      circleMultiplyL2 T (a.curry t) (timeScalarLift T φ t) := by
    apply Lp.ext
    filter_upwards [hm,circle_multiply_l2_ae T (a.curry t) (timeScalarLift T φ t)]
      with x hleft hright
    exact hleft.trans hright.symm
  have hφt' : timeScalarLift T φ t = φ t • circleContinuousL2 T 1 := hφt
  rw [hm',hφt']
  change circleCoefficientMultiplyL2 T (a.curry t) (φ t • circleContinuousL2 T 1) = _
  rw [map_smul,circle_coefficient_multiply_l2_apply,
    circle_multiply_l2_continuous,mul_one]

variable (τ : ℝ)

/-- The continuous coefficient b+(eta+h)*h_s/A; the first derivative here
is the physical derivative in the existing low Sobolev coordinates. -/
def circleParabolicRotationCoefficient
    (z : (Fin 6 → CircleTimeCoefficient T) × CircleParabolicSpace T τ) :
    CircleTimeCoefficient T :=
  z.1 5+(z.1 4+circleParabolicLowCoordinates T τ z.2 0)*
    circleParabolicLowCoordinates T τ z.2 1*
      Ring.inverse (1-z.1 0*circleParabolicLowCoordinates T τ z.2 0)

/-- The rotation term with an independent scalar time-L2 phase speed. -/
def circleParabolicRotationAction
    (p : ((Fin 6 → CircleTimeCoefficient T) × CircleParabolicSpace T τ) ×
      Lp ℂ 2 (volume : Measure unitInterval)) : CircleTimeL2 T :=
  circleTimeScalarCoefficientMultiplyL2 T (circleParabolicRotationCoefficient T τ p.1) p.2

set_option maxHeartbeats 800000 in
private theorem rotation_smooth_from_units
    {R E P Y : Type*} [NormedCommRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (low : E →L[ℂ] (Fin 2 → R)) (M : R →L[ℂ] P →L[ℂ] Y)
    (s : Set ((Fin 6 → R) × E))
    (hunit : ∀ z ∈ s, IsUnit (1-z.1 0*low z.2 0)) :
    ContDiffOn ℂ (⊤ : WithTop ℕ∞)
      (fun z : (Fin 6 → R) × E =>
        z.1 5+(z.1 4+low z.2 0)*low z.2 1*Ring.inverse (1-z.1 0*low z.2 0)) s ∧
    ContDiffOn ℂ (⊤ : WithTop ℕ∞)
      (fun p : ((Fin 6 → R) × E) × P => M
        (p.1.1 5+(p.1.1 4+low p.1.2 0)*low p.1.2 1*
          Ring.inverse (1-p.1.1 0*low p.1.2 0)) p.2)
      (Prod.fst ⁻¹' s) := by
  have hlowMap : ContDiff ℂ (⊤ : WithTop ℕ∞) low := low.contDiff
  have hsnd : ContDiff ℂ (⊤ : WithTop ℕ∞) (fun z : (Fin 6 → R) × E => z.2) :=
    contDiff_snd
  have hlow (j : Fin 2) : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun z : (Fin 6 → R) × E => low z.2 j) := by
    simpa only [Function.comp_def] using contDiff_pi.mp (hlowMap.comp hsnd) j
  have hfst : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun z : (Fin 6 → R) × E => z.1) := contDiff_fst
  have hbackground (i : Fin 6) : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun z : (Fin 6 → R) × E => z.1 i) := contDiff_pi.mp hfst i
  have hA : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun z : (Fin 6 → R) × E => 1-z.1 0*low z.2 0) :=
    contDiff_const.sub ((hbackground 0).mul (hlow 0))
  have hG : ContDiffOn ℂ (⊤ : WithTop ℕ∞)
      (fun z : (Fin 6 → R) × E =>
        z.1 5+(z.1 4+low z.2 0)*low z.2 1*Ring.inverse (1-z.1 0*low z.2 0)) s := by
    intro z hz
    have hu : IsUnit (1-z.1 0*low z.2 0) := hunit z hz
    have hi := contDiffAt_ringInverse ℂ (n := (⊤ : WithTop ℕ∞)) hu.unit
    rw [hu.unit_spec] at hi
    have hAi : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
        (fun w : (Fin 6 → R) × E => Ring.inverse (1-w.1 0*low w.2 0)) z := by
      have hc := hi.comp z (hA.contDiffAt (x := z))
      simpa only [Function.comp_def] using! hc
    have h₀ := (hlow 0).contDiffAt (x := z)
    have h₁ := (hlow 1).contDiffAt (x := z)
    have h₄ := (hbackground 4).contDiffAt (x := z)
    have h₅ := (hbackground 5).contDiffAt (x := z)
    exact (h₅.add (((h₄.add h₀).mul h₁).mul hAi)).contDiffWithinAt
  refine ⟨hG,?_⟩
  have hcoeff : ContDiffOn ℂ (⊤ : WithTop ℕ∞)
      (fun p : ((Fin 6 → R) × E) × P =>
        p.1.1 5+(p.1.1 4+low p.1.2 0)*low p.1.2 1*
          Ring.inverse (1-p.1.1 0*low p.1.2 0)) (Prod.fst ⁻¹' s) :=
    hG.comp contDiff_fst.contDiffOn (fun _ hp => hp)
  exact M.isBoundedBilinearMap.contDiff.comp_contDiffOn
    (hcoeff.prodMk contDiff_snd.contDiffOn)

private theorem rotation_domain_unit
    (z : (Fin 6 → CircleTimeCoefficient T) × CircleParabolicSpace T τ)
    (hz : z ∈ circleParabolicNormalGraphDomain T τ) :
    IsUnit (1-z.1 0*circleParabolicLowCoordinates T τ z.2 0) := by
  change IsUnit (1-z.1 0*circleParabolicLowCoordinates T τ z.2 0) ∧
    IsUnit ((1-z.1 0*circleParabolicLowCoordinates T τ z.2 0)^2+
      (circleParabolicLowCoordinates T τ z.2 1)^2) at hz
  exact hz.1

set_option maxHeartbeats 800000 in
/-- Both the rotation coefficient and its action by the external phase
speed are complex smooth on the actual joint unit domain. -/
theorem circle_parabolic_rotation_smooth :
    ContDiffOn ℂ (⊤ : WithTop ℕ∞) (circleParabolicRotationCoefficient T τ)
      (circleParabolicNormalGraphDomain T τ) ∧
    ContDiffOn ℂ (⊤ : WithTop ℕ∞) (circleParabolicRotationAction T τ)
      (Prod.fst ⁻¹' circleParabolicNormalGraphDomain T τ) := by
  simpa only [circleParabolicRotationCoefficient,circleParabolicRotationAction] using!
    (rotation_smooth_from_units
      (R := CircleTimeCoefficient T) (E := ↥(CircleParabolicSpace T τ))
      (P := Lp ℂ 2 (volume : Measure unitInterval)) (Y := ↥(CircleTimeL2 T))
      (circleParabolicLowCoordinates T τ) (circleTimeScalarCoefficientMultiplyL2 T)
      (circleParabolicNormalGraphDomain T τ)
      (fun z hz => by simpa only using! (rotation_domain_unit T τ z hz)))

private theorem map_rotation_polynomial
    {R S : Type*} [CommRing R] [CommRing S] (e : R →+* S)
    (b eta h hs r : R) (s : S) (hi : e r=s) :
    e (b+(eta+h)*hs*r) = e b+(e eta+e h)*e hs*s := by
  simp only [map_add,map_mul,hi]

private theorem rotation_coefficient_restrict
    (a : Fin 6 → CircleTimeCoefficient T) (U : CircleParabolicSpace T τ)
    (hU : (a,U) ∈ circleParabolicNormalGraphDomain T τ) (t : unitInterval) :
    (circleParabolicRotationCoefficient T τ (a,U)).curry t =
      let K := circleTimeNormalGraphBackground T a t
      let u := circleNormalGraphLowCoordinates T (circleParabolicCurve T τ U t)
      K.b+(K.eta+u 0)*u 1*Ring.inverse (1-K.k*u 0) := by
  let low := circleParabolicLowCoordinates T τ U
  let A : CircleTimeCoefficient T := 1-a 0*low 0
  have hA : IsUnit A := hU.1
  have hi := circle_time_coefficient_inverse_restrict T A hA t
  have hlow (j : Fin 2) : (low j).curry t =
      circleNormalGraphLowCoordinates T (circleParabolicCurve T τ U t) j := by
    apply ContinuousMap.ext
    intro x
    exact circle_parabolic_low_coordinates_apply T τ U j t x
  have hslice : A.curry t = 1-(a 0).curry t*(low 0).curry t := rfl
  rw [hslice] at hi
  have hformula : (circleParabolicRotationCoefficient T τ (a,U)).curry t =
      (a 5).curry t+((a 4).curry t+(low 0).curry t)*(low 1).curry t*
        Ring.inverse (1-(a 0).curry t*(low 0).curry t) :=
    map_rotation_polynomial (circleTimeCoefficientRestriction T t).toRingHom
      (a 5) (a 4) (low 0) (low 1) (Ring.inverse A) _ hi
  simpa only [hlow,circleTimeNormalGraphBackground,normalGraphBackgroundFromCoordinates]
    using! hformula

private theorem combine_rotation_ae
    {X V P : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → V) (F : P → X → V) (r g : X → V) (B : P → X → V → V)
    (hf : f =ᵐ[μ] r) (hF : ∀ p, F p =ᵐ[μ] fun x => B p x (r x))
    (hg : ∀ x, r x=g x) :
    (f =ᵐ[μ] g) ∧ ∀ p, F p =ᵐ[μ] fun x => B p x (g x) := by
  refine ⟨hf.trans (Eventually.of_forall hg),?_⟩
  intro p
  exact (hF p).trans (Eventually.of_forall fun x => congrArg (B p x) (hg x))

/-- The time-L2 expressions agree almost everywhere with the existing
spatial rotation field, both before and after the external phase action. -/
theorem circle_parabolic_rotation_ae
    (a : Fin 6 → CircleTimeCoefficient T) (U : CircleParabolicSpace T τ)
    (hU : (a,U) ∈ circleParabolicNormalGraphDomain T τ) :
    ((circleTimeContinuousL2 T (circleParabolicRotationCoefficient T τ (a,U)) :
        unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleNormalGraphRotationField T (circleTimeNormalGraphBackground T a t)
        (circleParabolicCurve T τ U t)) ∧
    ∀ φ : Lp ℂ 2 (volume : Measure unitInterval),
      (circleParabolicRotationAction T τ ((a,U),φ) : unitInterval → CircleL2 T) =ᵐ[volume]
        fun t => φ t • circleNormalGraphRotationField T (circleTimeNormalGraphBackground T a t)
          (circleParabolicCurve T τ U t) := by
  have hfield (t : unitInterval) :
      circleContinuousL2 T ((circleParabolicRotationCoefficient T τ (a,U)).curry t) =
        circleNormalGraphRotationField T (circleTimeNormalGraphBackground T a t)
          (circleParabolicCurve T τ U t) := by
    simpa only [circleNormalGraphRotationField] using!
      congrArg (circleContinuousL2 T) (rotation_coefficient_restrict T τ a U hU t)
  exact combine_rotation_ae (volume : Measure unitInterval)
    ((circleTimeContinuousL2 T (circleParabolicRotationCoefficient T τ (a,U))) :
      unitInterval → CircleL2 T)
    (fun φ : Lp ℂ 2 (volume : Measure unitInterval) =>
      (circleParabolicRotationAction T τ ((a,U),φ) : unitInterval → CircleL2 T))
    (fun t => circleContinuousL2 T ((circleParabolicRotationCoefficient T τ (a,U)).curry t))
    (fun t => circleNormalGraphRotationField T (circleTimeNormalGraphBackground T a t)
      (circleParabolicCurve T τ U t))
    (fun φ t v => φ t • v)
    (circle_time_continuous_l2_ae T (circleParabolicRotationCoefficient T τ (a,U)))
    (time_scalar_coefficient_multiply_ae T (circleParabolicRotationCoefficient T τ (a,U)))
    hfield

end Lemniscate
