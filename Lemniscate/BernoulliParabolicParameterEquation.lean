import Lemniscate.PeriodicParabolicNormalGraphDerivative
import Lemniscate.PeriodicParabolicRotation
import Lemniscate.PeriodicProfileShiftSmoothness
import Lemniscate.BernoulliSobolevLinearization

/-! The actual parameter equation for spatial translation, initial value
and angular velocity. All parameters use one common open unit domain.
The transport term uses the x derivative, without a physical-arclength
factor. 
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

variable (T : ℝ) [Fact (0 < T)]

abbrev CircleParabolicParameter :=
  ℝ × (CircleSobolevSpace T 2 × Lp ℂ 2 (volume : Measure unitInterval))

/-- Translate each field of the existing Bernoulli background by x ↦ x+a*t. -/
def circleBernoulliParabolicBackground (q p : C(AddCircle T, ℂ)) (a : ℝ) :
    Fin 6 → CircleTimeCoefficient T :=
  let K := circleBernoulliBackground T q p
  fun i => circleProfileTimeShift T (![K.k,K.ks,K.kss,K.ksss,K.eta,K.b] i) a

private theorem bernoulli_parabolic_background_zero
    (q p : C(AddCircle T, ℂ)) :
    circleBernoulliParabolicBackground T q p 0 =
      circleTimeConstantBackground T (circleBernoulliBackground T q p) := by
  funext i
  apply ContinuousMap.ext
  intro z
  let K := circleBernoulliBackground T q p
  change (![K.k,K.ks,K.kss,K.ksss,K.eta,K.b] i)
      (z.2+((0*(z.1:ℝ):ℝ):AddCircle T)) =
    (![K.k,K.ks,K.kss,K.ksss,K.eta,K.b] i) z.2
  simp only [zero_mul,AddCircle.coe_zero,add_zero]

private theorem bernoulli_parabolic_background_smooth
    (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) :
    ContDiff ℝ ∞ (circleBernoulliParabolicBackground T q p) := by
  have hs := circle_profile_time_shift_smooth T q p hq hp
  have hQ : ContDiff ℝ ∞ (circleProfileTimeShift T q) := hs.fst
  have hP : ContDiff ℝ ∞ (circleProfileTimeShift T p) := hs.snd
  have heq : circleBernoulliParabolicBackground T q p = fun a : ℝ =>
      ![(3:ℂ) • circleProfileTimeShift T q a,
        ((3*Real.sqrt 2:ℝ):ℂ) • circleProfileTimeShift T p a,
        (-6:ℂ) • (circleProfileTimeShift T q a)^3,
        ((-18*Real.sqrt 2:ℝ):ℂ) •
          ((circleProfileTimeShift T q a)^2*circleProfileTimeShift T p a),
        -((circleProfileTimeShift T q a)^3),
        ((Real.sqrt 2:ℝ):ℂ) •
          (circleProfileTimeShift T q a*circleProfileTimeShift T p a)] := by
    funext a i
    fin_cases i <;> apply ContinuousMap.ext <;> intro z <;> rfl
  rw [heq]
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']
  · exact hQ.const_smul (3:ℂ)
  · exact hP.const_smul ((3*Real.sqrt 2:ℝ):ℂ)
  · exact (hQ.pow 3).const_smul (-6:ℂ)
  · exact ((hQ.pow 2).mul hP).const_smul ((-18*Real.sqrt 2:ℝ):ℂ)
  · exact (hQ.pow 3).neg
  · exact (hQ.mul hP).const_smul ((Real.sqrt 2:ℝ):ℂ)

private theorem bernoulli_parabolic_background_slice
    (q p : C(AddCircle T, ℂ)) (a : ℝ) (t : unitInterval) :
    circleTimeNormalGraphBackground T (circleBernoulliParabolicBackground T q p a) t =
      circleBernoulliBackground T ((circleProfileTimeShift T q a).curry t)
        ((circleProfileTimeShift T p a).curry t) := by
  rfl

variable (τ : ℝ)

/-- The common unit domain for the time normal-graph and rotation terms. -/
def circleParabolicTranslatedDomain (b : ℝ → Fin 6 → CircleTimeCoefficient T) :
    Set (CircleParabolicParameter T × CircleParabolicSpace T τ) :=
  (fun z => (b z.1.1,z.2)) ⁻¹'
    circleParabolicNormalGraphDomain T τ

/-- The translated, rotating normal-graph equation and its actual initial
condition. The external scalar time-L2 variable is the angular velocity. -/
def circleParabolicTranslatedEquation (b : ℝ → Fin 6 → CircleTimeCoefficient T)
    (z : CircleParabolicParameter T × CircleParabolicSpace T τ) :
    CircleSobolevSpace T 2 × CircleTimeL2 T :=
  (circleParabolicInitialValue T τ z.2-z.1.2.1,
    circleParabolicTimeDerivative T τ z.2-
      circleParabolicNormalGraphFlow T τ (15/2)
        (b z.1.1,z.2)-
      (((z.1.1/τ:ℝ):ℂ) •
        (((circleSobolevCoordinate T 4 1).compLpL 2
          (volume : Measure unitInterval)).comp (circleParabolicH4 T τ)) z.2)+
      circleParabolicRotationAction T τ
        ((b z.1.1,z.2),z.1.2.2))

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
theorem circle_parabolic_translated_equation_smooth
    (b : ℝ → Fin 6 → CircleTimeCoefficient T)
    (hb : ContDiff ℝ ∞ b) :
    IsOpen (circleParabolicTranslatedDomain T τ b) ∧
      ((0 : CircleParabolicParameter T),(0 : CircleParabolicSpace T τ)) ∈
        circleParabolicTranslatedDomain T τ b ∧
      ContDiffOn ℝ ∞ (circleParabolicTranslatedEquation T τ b)
        (circleParabolicTranslatedDomain T τ b) := by
  let X := CircleParabolicParameter T × CircleParabolicSpace T τ
  let input : X → (Fin 6 → CircleTimeCoefficient T) × CircleParabolicSpace T τ :=
    fun z => (b z.1.1,z.2)
  have ha : ContDiff ℝ ∞ (fun z : X => z.1.1) := contDiff_fst.comp contDiff_fst
  have hU : ContDiff ℝ ∞ (fun z : X => z.2) := contDiff_snd
  have hbg := hb.comp ha
  have hinput : ContDiff ℝ ∞ input := hbg.prodMk hU
  have hflow := circle_parabolic_normal_graph_flow_smooth T τ (15/2)
  have hrotation := circle_parabolic_rotation_smooth T τ
  have hopen : IsOpen (circleParabolicTranslatedDomain T τ b) :=
    hflow.1.preimage hinput.continuous
  have hzero : ((0 : CircleParabolicParameter T),(0 : CircleParabolicSpace T τ)) ∈
      circleParabolicTranslatedDomain T τ b :=
    hflow.2.1 (b 0)
  have hflowR : ContDiffOn ℝ ∞ (circleParabolicNormalGraphFlow T τ (15/2))
      (circleParabolicNormalGraphDomain T τ) :=
    (hflow.2.2.of_le (show (∞ : WithTop ℕ∞) ≤ ⊤ from le_top)).restrict_scalars ℝ
  have hrotationR : ContDiffOn ℝ ∞ (circleParabolicRotationAction T τ)
      (Prod.fst ⁻¹' circleParabolicNormalGraphDomain T τ) :=
    (hrotation.2.of_le (show (∞ : WithTop ℕ∞) ≤ ⊤ from le_top)).restrict_scalars ℝ
  have hF : ContDiffOn ℝ ∞ (fun z : X =>
      circleParabolicNormalGraphFlow T τ (15/2) (input z))
      (circleParabolicTranslatedDomain T τ b) :=
    hflowR.comp hinput.contDiffOn (fun _ hz => hz)
  have hφ : ContDiff ℝ ∞ (fun z : X => z.1.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp contDiff_fst)
  have hR : ContDiffOn ℝ ∞ (fun z : X =>
      circleParabolicRotationAction T τ (input z,z.1.2.2))
      (circleParabolicTranslatedDomain T τ b) :=
    hrotationR.comp (hinput.prodMk hφ).contDiffOn (fun _ hz => hz)
  have hu₀ : ContDiff ℝ ∞ (fun z : X => z.1.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_fst)
  have hI : ContDiff ℝ ∞ (fun z : X => circleParabolicInitialValue T τ z.2) := by
    simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars'] using!
      ((circleParabolicInitialValue T τ).restrictScalars ℝ).contDiff.comp hU
  have hv : ContDiff ℝ ∞ (fun z : X => circleParabolicTimeDerivative T τ z.2) := by
    simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars'] using!
      (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
        ((circleParabolicTimeDerivative T τ).restrictScalars ℝ)).comp hU
  let Dx : CircleParabolicSpace T τ →L[ℂ] CircleTimeL2 T :=
    ((circleSobolevCoordinate T 4 1).compLpL 2 (volume : Measure unitInterval)).comp
      (circleParabolicH4 T τ)
  have hDx : ContDiff ℝ ∞ (fun z : X => Dx z.2) := by
    simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars'] using!
      (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
        (Dx.restrictScalars ℝ)).comp hU
  have hscalar : ContDiff ℝ ∞ (fun z : X => ((z.1.1/τ:ℝ):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (ha.div_const τ)
  have hresult := (hI.sub hu₀).contDiffOn.prodMk
    (((hv.contDiffOn.sub hF).sub (hscalar.smul hDx).contDiffOn).add hR)
  refine ⟨hopen,hzero,?_⟩
  simpa only [circleParabolicTranslatedEquation,input,Dx] using! hresult

/-- The common unit domain for the actual Bernoulli translation. -/
def circleBernoulliParabolicParameterDomain (q p : C(AddCircle T, ℂ)) :
    Set (CircleParabolicParameter T × CircleParabolicSpace T τ) :=
  circleParabolicTranslatedDomain T τ (circleBernoulliParabolicBackground T q p)

/-- The actual translated Bernoulli equation, with initial value and
angular velocity as independent parameters. -/
def circleBernoulliParabolicParameterEquation (q p : C(AddCircle T, ℂ))
    (z : CircleParabolicParameter T × CircleParabolicSpace T τ) :
    CircleSobolevSpace T 2 × CircleTimeL2 T :=
  circleParabolicTranslatedEquation T τ (circleBernoulliParabolicBackground T q p) z

private theorem bernoulli_parameter_equation_smooth
    (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) :
    IsOpen (circleBernoulliParabolicParameterDomain T τ q p) ∧
      ((0 : CircleParabolicParameter T),(0 : CircleParabolicSpace T τ)) ∈
        circleBernoulliParabolicParameterDomain T τ q p ∧
      ContDiffOn ℝ ∞ (circleBernoulliParabolicParameterEquation T τ q p)
        (circleBernoulliParabolicParameterDomain T τ q p) := by
  exact circle_parabolic_translated_equation_smooth T τ
    (circleBernoulliParabolicBackground T q p)
    (bernoulli_parabolic_background_smooth T q p hq hp)

private theorem lp_zero_of_slice_zero
    {H Y : Type*} [NormedAddCommGroup H] [NormedAddCommGroup Y]
    (w : Lp H 2 (volume : Measure unitInterval))
    (v : Lp Y 2 (volume : Measure unitInterval)) (F : unitInterval → H → Y)
    (hw : w = 0) (hF : ∀ t, F t 0 = 0)
    (hv : (v : unitInterval → Y) =ᵐ[volume] fun t => F t (w t)) : v = 0 := by
  apply Lp.ext
  filter_upwards [hv,Lp.coeFn_zero H 2 (volume : Measure unitInterval),
    Lp.coeFn_zero Y 2 (volume : Measure unitInterval)] with t ht hw₀ hv₀
  have hwt : w t = (0 : H) :=
    (congrArg (fun W : Lp H 2 (volume : Measure unitInterval) => W t) hw).trans hw₀
  exact ht.trans ((congrArg (F t) hwt).trans ((hF t).trans hv₀.symm))

set_option maxHeartbeats 600000 in
private theorem bernoulli_parameter_zero_face
    (q p : C(AddCircle T, ℂ)) (he : ∀ x, 2*(p x)^2+(q x)^4 = 1) (a : ℝ) :
    circleBernoulliParabolicParameterEquation T τ q p ((a,0,0),0) = 0 := by
  let b := circleBernoulliParabolicBackground T q p a
  have hdom : (b,(0 : CircleParabolicSpace T τ)) ∈ circleParabolicNormalGraphDomain T τ :=
    (circle_parabolic_normal_graph_flow_smooth T τ (15/2)).2.1 b
  have hflowAE := circle_parabolic_normal_graph_flow_ae T τ (15/2) b 0 hdom
  have hslices (t : unitInterval) :
      circleNormalGraphFlow T (circleTimeNormalGraphBackground T b t) (15/2) 0 = 0 := by
    have he' : ∀ x : AddCircle T,
        2*((circleProfileTimeShift T p a).curry t x)^2+
          ((circleProfileTimeShift T q a).curry t x)^4 = 1 := by
      intro x
      exact he (x+((a*(t:ℝ):ℝ):AddCircle T))
    simpa only [b,bernoulli_parabolic_background_slice] using
      (bernoulli_sobolev_flow_linearization T ((circleProfileTimeShift T q a).curry t)
        ((circleProfileTimeShift T p a).curry t) he').1
  have hflowzero : circleParabolicNormalGraphFlow T τ (15/2) (b,0) = 0 :=
    lp_zero_of_slice_zero (circleParabolicH4 T τ 0)
      (circleParabolicNormalGraphFlow T τ (15/2) (b,0))
      (fun t => circleNormalGraphFlow T (circleTimeNormalGraphBackground T b t) (15/2))
      (map_zero (circleParabolicH4 T τ)) hslices hflowAE
  change (circleParabolicInitialValue T τ 0-0,
    circleParabolicTimeDerivative T τ 0-circleParabolicNormalGraphFlow T τ (15/2) (b,0)-
      (((a/τ:ℝ):ℂ) • (((circleSobolevCoordinate T 4 1).compLpL 2
        (volume : Measure unitInterval)).comp (circleParabolicH4 T τ)) 0)+
      circleParabolicRotationAction T τ ((b,0),0)) = 0
  simp only [circleParabolicRotationAction,map_zero,sub_zero,smul_zero,add_zero,hflowzero]
  rfl

private theorem bernoulli_parameter_zero_slice
    (q p : C(AddCircle T, ℂ)) :
    (fun U : CircleParabolicSpace T τ =>
      circleBernoulliParabolicParameterEquation T τ q p (0,U)) =
    (fun U : CircleParabolicSpace T τ =>
      (circleParabolicInitialValue T τ U,
        circleParabolicTimeDerivative T τ U-circleParabolicNormalGraphFlow T τ (15/2)
          (circleTimeConstantBackground T (circleBernoulliBackground T q p),U))) := by
  funext U
  simp only [circleBernoulliParabolicParameterEquation,circleParabolicTranslatedEquation,Prod.fst_zero,Prod.snd_zero,
    bernoulli_parabolic_background_zero,
    circleParabolicRotationAction,zero_div,Complex.ofReal_zero,zero_smul,map_zero,
    sub_zero,add_zero]

set_option maxHeartbeats 800000 in
/-- A single open parameter equation is C∞, has its entire zero-height
translation branch, and has the actual linear data isomorphism as its
partial derivative in the solution variable at the origin. -/
theorem bernoulli_parabolic_parameter_equation
    (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T)
    (hBA : ∀ f : CircleSobolevSpace T 4,
      circleSobolevPrincipalOperator T f-
        B (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) =
          -(circleNormalGraphDerivative T (circleBernoulliBackground T q p) (15/2) f)) :
    IsOpen (circleBernoulliParabolicParameterDomain T τ q p) ∧
      ((0 : CircleParabolicParameter T),(0 : CircleParabolicSpace T τ)) ∈
        circleBernoulliParabolicParameterDomain T τ q p ∧
      ContDiffOn ℝ ∞ (circleBernoulliParabolicParameterEquation T τ q p)
        (circleBernoulliParabolicParameterDomain T τ q p) ∧
      (∀ a : ℝ, circleBernoulliParabolicParameterEquation T τ q p ((a,0,0),0) = 0) ∧
      HasFDerivAt
        (fun U : CircleParabolicSpace T τ =>
          circleBernoulliParabolicParameterEquation T τ q p (0,U))
        (circleParabolicLowerOrderData T τ B) 0 := by
  have hregularity := bernoulli_parameter_equation_smooth T τ q p hq hp
  refine ⟨hregularity.1,hregularity.2.1,hregularity.2.2,
    bernoulli_parameter_zero_face T τ q p he,?_⟩
  have hstaticzero := (bernoulli_sobolev_flow_linearization T q p he).1
  have hderiv := circle_parabolic_normal_graph_hasFDerivAt T τ
    (circleBernoulliBackground T q p) (15/2) B hstaticzero hBA
  rw [bernoulli_parameter_zero_slice]
  exact hderiv

end Lemniscate
