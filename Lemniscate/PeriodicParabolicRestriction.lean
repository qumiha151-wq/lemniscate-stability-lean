import Lemniscate.PeriodicParabolicNormedSpace
import Lemniscate.PeriodicFiniteParabolicSolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Restriction of the actual maximal-regularity space to a strict time
subinterval.  The physical velocity is composed with the affine time map;
the interval length is absorbed entirely into the new physical duration.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

/-- The increasing affine parametrization of a nondegenerate time subinterval. -/
def unitTimeAffine (a b : unitInterval) (hab : a < b) : C(unitInterval,unitInterval) where
  toFun t := ⟨(a:ℝ)+((b:ℝ)-(a:ℝ))*(t:ℝ),by
    have hc : 0 ≤ (b:ℝ)-(a:ℝ) := sub_nonneg.mpr hab.le
    have hlo := mul_nonneg hc t.property.1
    have hhi := mul_le_mul_of_nonneg_left t.property.2 hc
    constructor <;> linarith [a.property.1,b.property.2]⟩
  continuous_toFun := by fun_prop

@[simp] theorem unit_time_affine_zero (a b : unitInterval) (hab : a < b) :
    unitTimeAffine a b hab 0 = a := by
  apply Subtype.ext
  change (a:ℝ)+((b:ℝ)-(a:ℝ))*0 = (a:ℝ)
  ring

@[simp] theorem unit_time_affine_one (a b : unitInterval) (hab : a < b) :
    unitTimeAffine a b hab 1 = b := by
  apply Subtype.ext
  change (a:ℝ)+((b:ℝ)-(a:ℝ))*1 = (b:ℝ)
  ring

private theorem affine_real_map_volume (c d : ℝ) (hc : c ≠ 0) :
    Measure.map (fun x : ℝ => d+c*x) volume = ENNReal.ofReal |c⁻¹| • volume := by
  change Measure.map ((fun x : ℝ => d+x) ∘ (fun x : ℝ => c*x)) volume = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),Real.map_volume_mul_left hc,
    Measure.map_smul,map_add_left_eq_self]

private theorem unit_time_affine_map_le (a b : unitInterval) (hab : a < b) :
    Measure.map (unitTimeAffine a b hab) (volume : Measure unitInterval) ≤
      ENNReal.ofReal |((b:ℝ)-(a:ℝ))⁻¹| • volume := by
  let c : ℝ := (b:ℝ)-(a:ℝ)
  have hcpos : 0 < c := sub_pos.mpr (show (a:ℝ) < (b:ℝ) from hab)
  have hc : c ≠ 0 := hcpos.ne'
  let φ : ℝ → ℝ := fun x => (a:ℝ)+c*x
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply (unitTimeAffine a b hab).continuous.measurable hs,
    Measure.smul_apply]
  calc
    volume ((unitTimeAffine a b hab) ⁻¹' s) =
        volume ((fun t : unitInterval => (t:ℝ)) '' ((unitTimeAffine a b hab) ⁻¹' s)) :=
      unitInterval.volume_apply
    _ ≤ volume (φ ⁻¹' ((fun t : unitInterval => (t:ℝ)) '' s)) := by
      apply measure_mono
      rintro x ⟨t,ht,rfl⟩
      exact ⟨unitTimeAffine a b hab t,ht,rfl⟩
    _ = Measure.map φ volume ((fun t : unitInterval => (t:ℝ)) '' s) :=
      (Measure.map_apply (by fun_prop)
        (unitInterval.measurableEmbedding_coe.measurableSet_image' hs)).symm
    _ = ENNReal.ofReal |c⁻¹| *
        volume ((fun t : unitInterval => (t:ℝ)) '' s) := by
      rw [affine_real_map_volume c (a:ℝ) hc]
      rfl
    _ = _ := by rw [← unitInterval.volume_apply]; rfl

private theorem unit_time_affine_quasi_preserving
    (a b : unitInterval) (hab : a < b) :
    Measure.QuasiMeasurePreserving (unitTimeAffine a b hab)
      (volume : Measure unitInterval) volume :=
  ⟨(unitTimeAffine a b hab).continuous.measurable,
    Measure.absolutelyContinuous_of_le_smul (unit_time_affine_map_le a b hab)⟩

section Pullback
variable {E : Type*} [NormedAddCommGroup E]

private theorem unit_time_affine_memLp
    (a b : unitInterval) (hab : a < b)
    (f : Lp E 2 (volume : Measure unitInterval)) :
    MemLp (fun t => f (unitTimeAffine a b hab t)) 2 volume := by
  have hm : MemLp f 2 (Measure.map (unitTimeAffine a b hab) volume) :=
    (Lp.memLp f).of_measure_le_smul (by simp) (unit_time_affine_map_le a b hab)
  exact hm.comp_of_map (unitTimeAffine a b hab).continuous.measurable.aemeasurable

private def unitTimeLpRestriction
    (a b : unitInterval) (hab : a < b)
    (f : Lp E 2 (volume : Measure unitInterval)) : Lp E 2 (volume : Measure unitInterval) :=
  (unit_time_affine_memLp a b hab f).toLp (fun t => f (unitTimeAffine a b hab t))

private theorem unit_time_lp_restriction_ae
    (a b : unitInterval) (hab : a < b)
    (f : Lp E 2 (volume : Measure unitInterval)) :
    (unitTimeLpRestriction a b hab f : unitInterval → E) =ᵐ[volume]
      fun t => f (unitTimeAffine a b hab t) :=
  MemLp.coeFn_toLp (unit_time_affine_memLp a b hab f)

end Pullback

private theorem unit_time_affine_primitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (q v : unitInterval → E) (τ : ℝ) (hv : Integrable v volume)
    (hq : ∀ t, q t-q 0 = τ • (∫ r in Iic t, v r ∂volume))
    (a b : unitInterval) (hab : a < b) (t : unitInterval) :
    q (unitTimeAffine a b hab t)-q a =
      (τ*((b:ℝ)-(a:ℝ))) •
        (∫ r in Iic t, v (unitTimeAffine a b hab r) ∂volume) := by
  let clamp : ℝ → unitInterval := Set.projIcc (0:ℝ) 1 zero_le_one
  have hclamp (r : unitInterval) : clamp (r:ℝ) = r := Set.projIcc_val zero_le_one r
  let w : ℝ → E := fun r => v (clamp r)
  have hwOn : IntegrableOn w (Icc (0:ℝ) 1) volume := by
    apply (unitInterval.measurePreserving_coe.integrable_comp_emb
      unitInterval.measurableEmbedding_coe).mp
    simpa only [Function.comp_def,w,hclamp] using hv
  have hw : IntervalIntegrable w volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hwOn
  have hint (r : unitInterval) : IntervalIntegrable w volume 0 (r:ℝ) :=
    hw.mono_set (uIcc_subset_uIcc (by simp) (by simpa [uIcc_of_le zero_le_one] using r.property))
  have hreal (r : unitInterval) : q r-q 0 = τ • (∫ x in (0:ℝ)..(r:ℝ), w x) := by
    rw [← unit_interval_setIntegral w r]
    simpa only [w,hclamp] using hq r
  have hdiff : q (unitTimeAffine a b hab t)-q a =
      τ • (∫ x in (a:ℝ)..(unitTimeAffine a b hab t:ℝ), w x) := by
    calc
      _ = (q (unitTimeAffine a b hab t)-q 0)-(q a-q 0) := by abel
      _ = τ • (∫ x in (0:ℝ)..(unitTimeAffine a b hab t:ℝ), w x)-
          τ • (∫ x in (0:ℝ)..(a:ℝ), w x) :=
        congrArg₂ HSub.hSub (hreal (unitTimeAffine a b hab t)) (hreal a)
      _ = _ := by
        rw [← smul_sub,intervalIntegral.integral_interval_sub_left
          (hint (unitTimeAffine a b hab t)) (hint a)]
  have hnew : (∫ r in Iic t, v (unitTimeAffine a b hab r) ∂volume) =
      ∫ x in (0:ℝ)..(t:ℝ), w ((a:ℝ)+((b:ℝ)-(a:ℝ))*x) := by
    rw [← unit_interval_setIntegral (fun x => w ((a:ℝ)+((b:ℝ)-(a:ℝ))*x)) t]
    apply integral_congr_ae
    exact Eventually.of_forall fun r => congrArg v (hclamp (unitTimeAffine a b hab r)).symm
  rw [hnew,mul_smul,intervalIntegral.smul_integral_comp_add_mul]
  change q (unitTimeAffine a b hab t)-q a =
    τ • (∫ x in (a:ℝ)..((a:ℝ)+((b:ℝ)-(a:ℝ))*(t:ℝ)), w x) at hdiff
  simpa only [mul_zero,add_zero] using hdiff

variable (T : ℝ) [Fact (0 < T)] (τ : ℝ)

private def restrictedParabolicAmbient
    (a b : unitInterval) (hab : a < b) (U : CircleParabolicSpace T τ) :
    CircleParabolicAmbient T :=
  ((circleParabolicCurve T τ U).comp (unitTimeAffine a b hab),
    unitTimeLpRestriction a b hab (circleParabolicH4 T τ U),
    unitTimeLpRestriction a b hab (circleParabolicTimeDerivative T τ U))

private theorem restricted_parabolic_mem
    (a b : unitInterval) (hab : a < b) (U : CircleParabolicSpace T τ) :
    restrictedParabolicAmbient T τ a b hab U ∈
      circleParabolicSubmodule T (τ*((b:ℝ)-(a:ℝ))) := by
  let q := (circleParabolicCurve T τ U).comp (unitTimeAffine a b hab)
  let f := unitTimeLpRestriction a b hab (circleParabolicH4 T τ U)
  let v := unitTimeLpRestriction a b hab (circleParabolicTimeDerivative T τ U)
  have hf := unit_time_lp_restriction_ae a b hab (circleParabolicH4 T τ U)
  have hv := unit_time_lp_restriction_ae a b hab (circleParabolicTimeDerivative T τ U)
  have hvalue := (unit_time_affine_quasi_preserving a b hab).ae (circle_parabolic_value_ae T τ U)
  apply (circle_parabolic_mem_iff T (τ*((b:ℝ)-(a:ℝ))) _).mpr
  constructor
  · have hq := ContinuousMap.coeFn_toLp (p := 2) (volume : Measure unitInterval) (𝕜 := ℂ) q
    have hqv := (circleSobolevCoordinate T 2 0).coeFn_compLpL
      (p := 2) (μ := (volume : Measure unitInterval))
      (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ q)
    have hfv := (circleSobolevCoordinate T 4 0).coeFn_compLpL
      (p := 2) (μ := (volume : Measure unitInterval)) f
    apply Lp.ext
    filter_upwards [hq,hqv,hfv,hf,hvalue] with t hqt hqvt hfvt hft hvalt
    change ((circleSobolevCoordinate T 2 0).compLpL 2 volume
      (ContinuousMap.toLp 2 volume ℂ q)) t =
        ((circleSobolevCoordinate T 4 0).compLpL 2 volume f) t
    rw [hqvt,hqt,hfvt,hft]
    exact hvalt
  · intro t
    have hp := unit_time_affine_primitive
      (fun r => circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U r))
      (circleParabolicTimeDerivative T τ U) τ
      (circle_parabolic_time_derivative_integrable T τ U)
      (circle_parabolic_integral_identity T τ U) a b hab t
    have hi : (∫ r in Iic t, v r ∂volume) =
        ∫ r in Iic t, circleParabolicTimeDerivative T τ U (unitTimeAffine a b hab r) ∂volume :=
      integral_congr_ae (ae_restrict_of_ae hv)
    change circleSobolevCoordinate T 2 0 (q t)-circleSobolevCoordinate T 2 0 (q 0) =
      (τ*((b:ℝ)-(a:ℝ))) • (∫ r in Iic t, v r ∂volume)
    have hqzero : circleSobolevCoordinate T 2 0 (q 0) =
        circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U a) :=
      congrArg (fun r : unitInterval =>
        circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U r))
        (unit_time_affine_zero a b hab)
    exact (congrArg (fun z : CircleL2 T => circleSobolevCoordinate T 2 0 (q t)-z)
      hqzero).trans (hp.trans (congrArg
        (fun z : CircleL2 T => (τ*((b:ℝ)-(a:ℝ))) • z) hi.symm))

/-- Restriction to [a,b], expressed on unit time with physical length
tau*(b-a).  The physical velocity acquires no additional multiplier. -/
def circleParabolicRestriction
    (a b : unitInterval) (hab : a < b) (U : CircleParabolicSpace T τ) :
    CircleParabolicSpace T (τ*((b:ℝ)-(a:ℝ))) :=
  ⟨restrictedParabolicAmbient T τ a b hab U,restricted_parabolic_mem T τ a b hab U⟩

/-- The restriction has the actual restricted representatives and initial
value; its continuous H2 norm is at most the original one. -/
theorem circle_parabolic_restriction_components
    (a b : unitInterval) (hab : a < b) (U : CircleParabolicSpace T τ) :
    let R := circleParabolicRestriction T τ a b hab U
    let τ' := τ*((b:ℝ)-(a:ℝ))
    (∀ t, circleParabolicCurve T τ' R t =
      circleParabolicCurve T τ U (unitTimeAffine a b hab t)) ∧
    ((circleParabolicH4 T τ' R : unitInterval → CircleSobolevSpace T 4) =ᵐ[volume]
      fun t => circleParabolicH4 T τ U (unitTimeAffine a b hab t)) ∧
    ((circleParabolicTimeDerivative T τ' R : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleParabolicTimeDerivative T τ U (unitTimeAffine a b hab t)) ∧
    circleParabolicInitialValue T τ' R = circleParabolicCurve T τ U a ∧
    ‖circleParabolicCurve T τ' R‖ ≤ ‖circleParabolicCurve T τ U‖ := by
  refine ⟨fun _ => rfl,unit_time_lp_restriction_ae a b hab _,
    unit_time_lp_restriction_ae a b hab _,?_,?_⟩
  · exact congrArg (circleParabolicCurve T τ U) (unit_time_affine_zero a b hab)
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro t
    exact (circleParabolicCurve T τ U).norm_coe_le_norm (unitTimeAffine a b hab t)

/-- Autonomous equations satisfied almost everywhere are preserved by
restriction, with the same physical right-hand side. -/
theorem circle_parabolic_restriction_pde
    (a b : unitInterval) (hab : a < b)
    (F : CircleSobolevSpace T 4 → CircleL2 T) (U : CircleParabolicSpace T τ)
    (hPDE : ∀ᵐ t : unitInterval ∂volume,
      circleParabolicTimeDerivative T τ U t = F (circleParabolicH4 T τ U t)) :
    let τ' := τ*((b:ℝ)-(a:ℝ))
    let R := circleParabolicRestriction T τ a b hab U
    ∀ᵐ t : unitInterval ∂volume,
      circleParabolicTimeDerivative T τ' R t = F (circleParabolicH4 T τ' R t) := by
  have hcomponents := circle_parabolic_restriction_components T τ a b hab U
  have hH4 := hcomponents.2.1
  have hv := hcomponents.2.2.1
  filter_upwards [hH4,hv,(unit_time_affine_quasi_preserving a b hab).ae hPDE]
    with t hft hvt ht
  exact hvt.trans (ht.trans (congrArg F hft.symm))

private theorem equal_parameter_witness {A : Type*} {B : A → Type*}
    {P : ∀ a, B a → Prop} {a b : A}
    (hab : a = b) (x : B a) (hx : P a x) : ∃ y : B b, P b y := by
  subst b
  exact ⟨x,hx⟩

private theorem pair_witnesses {X Y : Type*} {P : X → Prop} {Q : Y → Prop}
    (hx : ∃ x, P x) (hy : ∃ y, Q y) : ∃ x y, P x ∧ Q y := by
  obtain ⟨x,hx⟩ := hx
  obtain ⟨y,hy⟩ := hy
  exact ⟨x,y,hx,hy⟩

private theorem restriction_at_duration
    (a b : unitInterval) (hab : a < b) (σ : ℝ)
    (hσ : τ*((b:ℝ)-(a:ℝ)) = σ) (U : CircleParabolicSpace T τ) :
    ∃ R : CircleParabolicSpace T σ,
      (∀ t, circleParabolicCurve T σ R t =
        circleParabolicCurve T τ U (unitTimeAffine a b hab t)) ∧
      ((circleParabolicH4 T σ R : unitInterval → CircleSobolevSpace T 4) =ᵐ[volume]
        fun t => circleParabolicH4 T τ U (unitTimeAffine a b hab t)) ∧
      ((circleParabolicTimeDerivative T σ R : unitInterval → CircleL2 T) =ᵐ[volume]
        fun t => circleParabolicTimeDerivative T τ U (unitTimeAffine a b hab t)) ∧
      circleParabolicInitialValue T σ R = circleParabolicCurve T τ U a ∧
      ‖circleParabolicCurve T σ R‖ ≤ ‖circleParabolicCurve T τ U‖ ∧
      ∀ F : CircleSobolevSpace T 4 → CircleL2 T,
        (∀ᵐ t : unitInterval ∂volume,
          circleParabolicTimeDerivative T τ U t = F (circleParabolicH4 T τ U t)) →
        ∀ᵐ t : unitInterval ∂volume,
          circleParabolicTimeDerivative T σ R t = F (circleParabolicH4 T σ R t) := by
  refine equal_parameter_witness (B := fun σ : ℝ => ↥(CircleParabolicSpace T σ))
    (P := fun σ (R : CircleParabolicSpace T σ) =>
      (∀ t, circleParabolicCurve T σ R t =
        circleParabolicCurve T τ U (unitTimeAffine a b hab t)) ∧
      ((circleParabolicH4 T σ R : unitInterval → CircleSobolevSpace T 4) =ᵐ[volume]
        fun t => circleParabolicH4 T τ U (unitTimeAffine a b hab t)) ∧
      ((circleParabolicTimeDerivative T σ R : unitInterval → CircleL2 T) =ᵐ[volume]
        fun t => circleParabolicTimeDerivative T τ U (unitTimeAffine a b hab t)) ∧
      circleParabolicInitialValue T σ R = circleParabolicCurve T τ U a ∧
      ‖circleParabolicCurve T σ R‖ ≤ ‖circleParabolicCurve T τ U‖ ∧
      ∀ F : CircleSobolevSpace T 4 → CircleL2 T,
        (∀ᵐ t : unitInterval ∂volume,
          circleParabolicTimeDerivative T τ U t = F (circleParabolicH4 T τ U t)) →
        ∀ᵐ t : unitInterval ∂volume,
          circleParabolicTimeDerivative T σ R t = F (circleParabolicH4 T σ R t))
    hσ (circleParabolicRestriction T τ a b hab U) ?_
  have hc := circle_parabolic_restriction_components T τ a b hab U
  exact ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2,
    fun F hF => circle_parabolic_restriction_pde T τ a b hab F U hF⟩

/-- Both half-interval restrictions have the same physical duration tau/2.
This package avoids dependent duration casts in overlap and restart proofs. -/
theorem circle_parabolic_half_restrictions (U : CircleParabolicSpace T τ) :
    let m : unitInterval := ⟨1/2,by constructor <;> norm_num⟩
    let l := unitTimeAffine 0 m (by change (0:ℝ) < 1/2; norm_num)
    let r := unitTimeAffine m 1 (by change (1/2:ℝ) < 1; norm_num)
    ∃ R₀ R₁ : CircleParabolicSpace T (τ/2),
      ((∀ t, circleParabolicCurve T (τ/2) R₀ t = circleParabolicCurve T τ U (l t)) ∧
        ((circleParabolicH4 T (τ/2) R₀ : unitInterval → CircleSobolevSpace T 4) =ᵐ[volume]
          fun t => circleParabolicH4 T τ U (l t)) ∧
        ((circleParabolicTimeDerivative T (τ/2) R₀ : unitInterval → CircleL2 T) =ᵐ[volume]
          fun t => circleParabolicTimeDerivative T τ U (l t)) ∧
        circleParabolicInitialValue T (τ/2) R₀ = circleParabolicInitialValue T τ U ∧
        ‖circleParabolicCurve T (τ/2) R₀‖ ≤ ‖circleParabolicCurve T τ U‖ ∧
        ∀ F : CircleSobolevSpace T 4 → CircleL2 T,
          (∀ᵐ t : unitInterval ∂volume,
            circleParabolicTimeDerivative T τ U t = F (circleParabolicH4 T τ U t)) →
          ∀ᵐ t : unitInterval ∂volume,
            circleParabolicTimeDerivative T (τ/2) R₀ t = F (circleParabolicH4 T (τ/2) R₀ t)) ∧
      ((∀ t, circleParabolicCurve T (τ/2) R₁ t = circleParabolicCurve T τ U (r t)) ∧
        ((circleParabolicH4 T (τ/2) R₁ : unitInterval → CircleSobolevSpace T 4) =ᵐ[volume]
          fun t => circleParabolicH4 T τ U (r t)) ∧
        ((circleParabolicTimeDerivative T (τ/2) R₁ : unitInterval → CircleL2 T) =ᵐ[volume]
          fun t => circleParabolicTimeDerivative T τ U (r t)) ∧
        circleParabolicInitialValue T (τ/2) R₁ = circleParabolicCurve T τ U m ∧
        ‖circleParabolicCurve T (τ/2) R₁‖ ≤ ‖circleParabolicCurve T τ U‖ ∧
        ∀ F : CircleSobolevSpace T 4 → CircleL2 T,
          (∀ᵐ t : unitInterval ∂volume,
            circleParabolicTimeDerivative T τ U t = F (circleParabolicH4 T τ U t)) →
          ∀ᵐ t : unitInterval ∂volume,
            circleParabolicTimeDerivative T (τ/2) R₁ t = F (circleParabolicH4 T (τ/2) R₁ t)) := by
  dsimp only
  let m : unitInterval := ⟨1/2,by constructor <;> norm_num⟩
  have h₀ : (0:unitInterval) < m := by change (0:ℝ) < 1/2; norm_num
  have h₁ : m < (1:unitInterval) := by change (1/2:ℝ) < 1; norm_num
  exact pair_witnesses
    (restriction_at_duration T τ 0 m h₀ (τ/2) (by change τ*((1/2:ℝ)-0) = τ/2; ring) U)
    (restriction_at_duration T τ m 1 h₁ (τ/2) (by change τ*(1-(1/2:ℝ)) = τ/2; ring) U)

end Lemniscate
