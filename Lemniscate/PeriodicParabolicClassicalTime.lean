import Lemniscate.PeriodicFiniteParabolicSolution
import Lemniscate.PeriodicSobolevDerivatives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-! A continuous spatial representative of the physical velocity gives the
actual time derivative in C(circle), hence at every spatial point. The
recorded Bochner primitive is lifted through the injective L2 embedding.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped Topology

private theorem unit_primitive_lift_hasDerivWithinAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (hL : Function.Injective L)
    (q : unitInterval → E) (v : unitInterval → F) (τ : ℝ)
    (hv : Integrable v volume)
    (hq : ∀ t : unitInterval, L (q t)-L (q 0)=τ • (∫ s in Iic t, v s ∂volume))
    (r₀ : ℝ) (hr₀ : 0 ≤ r₀) (hr₀1 : r₀ < 1)
    (V : C(Icc r₀ (1:ℝ),E))
    (hV : ∀ᵐ (t : unitInterval) ∂(volume : Measure unitInterval), r₀ ≤ (t:ℝ) →
      v t=L (V (Set.projIcc r₀ 1 hr₀1.le (t:ℝ))))
    (r : ℝ) (hr : r₀ ≤ r) (hr1 : r ≤ 1) :
    HasDerivWithinAt (fun s : ℝ => q (Set.projIcc (0:ℝ) 1 zero_le_one s))
      (τ • V (Set.projIcc r₀ 1 hr₀1.le r)) (Icc r₀ 1) r := by
  let clamp : ℝ → unitInterval := Set.projIcc (0:ℝ) 1 zero_le_one
  have hclamp (t : unitInterval) : clamp (t:ℝ)=t := Set.projIcc_val zero_le_one t
  let w : ℝ → F := fun s => v (clamp s)
  let W : ℝ → E := fun s => V (Set.projIcc r₀ 1 hr₀1.le s)
  have hW : Continuous W := V.continuous.comp continuous_projIcc
  have hwOn : IntegrableOn w (Icc (0:ℝ) 1) volume := by
    apply (unitInterval.measurePreserving_coe.integrable_comp_emb
      unitInterval.measurableEmbedding_coe).mp
    simpa only [Function.comp_def,w,hclamp] using hv
  have hw01 : IntervalIntegrable w volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hwOn
  have hint (t : unitInterval) : IntervalIntegrable w volume 0 (t:ℝ) := by
    apply hw01.mono_set
    rw [uIcc_of_le t.property.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl t.property.2
  have hreal (t : unitInterval) :
      L (q t)-L (q 0)=τ • (∫ s in (0:ℝ)..(t:ℝ), w s) := by
    rw [← unit_interval_setIntegral w t]
    simpa only [w,hclamp] using hq t
  have hBrestrict : ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1),
      r₀ ≤ s → w s=L (W s) := by
    rw [← unitInterval.measurePreserving_coe.map_eq]
    apply unitInterval.measurableEmbedding_coe.ae_map_iff.mpr
    simpa only [w,W,hclamp] using hV
  have hB : ∀ᵐ s ∂volume, s ∈ Icc (0:ℝ) 1 → r₀ ≤ s → w s=L (W s) :=
    (ae_restrict_iff' measurableSet_Icc).mp hBrestrict
  let a : unitInterval := ⟨r₀,hr₀,hr₀1.le⟩
  let P : ℝ → E := fun s => q a+τ • (∫ x in r₀..s, W x)
  have hP (t : Icc r₀ (1:ℝ)) :
      q ⟨(t:ℝ),hr₀.trans t.property.1,t.property.2⟩=P (t:ℝ) := by
    let u : unitInterval := ⟨(t:ℝ),hr₀.trans t.property.1,t.property.2⟩
    have hdiff : L (q u)-L (q a)=τ • (∫ x in r₀..(t:ℝ), w x) := by
      calc
        _ = (L (q u)-L (q 0))-(L (q a)-L (q 0)) := by abel
        _ = τ • (∫ x in (0:ℝ)..(u:ℝ), w x)-
            τ • (∫ x in (0:ℝ)..(a:ℝ), w x) :=
          congrArg₂ HSub.hSub (hreal u) (hreal a)
        _ = _ := by
          rw [← smul_sub,intervalIntegral.integral_interval_sub_left (hint u) (hint a)]
    have heq : (∫ x in r₀..(t:ℝ), w x)=∫ x in r₀..(t:ℝ), L (W x) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hB] with s hs hst
      rw [uIoc_of_le t.property.1] at hst
      exact hs ⟨hr₀.trans hst.1.le,hst.2.trans t.property.2⟩ hst.1.le
    apply hL
    calc
      L (q u) = L (q a)+τ • (∫ x in r₀..(t:ℝ), w x) := by rw [← hdiff]; abel
      _ = L (q a)+τ • L (∫ x in r₀..(t:ℝ), W x) := by
        rw [heq,L.intervalIntegral_comp_comm (hW.intervalIntegrable _ _)]
      _ = L (P (t:ℝ)) := by simp only [P,map_add,map_smul]
  have hPd : HasDerivAt P (τ • W r) r :=
    ((intervalIntegral.integral_hasDerivAt_right (hW.intervalIntegrable r₀ r)
      hW.aestronglyMeasurable.stronglyMeasurableAtFilter hW.continuousAt).const_smul τ).const_add (q a)
  have hwithin : HasDerivWithinAt P (τ • W r) (Icc r₀ (1:ℝ)) r :=
    hPd.hasDerivWithinAt
  apply hwithin.congr_of_mem ?_ (show r ∈ Icc r₀ (1:ℝ) from ⟨hr,hr1⟩)
  intro s hs
  change q (Set.projIcc (0:ℝ) 1 zero_le_one s)=P s
  rw [Set.projIcc_of_mem zero_le_one ⟨hr₀.trans hs.1,hs.2⟩]
  exact hP ⟨s,hs⟩

variable (T : ℝ) [Fact (0 < T)]

set_option maxHeartbeats 800000 in
/-- A continuous spatial representative of the actual physical velocity
gives the C(circle)-valued time derivative within the closed time interval,
including its one-sided endpoint values.
No classical time differentiability is assumed for the MR solution. -/
theorem circle_parabolic_hasDerivWithinAt_of_continuous_velocity
    (τ : ℝ) (U : CircleParabolicSpace T τ)
    (r₀ : ℝ) (hr₀ : 0 ≤ r₀) (hr₀1 : r₀ < 1)
    (V : C(Icc r₀ (1:ℝ),C(AddCircle T,ℂ)))
    (hV : ∀ᵐ (t : unitInterval) ∂(volume : Measure unitInterval), r₀ ≤ (t:ℝ) →
      circleParabolicTimeDerivative T τ U t=
        circleContinuousL2 T (V (Set.projIcc r₀ 1 hr₀1.le (t:ℝ))))
    (r : ℝ) (hr : r₀ ≤ r) (hr1 : r ≤ 1) :
    let q : ℝ → C(AddCircle T,ℂ) := fun s => circleSobolevH1Embedding T
      (circleSobolevInclusion T 1
        (circleParabolicCurve T τ U (Set.projIcc (0:ℝ) 1 zero_le_one s)))
    HasDerivWithinAt q (τ • V (Set.projIcc r₀ 1 hr₀1.le r)) (Icc r₀ 1) r := by
  let u : unitInterval → C(AddCircle T,ℂ) := fun t => circleSobolevH1Embedding T
    (circleSobolevInclusion T 1 (circleParabolicCurve T τ U t))
  let L : C(AddCircle T,ℂ) →L[ℝ] CircleL2 T :=
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).restrictScalars ℝ
  have hL : Function.Injective L := by
    intro f g hfg
    change (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ) f =
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ) g at hfg
    exact ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle hfg
  have hLu (t : unitInterval) :
      L (u t)=circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U t) := by
    change circleContinuousL2 T (circleSobolevH1Embedding T
      (circleSobolevInclusion T 1 (circleParabolicCurve T τ U t))) = _
    rw [circle_sobolev_h1_embedding_l2]
    rfl
  have hprimitive (t : unitInterval) : L (u t)-L (u 0)=
      τ • (∫ s in Iic t, circleParabolicTimeDerivative T τ U s ∂volume) := by
    exact (congrArg₂ (fun a b : CircleL2 T => a-b) (hLu t) (hLu 0)).trans
      (circle_parabolic_integral_identity T τ U t)
  have hd := unit_primitive_lift_hasDerivWithinAt L hL u
    (circleParabolicTimeDerivative T τ U) τ
    (circle_parabolic_time_derivative_integrable T τ U)
    hprimitive r₀ hr₀ hr₀1 V hV r hr hr1
  exact hd

end Lemniscate
