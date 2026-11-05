import Lemniscate.PeriodicFiniteParabolicSolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-! An actual classical height with square-integrable spatial jet and
velocity belongs to the closed maximal-regularity space. Only interior
time derivatives are needed to recover its Bochner primitive. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

private theorem unit_primitive_of_interior_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (q : C(unitInterval,E)) (v : unitInterval → E) (τ : ℝ)
    (hv : Integrable v volume)
    (hd : ∀ r : ℝ, 0 < r → r < 1 →
      HasDerivAt (fun s => q (Set.projIcc (0:ℝ) 1 zero_le_one s))
        (τ • v (Set.projIcc (0:ℝ) 1 zero_le_one r)) r)
    (t : unitInterval) :
    q t-q 0 = τ • (∫ r in Iic t, v r ∂volume) := by
  let clamp : ℝ → unitInterval := Set.projIcc (0:ℝ) 1 zero_le_one
  have hclamp (r : unitInterval) : clamp (r:ℝ) = r :=
    Set.projIcc_val zero_le_one r
  let w : ℝ → E := fun r => v (clamp r)
  have hwOn : IntegrableOn w (Icc (0:ℝ) 1) volume := by
    apply (unitInterval.measurePreserving_coe.integrable_comp_emb
      unitInterval.measurableEmbedding_coe).mp
    simpa only [Function.comp_def,w,hclamp] using hv
  have hw01 : IntervalIntegrable w volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hwOn
  have hwt : IntervalIntegrable w volume 0 (t:ℝ) := by
    apply hw01.mono_set
    rw [uIcc_of_le t.property.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl t.property.2
  have hq : Continuous (fun r : ℝ => q (clamp r)) :=
    q.continuous.comp continuous_projIcc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    t.property.1 hq.continuousOn
    (fun r hr => hd r hr.1 (hr.2.trans_le t.property.2)) (hwt.smul τ)
  have hzero : clamp 0 = (0:unitInterval) := hclamp 0
  have hvalue : (∫ r in (0:ℝ)..(t:ℝ), τ • w r) = q t-q 0 := by
    simpa only [hclamp,hzero] using hFTC
  have hconvert : (∫ r in Iic t, v r ∂volume) =
      ∫ r in (0:ℝ)..(t:ℝ), w r := by
    rw [← unit_interval_setIntegral w t]
    simp only [w,hclamp]
  rw [hconvert,← intervalIntegral.integral_smul]
  exact hvalue.symm

variable (T : ℝ) [Fact (0 < T)]

local instance classicalParabolicSecondCountable (m : ℕ) :
    SecondCountableTopologyEither unitInterval (CircleSobolevSpace T m) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

/-- The genuine interior time equation, continuity up to the endpoints
and L2 integrability recover every constraint of the actual parabolic
space. Neither endpoint time derivatives nor continuous H4/velocity
representatives are required. -/
theorem periodic_classical_parabolic_space
    (τ : ℝ) (u : C(unitInterval,CircleSobolevSpace T 2))
    (W : unitInterval → CircleSobolevSpace T 4) (V : unitInterval → CircleL2 T)
    (hW : MemLp W 2 (volume : Measure unitInterval))
    (hV : MemLp V 2 (volume : Measure unitInterval))
    (hvalue : ∀ᵐ r ∂volume, circleSobolevCoordinate T 2 0 (u r) =
      circleSobolevCoordinate T 4 0 (W r))
    (hderiv : ∀ r : ℝ, 0 < r → r < 1 →
      HasDerivAt (fun s => circleSobolevCoordinate T 2 0
        (u (Set.projIcc (0:ℝ) 1 zero_le_one s)))
        (τ • V (Set.projIcc (0:ℝ) 1 zero_le_one r)) r) :
    ∃ U : CircleParabolicSpace T τ,
      circleParabolicCurve T τ U = u ∧
      circleParabolicH4 T τ U = hW.toLp W ∧
      circleParabolicTimeDerivative T τ U = hV.toLp V := by
  let H4 : CircleTimeH4 T := hW.toLp W
  let vel : CircleTimeL2 T := hV.toLp V
  have hH4 : (H4 : unitInterval → CircleSobolevSpace T 4) =ᵐ[volume] W :=
    MemLp.coeFn_toLp hW
  have hvel : (vel : unitInterval → CircleL2 T) =ᵐ[volume] V :=
    MemLp.coeFn_toLp hV
  have hVint : Integrable V volume := memLp_one_iff_integrable.mp
    (hV.mono_exponent (by norm_num : (1:ℝ≥0∞) ≤ 2))
  let q : C(unitInterval,CircleL2 T) :=
    ⟨fun r => circleSobolevCoordinate T 2 0 (u r),
      (circleSobolevCoordinate T 2 0).continuous.comp u.continuous⟩
  let z : CircleParabolicAmbient T := (u,(H4,vel))
  have hz : z ∈ circleParabolicSubmodule T τ := by
    apply (circle_parabolic_mem_iff T τ z).mpr
    constructor
    · have hu := ContinuousMap.coeFn_toLp (p := 2) volume (𝕜 := ℂ) u
      have huL := (circleSobolevCoordinate T 2 0).coeFn_compLpL
        (p := 2) (μ := (volume : Measure unitInterval))
        (ContinuousMap.toLp 2 volume ℂ u)
      have hWL := (circleSobolevCoordinate T 4 0).coeFn_compLpL
        (p := 2) (μ := (volume : Measure unitInterval)) H4
      apply Lp.ext
      filter_upwards [hu,huL,hWL,hH4,hvalue] with r hur huLr hWLr hH4r hvaluer
      change ((circleSobolevCoordinate T 2 0).compLpL 2 volume
        (ContinuousMap.toLp 2 volume ℂ u)) r =
        ((circleSobolevCoordinate T 4 0).compLpL 2 volume H4) r
      rw [huLr,hur,hWLr,hH4r]
      exact hvaluer
    · intro t
      change q t-q 0 = τ • (∫ r in Iic t, vel r ∂volume)
      have hi : (∫ r in Iic t, vel r ∂volume) = ∫ r in Iic t, V r ∂volume :=
        integral_congr_ae (ae_restrict_of_ae hvel)
      rw [hi]
      exact unit_primitive_of_interior_derivative q V τ hVint hderiv t
  exact ⟨⟨z,hz⟩,rfl,rfl,rfl⟩

end Lemniscate
