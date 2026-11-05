import Lemniscate.BernoulliPhysicalGraphStability
import Lemniscate.BernoulliLocalFlowChartData
import Lemniscate.PeriodicParabolicLocalUniqueness
import Lemniscate.PeriodicParabolicInteriorTime
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace Lemniscate
open Complex Set Filter MeasureTheory
open scoped ContDiff Topology NNReal ENNReal ComplexConjugate

private theorem identification_positive_radius_transport
    {P : ℝ → Prop} {Q : Prop} (h : ∃ d>0,P d)
    (H : ∀ d,0<d → P d → Q) : Q := by
  rcases h with ⟨d,hd,hP⟩
  exact H d hd hP

private theorem local_angle_identification
    (b d : ℝ) (hd : 0<d) (hdb : d<b) (f g : ℝ → ℝ)
    (hf₀ : f 0=0) (hftrace : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 0))
    (hf : ContDiffOn ℝ 1 f (Ioo 0 b)) (hg : Continuous g)
    (hderiv : ∀ r ∈ Ioo (0:ℝ) d,HasDerivAt g (deriv f r) r) :
    ∀ r ∈ Icc (0:ℝ) d,f r=g r-g 0 := by
  have hfd (r : ℝ) (hr : r∈Ioo (0:ℝ) d) : DifferentiableAt ℝ f r :=
    (hf.contDiffAt (isOpen_Ioo.mem_nhds ⟨hr.1,hr.2.trans hdb⟩)).differentiableAt (by simp)
  obtain ⟨c,hc⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo
    (fun r hr => (hfd r hr).differentiableWithinAt)
    (fun r hr => (hderiv r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hderiv r hr).deriv.symm)
  have heq₀ : f =ᶠ[𝓝[>] (0:ℝ)] (fun r => g r+c) := by
    filter_upwards [Ioo_mem_nhdsGT hd] with r hr using hc hr
  have hg₀ : Tendsto (fun r => g r+c) (𝓝[>] (0:ℝ)) (𝓝 (g 0+c)) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add_const c
  have hc₀ : g 0+c=0 := tendsto_nhds_unique hg₀ (hftrace.congr' heq₀)
  have heqD : f =ᶠ[𝓝[<] d] (fun r => g r+c) := by
    filter_upwards [Ioo_mem_nhdsLT hd] with r hr using hc hr
  have hfD : Tendsto f (𝓝[<] d) (𝓝 (f d)) :=
    (hf.contDiffAt (isOpen_Ioo.mem_nhds ⟨hd,hdb⟩)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hgD : Tendsto (fun r => g r+c) (𝓝[<] d) (𝓝 (g d+c)) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add_const c
  have hD : f d=g d+c := tendsto_nhds_unique hfD (hgD.congr' heqD.symm)
  intro r hr
  rcases hr.1.eq_or_lt with hzero | hpos
  · subst r
    simp only [hf₀,sub_self]
  · rcases hr.2.eq_or_lt with hend | hlt
    · subst r
      linarith only [hD,hc₀]
    · have hh := hc ⟨hpos,hlt⟩
      linarith only [hh,hc₀]

variable (T : ℝ) [Fact (0<T)]

set_option maxHeartbeats 800000 in
/-- A phase-fixed local chart of a given flow agrees with the actual
global normal-height solution and its accumulated rotation on one closed
forward interval. Only continuous H2 smallness enters uniqueness. -/
theorem bernoulli_local_flow_identification
    (e : ℝ ≃o ℝ) (q p : C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (τ : ℝ) (hτ : 0<τ) (η : ℝ) (z₀ : CircleSobolevSpace T 2)
    (D : BernoulliNormalGraphEvolution T q p ψ τ hτ η z₀)
    (σ₀ : ℝ≥0) (a α₀ : ℝ) (ρ : ℝ → ℝ) (p₀ : ℂ)
    (χ₀ : ℝ ≃o ℝ) (Y : ℝ → ℝ → ℂ)
    (C : BernoulliLocalFlowChart T e q p ψ η (D.u σ₀)
      a (σ₀:ℝ) α₀ ρ p₀ χ₀ Y)
    (hunique : ∀ d : ℝ,0<d → ∀ R V : CircleParabolicSpace T d,
      circleParabolicInitialValue T d R=circleParabolicInitialValue T d V →
      ‖circleParabolicCurve T d R‖<η → ‖circleParabolicCurve T d V‖<η →
      (∀ᵐ r : unitInterval ∂volume,circleParabolicTimeDerivative T d R r=
        circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
          (circleParabolicH4 T d R r)) →
      (∀ᵐ r : unitInterval ∂volume,circleParabolicTimeDerivative T d V r=
        circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
          (circleParabolicH4 T d V r)) → R=V) :
    ∃ d>0,d<C.comparisonRadius ∧ ∀ r∈Icc (0:ℝ) d,
      circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (C.high r))=
        D.u (Real.toNNReal ((σ₀:ℝ)+r)) ∧
      C.angle r=D.theta ((σ₀:ℝ)+r)-D.theta (σ₀:ℝ) := by
  let flow := circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
  let low := fun r : ℝ => circleSobolevInclusion T 2
    (circleSobolevInclusion T 3 (C.high r))
  have hcover (σ : ℝ≥0) (hσ : 0<σ) :
      ∃ (m : ℕ) (r : unitInterval),0<(r:ℝ) ∧ (r:ℝ)<1 ∧
        circleParabolicSegmentTime τ hτ m r=σ := by
    have hσR : 0<(σ:ℝ) := hσ
    obtain ⟨m,r,hr₁,hrlow,heq⟩ :=
      circle_parabolic_interior_time τ hτ (σ:ℝ) hσR σ le_rfl
    exact ⟨m,r,(lt_min (by norm_num) (div_pos hσR hτ)).trans_le hrlow,hr₁,heq⟩
  have hsmall (m : ℕ) : ‖circleParabolicCurve T τ (D.U m)‖<η :=
    (norm_fst_le (D.U m).val).trans_lt (D.segmentSmall m)
  have hchart (d : ℝ) (hd : 0<d) (hdC : d<C.comparisonRadius) :
      ∃ R : CircleParabolicSpace T d,
        (∀ r : unitInterval,circleParabolicCurve T d R r=low (d*(r:ℝ))) ∧
        ‖circleParabolicCurve T d R‖<η ∧
        ∀ᵐ r : unitInterval ∂volume,circleParabolicTimeDerivative T d R r=
          flow (circleParabolicH4 T d R r) := by
    refine (C.comparison d hd hdC.le).imp ?_
    intro R hR
    exact ⟨hR.1,hR.2.2.1,hR.2.2.2.2.1⟩
  refine identification_positive_radius_transport
    (circle_parabolic_global_local_uniqueness T τ hτ D.u D.U D.segments hcover
      flow η hsmall D.equation hunique σ₀ C.comparisonRadius C.comparisonPositive
      low C.initial hchart) ?_
  intro d hd hdata
  have hdC : d<C.comparisonRadius := hdata.1
  have hheight := hdata.2
  have hdtime : d<C.timeRadius := hdC.trans C.comparisonShort
  have hangleOmega : ∀ r ∈ Ioo (0:ℝ) d,((deriv C.angle r:ℝ):ℂ)=
      circleNormalGraphAngularVelocity T (circleBernoulliBackground T q p) (15/2) ψ
        (C.high r) := by
    refine Exists.elim (C.comparison d hd hdC.le) ?_
    intro R hR
    intro r hr
    have hunit : r/d∈Ioo (0:ℝ) 1 :=
      ⟨div_pos hr.1 hd,(div_lt_one hd).mpr hr.2⟩
    have hscale : d*(r/d)=r := by field_simp [hd.ne']
    simpa only [hscale] using! hR.2.2.2.2.2 (r/d) hunit
  have hclock (r : ℝ) (hr : r∈Ioo (0:ℝ) d) : 0<(σ₀:ℝ)+r :=
    add_pos_of_nonneg_of_pos σ₀.property hr.1
  have hhigh (r : ℝ) (hr : r∈Ioo (0:ℝ) d) :
      C.high r=circleSobolevInclusion T 4 (D.w 5 ⟨(σ₀:ℝ)+r,hclock r hr⟩) := by
    apply circle_sobolev_value_injective T 4
    change circleSobolevCoordinate T 2 0 (low r)=
      circleSobolevCoordinate T 5 0 (D.w 5 ⟨(σ₀:ℝ)+r,hclock r hr⟩)
    rw [hheight r ⟨hr.1.le,hr.2.le⟩,Real.toNNReal_of_nonneg (hclock r hr).le]
    exact (D.positiveValue 5 ⟨(σ₀:ℝ)+r,hclock r hr⟩).symm
  have hangleDerivative (r : ℝ) (hr : r∈Ioo (0:ℝ) d) :
      deriv C.angle r=D.omega ((σ₀:ℝ)+r) := by
    apply Complex.ofReal_injective
    exact (hangleOmega r hr).trans
      ((congrArg (circleNormalGraphAngularVelocity T (circleBernoulliBackground T q p)
        (15/2) ψ) (hhigh r hr)).trans
          (D.omegaValue ⟨(σ₀:ℝ)+r,hclock r hr⟩).symm)
  have htheta (r : ℝ) (hr : r∈Ioo (0:ℝ) d) :
      HasDerivAt (fun s : ℝ => D.theta ((σ₀:ℝ)+s))
        (D.omega ((σ₀:ℝ)+r)) r := by
    have hh := (D.thetaDerivative ((σ₀:ℝ)+r) (hclock r hr).le).hasDerivAt
      (Ici_mem_nhds (hclock r hr))
    simpa only [Function.comp_def,one_smul] using!
      hh.scomp r ((hasDerivAt_id r).const_add (σ₀:ℝ))
  have hangle := local_angle_identification C.timeRadius d hd hdtime C.angle
    (fun r : ℝ => D.theta ((σ₀:ℝ)+r)) C.angleZero C.angleTrace C.angleSmooth
    (D.thetaContinuous.comp (continuous_const.add continuous_id))
    (fun r hr => by rw [hangleDerivative r hr]; exact htheta r hr)
  refine ⟨d,hd,hdC,?_⟩
  intro r hr
  exact ⟨hheight r hr,by simpa only [add_zero] using! hangle r hr⟩

end Lemniscate
