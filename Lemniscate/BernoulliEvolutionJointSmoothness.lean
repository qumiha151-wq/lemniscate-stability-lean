import Lemniscate.BernoulliClosedSobolevPaths
import Lemniscate.CircleSobolevScaleFlow
import Lemniscate.BanachScaleTimeRegularity
import Lemniscate.PeriodicParabolicGlobalContinuousVelocity
import Lemniscate.PeriodicSmoothJointEvaluation

/-! Smoothness of the existing modulated evolution. The only quantitative
input concerns its low H2 graph neighborhood. Higher spatial norms need not
be small, and the initial endpoint is retained throughout. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Set
open scoped ContDiff Topology NNReal

set_option maxHeartbeats 800000 in
theorem bernoulli_evolution_joint_smooth
    (T : ℝ) [Fact (0<T)] (q p : C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (τ : ℝ) (hτ : 0<τ) (η : ℝ) (x₀ : CircleSobolevSpace T 2)
    (D : BernoulliNormalGraphEvolution T q p ψ τ hτ η x₀)
    (hk : ContDiff ℝ ∞ (fun x : ℝ => (circleBernoulliBackground T q p).k (x:AddCircle T)))
    (hks : ContDiff ℝ ∞ (fun x : ℝ => (circleBernoulliBackground T q p).ks (x:AddCircle T)))
    (hkss : ContDiff ℝ ∞ (fun x : ℝ => (circleBernoulliBackground T q p).kss (x:AddCircle T)))
    (hksss : ContDiff ℝ ∞ (fun x : ℝ => (circleBernoulliBackground T q p).ksss (x:AddCircle T)))
    (heta : ContDiff ℝ ∞ (fun x : ℝ => (circleBernoulliBackground T q p).eta (x:AddCircle T)))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => (circleBernoulliBackground T q p).b (x:AddCircle T)))
    (hgraph : ∀ f : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖<η →
      f ∈ circleNormalGraphDomain T (circleBernoulliBackground T q p) ∧
        circleNormalGraphRotationFunctional T ψ
          (circleNormalGraphRotationField T (circleBernoulliBackground T q p)
            (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))) ≠ 0) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => circleSobolevH1Embedding T
        (circleSobolevInclusion T 1 (D.u (Real.toNNReal z.1))) (z.2:AddCircle T))
      (Ici (0:ℝ) ×ˢ (univ:Set ℝ)) ∧
    ContDiffOn ℝ ∞ D.theta (Ici (0:ℝ)) := by
  let K := circleBernoulliBackground T q p
  obtain ⟨w,hw,hvalue,hzero,hpositive⟩ :=
    bernoulli_closed_sobolev_paths T q p ψ τ hτ η x₀ D
  have hscale (n : ℕ) :=
    circle_modulated_flow_sobolev_scale T K (15/2) ψ hk hks hkss hksss heta hb (n+2)
  choose O R hOpen hR hOmega hmem hRvalue using hscale
  let f4 (n : ℕ) (t : ℝ) : CircleSobolevSpace T 4 :=
    circleSobolevTruncation T 4 (n+7) (by omega) (w (n+5) t)
  have hf4value (n : ℕ) (t : ℝ) (ht : 0≤t) :
      circleSobolevCoordinate T 4 0 (f4 n t)=
        circleSobolevCoordinate T 2 0 (D.u (Real.toNNReal t)) := by
    simpa only [f4,circle_sobolev_truncation_value] using hvalue (n+5) t ht
  have hf4eq (n : ℕ) (t : ℝ) (ht : 0≤t) : f4 n t=f4 0 t := by
    apply circle_sobolev_value_injective T 4
    exact (hf4value n t ht).trans (hf4value 0 t ht).symm
  have hlow (n : ℕ) (t : ℝ) (ht : 0≤t) :
      circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f4 n t))=
        D.u (Real.toNNReal t) := by
    apply circle_sobolev_value_injective T 2
    exact hf4value n t ht
  have hpointsmall (m : ℕ) (r : unitInterval) :
      ‖circleParabolicCurve T τ (D.U m) r‖<η :=
    (((circleParabolicCurve T τ (D.U m)).norm_coe_le_norm r).trans
      (norm_fst_le (D.U m).val)).trans_lt (D.segmentSmall m)
  have hsmall (t : ℝ≥0) : ‖D.u t‖<η := by
    rcases eq_or_lt_of_le t.property with hz | ht
    · have ht0 : t=0 := Subtype.ext hz.symm
      have hc : circleParabolicSegmentTime τ hτ 0 0=(0:ℝ≥0) := by
        apply Subtype.ext
        norm_num [circleParabolicSegmentTime]
      rw [ht0,← hc,D.segments]
      exact hpointsmall 0 0
    · obtain ⟨m,r,hr,hlo,heq⟩ :=
        circle_parabolic_interior_time τ hτ t ht t le_rfl
      rw [← heq,D.segments]
      exact hpointsmall m r
  have hO (n : ℕ) : MapsTo (w (n+5)) (Ici (0:ℝ)) (O n) := by
    intro t ht
    apply (hmem n _).mpr
    exact hgraph _ (by rw [hlow n t ht]; exact hsmall _)
  let velocity : ℝ → C(AddCircle T,ℂ) := fun t =>
    circleSobolevH1Embedding T (circleSobolevInclusion T 1 (R 0 (w 5 t)))
  have hvelocity : ContinuousOn velocity (Ici (0:ℝ)) :=
    (circleSobolevH1Embedding T).continuous.comp_continuousOn
      ((circleSobolevInclusion T 1).continuous.comp_continuousOn
        ((hR 0).continuousOn.comp (hw 5) (hO 0)))
  have hvelocityvalue (t : ℝ) : circleContinuousL2 T (velocity t)=
      circleSobolevCoordinate T 2 0 (R 0 (w 5 t)) := by
    dsimp only [velocity]
    rw [circle_sobolev_h1_embedding_l2]
    rfl
  have hAE (m : ℕ) : ∀ᵐ r ∂volume,
      circleParabolicTimeDerivative T τ (D.U m) r =
        circleContinuousL2 T (velocity (circleParabolicSegmentTime τ hτ m r)) := by
    filter_upwards [D.equation m,circle_parabolic_value_ae T τ (D.U m)] with r hPDE hcurve
    let t : ℝ≥0 := circleParabolicSegmentTime τ hτ m r
    have htime : Real.toNNReal (t:ℝ)=t := Subtype.ext (Real.coe_toNNReal _ t.property)
    have hh4 : circleParabolicH4 T τ (D.U m) r=f4 0 t := by
      apply circle_sobolev_value_injective T 4
      calc
        _ = circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ (D.U m) r) := hcurve.symm
        _ = circleSobolevCoordinate T 2 0 (D.u t) :=
          congrArg (circleSobolevCoordinate T 2 0) (D.segments m r).symm
        _ = _ := by rw [hf4value 0 t t.property,htime]
    rw [hPDE,hh4,hvelocityvalue]
    exact (hRvalue 0 _ (hO 0 t.property)).symm
  have htime := circle_global_hasDerivWithinAt_of_continuous_velocity T τ hτ
    D.u D.U D.segments velocity hvelocity hAE
  let L (n : ℕ) : CircleSobolevSpace T (n+2) →L[ℝ] CircleL2 T :=
    (circleSobolevCoordinate T (n+2) 0).restrictScalars ℝ
  have hbase (n : ℕ) (t : ℝ) (ht : t ∈ Ici (0:ℝ)) :
      HasDerivWithinAt (fun s => L n (w n s))
        (L n (R n (w (n+5) t))) (Ici (0:ℝ)) t := by
    let toL2 : C(AddCircle T,ℂ) →L[ℝ] CircleL2 T :=
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).restrictScalars ℝ
    have hd := toL2.hasFDerivAt.comp_hasDerivWithinAt t (htime t ht)
    change HasDerivWithinAt
      (fun s => circleContinuousL2 T (circleSobolevH1Embedding T
        (circleSobolevInclusion T 1 (D.u (Real.toNNReal s)))))
      (circleContinuousL2 T (velocity t)) (Ici (0:ℝ)) t at hd
    have hcoord : HasDerivWithinAt
        (fun s => circleSobolevCoordinate T 2 0 (D.u (Real.toNNReal s)))
        (circleContinuousL2 T (velocity t)) (Ici (0:ℝ)) t := by
      simpa only [Function.comp_def,circle_sobolev_h1_embedding_l2,
        circle_sobolev_inclusion_coordinate] using! hd
    have hvR : circleContinuousL2 T (velocity t)=L n (R n (w (n+5) t)) := by
      rw [hvelocityvalue,hRvalue 0 _ (hO 0 ht)]
      change _=circleSobolevCoordinate T (n+2) 0 (R n (w (n+5) t))
      rw [hRvalue n _ (hO n ht)]
      exact congrArg (circleNormalGraphModulatedFlow T K (15/2) ψ) (hf4eq n t ht).symm
    apply (hcoord.congr_deriv hvR).congr_of_mem _ ht
    intro s hs
    exact hvalue n s hs
  have hsmooth := banach_scale_time_smooth
    (fun n => CircleSobolevSpace T (n+2)) 0 5 L
    (fun n => circle_sobolev_value_injective T (n+2)) w hw O R hR hO hbase
  have hQ (n : ℕ) (t : ℝ) (ht : 0≤t) :
      circleSobolevCoordinate T (n+2) 0 (w n t)=circleContinuousL2 T
        (circleSobolevH1Embedding T (circleSobolevInclusion T 1 (D.u (Real.toNNReal t)))) := by
    rw [circle_sobolev_h1_embedding_l2]
    exact hvalue n t ht
  refine ⟨circle_joint_smooth_of_sobolev_paths T 0 w hsmooth.2 _ hQ,?_⟩
  have hOmegaSmooth : ContDiffOn ℝ ∞
      (fun t => circleNormalGraphAngularVelocity T K (15/2) ψ (f4 0 t)) (Ici (0:ℝ)) :=
    (hOmega 0).comp (hsmooth.2 5) (hO 0)
  have hOmegaValue (t : ℝ) (ht : 0≤t) :
      (D.omega t:ℂ)=circleNormalGraphAngularVelocity T K (15/2) ψ (f4 0 t) := by
    rcases eq_or_lt_of_le ht with hz | hp
    · subst t
      rw [D.omegaZero,D.initialOmegaValue]
      congr 1
      apply circle_sobolev_value_injective T 4
      rw [hf4value 0 0 le_rfl]
      have hi := D.initialValues 5 0
      have hc : circleParabolicSegmentTime τ hτ 0 0=(0:ℝ≥0) := by
        apply Subtype.ext
        norm_num [circleParabolicSegmentTime]
      simpa only [Real.toNNReal_zero,← D.segments 0 0,hc,
        circle_sobolev_inclusion_coordinate] using! hi
    · rw [D.omegaValue ⟨t,hp⟩]
      congr 1
      apply circle_sobolev_value_injective T 4
      exact (D.positiveValue 5 ⟨t,hp⟩).trans
        ((congrArg (fun r => circleSobolevCoordinate T 2 0 (D.u r))
          (Subtype.ext (Real.coe_toNNReal t hp.le)).symm).trans (hf4value 0 t hp.le).symm)
  have homegaSmooth : ContDiffOn ℝ ∞ D.omega (Ici (0:ℝ)) :=
    (Complex.reCLM.contDiff.comp_contDiffOn hOmegaSmooth).congr
      (fun t ht => congrArg Complex.re (hOmegaValue t ht))
  apply (contDiffOn_infty_iff_derivWithin (uniqueDiffOn_Ici (0:ℝ))).mpr
  refine ⟨fun t ht => (D.thetaDerivative t ht).differentiableWithinAt,?_⟩
  exact homegaSmooth.congr
    (fun t ht => (D.thetaDerivative t ht).derivWithin (uniqueDiffOn_Ici (0:ℝ) t ht))

end Lemniscate
