import Lemniscate.BernoulliClassicalModulationConverse
import Lemniscate.NormalGraphPhaseExtraction
import Lemniscate.PeriodicClassicalParabolicSpace
import Lemniscate.PeriodicCurvatureProfileEntry
import Mathlib.Topology.Order.ProjIcc

/-! A phase-fixed classical geometric height gives an actual modulated
maximal-regularity solution, including its initial H4 trace. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped Topology ENNReal ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

local instance classicalSolutionSobolevSecondCountable (m : ℕ) :
    SecondCountableTopologyEither unitInterval (CircleSobolevSpace T m) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

local instance classicalSolutionL2SecondCountable :
    SecondCountableTopologyEither unitInterval (CircleL2 T) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

set_option maxHeartbeats 800000 in
/-- The actual scalar geometric equation and constant adjoint phase
determine the modulated L2 velocity and angular velocity. Continuity of
the actual modulated vector field along the closed H4 trajectory then
gives a genuine parabolic solution, without any H4 smallness or endpoint
continuity assumption on the initially prescribed scalar angular speed. -/
theorem bernoulli_classical_parabolic_solution
    (e : ℝ ≃o ℝ) (he : ∀ u, e u=∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    (q p : C(AddCircle T,ℂ))
    (hq : ∀ x : ℝ, q (x:AddCircle T)=(bernoulliProfileQ (e.symm x):ℂ))
    (hp : ∀ x : ℝ, p (x:AddCircle T)=(bernoulliProfileP (e.symm x):ℂ))
    (ψ : CircleL2 T) (τ : ℝ) (hτ : 0 < τ)
    (u : C(unitInterval,CircleSobolevSpace T 2))
    (W : C(unitInterval,CircleSobolevSpace T 4))
    (hinc : ∀ r, circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (W r))=u r)
    (H : unitInterval → Fin 5 → C(AddCircle T,ℂ))
    (hreal : ∀ r j x, ((H r j x).re:ℂ)=H r j x)
    (hspatial : ∀ r, ∀ j : Fin 4, HasCircleDeriv T (H r j.castSucc) (H r j.succ))
    (hjet : ∀ r, ∀ j : Fin 4, circleSobolevContinuousJet T (W r) j=H r j.castSucc)
    (hfourth : ∀ r, circleSobolevCoordinate T 4 4 (W r)=circleContinuousL2 T (H r 4))
    (hdomain : ∀ r, W r ∈ circleNormalGraphDomain T (circleBernoulliBackground T q p))
    (hregular : ∀ r x, 0<1-3*bernoulliProfileQ (e.symm x)*(H r 0 (x:AddCircle T)).re)
    (V : ℝ → C(AddCircle T,ℂ)) (hVc : ContinuousOn V (Ioo (0:ℝ) 1))
    (hVreal : ∀ r ∈ Ioo (0:ℝ) 1, ∀ x, ((V r x).re:ℂ)=V r x)
    (ω : ℝ → ℝ)
    (hpoint : ∀ r ∈ Ioo (0:ℝ) 1, ∀ x : AddCircle T,
      HasDerivAt (fun s => H (Set.projIcc (0:ℝ) 1 zero_le_one s) 0 x)
        (τ • V r x) r)
    (hphase : ∀ r, circleNormalGraphRotationFunctional T ψ (circleContinuousL2 T (H r 0))=0)
    (hden : ∀ r, circleNormalGraphRotationFunctional T ψ
      (circleNormalGraphRotationField T (circleBernoulliBackground T q p) (u r))≠0)
    (hscalar : ∀ r ∈ Ioo (0:ℝ) 1,
      let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
      let β := bernoulliCurve ∘ φ
      let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
      let n := fun s : ℝ => I*t s
      let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
      let h := fun s : ℝ => (H (Set.projIcc (0:ℝ) 1 zero_le_one r) 0
        ((Real.sqrt 2*s):AddCircle T)).re
      let h₁ := fun s : ℝ => Real.sqrt 2*(H (Set.projIcc (0:ℝ) 1 zero_le_one r) 1
        ((Real.sqrt 2*s):AddCircle T)).re
      ∀ x : ℝ, (V r (x:AddCircle T)).re+
        ω r*((conj (t (x/Real.sqrt 2))*β (x/Real.sqrt 2)).re+
          ((conj (t (x/Real.sqrt 2))*β (x/Real.sqrt 2)).im+h (x/Real.sqrt 2))*
            h₁ (x/Real.sqrt 2)/(1-k (x/Real.sqrt 2)*h (x/Real.sqrt 2)))=
          normalGraphFlowRHS β n k h (15/2) (x/Real.sqrt 2))
    (hmod : Continuous (fun r : unitInterval => circleNormalGraphModulatedFlow T
      (circleBernoulliBackground T q p) (15/2) ψ (W r))) :
    let K := circleBernoulliBackground T q p
    let B : C(unitInterval,CircleL2 T) :=
      ⟨fun r => circleNormalGraphModulatedFlow T K (15/2) ψ (W r),hmod⟩
    ∃ U : CircleParabolicSpace T τ,
      circleParabolicCurve T τ U=u ∧
      circleParabolicH4 T τ U=ContinuousMap.toLp 2 volume ℂ W ∧
      circleParabolicTimeDerivative T τ U=ContinuousMap.toLp 2 volume ℂ B ∧
      (∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ U r=
        circleNormalGraphModulatedFlow T K (15/2) ψ (circleParabolicH4 T τ U r)) ∧
      ∀ r ∈ Ioo (0:ℝ) 1, (ω r:ℂ)=circleNormalGraphAngularVelocity T K (15/2) ψ
        (W (Set.projIcc (0:ℝ) 1 zero_le_one r)) := by
  let K := circleBernoulliBackground T q p
  let B : C(unitInterval,CircleL2 T) :=
    ⟨fun r => circleNormalGraphModulatedFlow T K (15/2) ψ (W r),hmod⟩
  let clamp : ℝ → unitInterval := Set.projIcc (0:ℝ) 1 zero_le_one
  let F : ℝ → C(AddCircle T,ℂ) := fun r => H (clamp r) 0
  let h : ℝ → CircleL2 T := fun r => circleContinuousL2 T (F r)
  have hWvalue (r : unitInterval) :
      circleSobolevCoordinate T 4 0 (W r)=circleSobolevCoordinate T 2 0 (u r) :=
    congrArg (circleSobolevCoordinate T 2 0) (hinc r)
  have hHvalue (r : unitInterval) :
      circleContinuousL2 T (H r 0)=circleSobolevCoordinate T 2 0 (u r) := by
    have hj₀ : circleSobolevContinuousJet T (W r) (0:Fin 4)=H r (0:Fin 5) := by
      simpa only [Fin.castSucc_zero] using! hjet r (0:Fin 4)
    have hL₂ : circleContinuousL2 T (circleSobolevContinuousJet T (W r) (0:Fin 4)) =
        circleSobolevCoordinate T 4 (0:Fin 5) (W r) := by
      simpa only [Fin.castSucc_zero] using! circle_sobolev_classical_jet_l2 T 3 (W r) (0:Fin 4)
    exact (congrArg (circleContinuousL2 T) hj₀).symm.trans (hL₂.trans (hWvalue r))
  have hcurve : h=fun r => circleSobolevCoordinate T 2 0 (u (clamp r)) :=
    funext fun r => hHvalue (clamp r)
  have hCderiv (r : ℝ) (hr : r ∈ Ioo (0:ℝ) 1) :
      HasDerivAt F (τ • V r) r := by
    have hconst : ContinuousOn (fun _ : ℝ => (τ:ℝ)) (Ioo (0:ℝ) 1) := continuousOn_const
    have hG : ContinuousOn (fun s : ℝ => τ • V s) (Ioo (0:ℝ) 1) := by
      simpa only [Pi.smul_apply] using! hconst.smul hVc
    exact continuous_map_hasDerivAt_of_pointwise
      F (fun s => τ • V s) 0 1 hG hpoint r hr
  have hL2deriv (r : ℝ) (hr : r ∈ Ioo (0:ℝ) 1) :
      HasDerivAt h (τ • circleContinuousL2 T (V r)) r := by
    let L : C(AddCircle T,ℂ) →L[ℝ] CircleL2 T :=
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).restrictScalars ℝ
    have hd := L.hasFDerivAt.comp_hasDerivAt r (hCderiv r hr)
    change HasDerivAt (fun s => L (F s)) (L (τ • V r)) r at hd
    rw [L.map_smul] at hd
    simpa only [L,ContinuousLinearMap.coe_restrictScalars',h,circleContinuousL2] using! hd
  have hextract (r : ℝ) (hr : r ∈ Ioo (0:ℝ) 1) :
      (ω r:ℂ)=circleNormalGraphAngularVelocity T K (15/2) ψ (W (clamp r)) ∧
      circleContinuousL2 T (V r)=circleNormalGraphModulatedFlow T K (15/2) ψ (W (clamp r)) := by
    have hPDE := bernoulli_classical_modulation_converse T e he q p hq hp
      (H (clamp r)) (hreal (clamp r)) (hspatial (clamp r)) (W (clamp r))
      (hjet (clamp r)) (hfourth (clamp r)) (hdomain (clamp r)) (hregular (clamp r))
      (V r) (hVreal r hr) (ω r) (hscalar r hr)
    have hd : circleNormalGraphRotationFunctional T ψ
        (circleNormalGraphRotationField T K
          (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (W (clamp r)))))≠0 := by
      rw [hinc]
      exact hden (clamp r)
    exact circle_normal_graph_phase_extracts_modulation T K (15/2) ψ (W (clamp r)) h
      (circleContinuousL2 T (V r)) τ hτ.ne' (ω r:ℂ) univ r (mem_univ _)
      (uniqueDiffWithinAt_univ) (hL2deriv r hr).hasDerivWithinAt
      (fun s _ => hphase (clamp s)) hd hPDE
  have hderiv (r : ℝ) (hr : 0<r) (hr1 : r<1) :
      HasDerivAt (fun s => circleSobolevCoordinate T 2 0 (u (clamp s)))
        (τ • B (clamp r)) r := by
    have hd := hL2deriv r ⟨hr,hr1⟩
    rw [hcurve,(hextract r ⟨hr,hr1⟩).2] at hd
    simpa only [B] using! hd
  have hWm : MemLp W 2 (volume : Measure unitInterval) :=
    ContinuousMap.memLp (p := 2) (volume : Measure unitInterval) ℂ W
  have hBm : MemLp B 2 (volume : Measure unitInterval) :=
    ContinuousMap.memLp (p := 2) (volume : Measure unitInterval) ℂ B
  refine Exists.elim (periodic_classical_parabolic_space T τ u W B hWm hBm
    (Eventually.of_forall fun r => (hWvalue r).symm) hderiv) ?_
  intro U hdata
  have hUc := hdata.1
  have hUW := hdata.2.1
  have hUV := hdata.2.2
  have htoW : hWm.toLp W=ContinuousMap.toLp 2 volume ℂ W := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hWm).trans
      (ContinuousMap.coeFn_toLp (p := 2) volume (𝕜 := ℂ) W).symm
  have htoB : hBm.toLp B=ContinuousMap.toLp 2 volume ℂ B := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hBm).trans
      (ContinuousMap.coeFn_toLp (p := 2) volume (𝕜 := ℂ) B).symm
  refine ⟨U,hUc,hUW.trans htoW,hUV.trans htoB,?_,fun r hr => (hextract r hr).1⟩
  rw [hUV,hUW]
  filter_upwards [MemLp.coeFn_toLp hBm,MemLp.coeFn_toLp hWm] with r hv hw
  exact hv.trans (congrArg (circleNormalGraphModulatedFlow T K (15/2) ψ) hw.symm)

end Lemniscate
