import Lemniscate.BernoulliClassicalParabolicSolution
import Lemniscate.PeriodicSobolevConjugation
import Mathlib.Tactic.Linarith

noncomputable section
namespace Lemniscate

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

private theorem local_chart_positive_radius_transport
    {P : ℝ → Prop} {Q : Prop} (h : ∃ r > 0,P r)
    (H : ∀ r,0 < r → P r → Q) : Q := by
  rcases h with ⟨r,hr,hP⟩
  exact H r hr hP

set_option maxHeartbeats 800000 in
/-- A continuous classical H4 height with the actual scalar geometric
equation gives a parabolic solution on a short interval. Only its initial
H2 norm is small; the H4 norm and the parabolic norm need not be small. -/
theorem bernoulli_local_parabolic_chart
    (e : ℝ ≃o ℝ) (he : ∀ u, e u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    (q p : C(AddCircle T,ℂ))
    (hq : ∀ x : ℝ,q (x:AddCircle T)=(bernoulliProfileQ (e.symm x):ℂ))
    (hp : ∀ x : ℝ,p (x:AddCircle T)=(bernoulliProfileP (e.symm x):ℂ))
    (ψ : CircleL2 T) (b η : ℝ) (hb : 0 < b) (hη : 0 < η)
    (W : ℝ → CircleSobolevSpace T 4) (hW : ContinuousOn W (Ico 0 b))
    (F : ℝ → Fin 5 → C(AddCircle T,ℂ))
    (hcoord : ∀ r ∈ Ico 0 b,∀ j : Fin 5,
      circleSobolevCoordinate T 4 j (W r)=circleContinuousL2 T (F r j))
    (hreal₀ : ∀ r ∈ Ico 0 b,∀ x,((F r 0 x).re:ℂ)=F r 0 x)
    (x₀ : CircleSobolevSpace T 2)
    (hinit : circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (W 0))=x₀)
    (hsmall : ‖x₀‖ < η)
    (hdomain : ∀ f : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < η →
        f ∈ circleNormalGraphDomain T (circleBernoulliBackground T q p))
    (hden : ∀ g : CircleSobolevSpace T 2,‖g‖ < η →
      circleNormalGraphRotationFunctional T ψ
        (circleNormalGraphRotationField T (circleBernoulliBackground T q p) g)≠0)
    (hmod : ContinuousOn
      (circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ)
      {f : CircleSobolevSpace T 4 |
        ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < η})
    (hregular : ∀ r ∈ Ico 0 b,∀ x : ℝ,
      0 < 1-3*bernoulliProfileQ (e.symm x)*(F r 0 (x:AddCircle T)).re)
    (V : ℝ → C(AddCircle T,ℂ)) (hV : ContinuousOn V (Ioo 0 b))
    (hVreal : ∀ r ∈ Ioo 0 b,∀ x,((V r x).re:ℂ)=V r x)
    (omega : ℝ → ℝ)
    (htime : ∀ r ∈ Ioo 0 b,HasDerivAt (fun s => F s 0) (V r) r)
    (hphase : ∀ r ∈ Ico 0 b,
      circleNormalGraphRotationFunctional T ψ (circleContinuousL2 T (F r 0))=0)
    (hscalar : ∀ r ∈ Ioo 0 b,
      let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
      let β := bernoulliCurve ∘ φ
      let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
      let n := fun s : ℝ => I*t s
      let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
      let h := fun s : ℝ => (F r 0 ((Real.sqrt 2*s):AddCircle T)).re
      let h₁ := fun s : ℝ => Real.sqrt 2*(F r 1 ((Real.sqrt 2*s):AddCircle T)).re
      ∀ x : ℝ,(V r (x:AddCircle T)).re+
        omega r*((conj (t (x/Real.sqrt 2))*β (x/Real.sqrt 2)).re+
          ((conj (t (x/Real.sqrt 2))*β (x/Real.sqrt 2)).im+h (x/Real.sqrt 2))*
            h₁ (x/Real.sqrt 2)/(1-k (x/Real.sqrt 2)*h (x/Real.sqrt 2)))=
        normalGraphFlowRHS β n k h (15/2) (x/Real.sqrt 2)) :
    ∃ d₀ > 0,d₀ < b ∧ ∀ d > 0,d ≤ d₀ → ∃ U : CircleParabolicSpace T d,
      (∀ r : unitInterval,circleParabolicCurve T d U r=
        circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (W (d*(r:ℝ))))) ∧
      circleParabolicInitialValue T d U=x₀ ∧
      ‖circleParabolicCurve T d U‖ < η ∧
      (∀ᵐ r : unitInterval ∂volume,circleParabolicH4 T d U r=W (d*(r:ℝ))) ∧
      (∀ᵐ r ∂volume,circleParabolicTimeDerivative T d U r=
        circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
          (circleParabolicH4 T d U r)) ∧
      ∀ r ∈ Ioo (0:ℝ) 1,(omega (d*r):ℂ)=
        circleNormalGraphAngularVelocity T (circleBernoulliBackground T q p) (15/2) ψ
          (W (d*r)) := by
  let low : CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
    (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)
  let u : ℝ → CircleSobolevSpace T 2 := fun r => low (W r)
  have hu : ContinuousOn u (Ico 0 b) := low.continuous.comp_continuousOn hW
  have hu₀ : u 0=x₀ := hinit
  let m := (‖x₀‖+η)/2
  have hm₀ : 0≤m := by dsimp only [m]; positivity
  have hxm : ‖u 0‖<m := by rw [hu₀]; dsimp only [m]; linarith
  have hmη : m<η := by dsimp only [m]; linarith
  have hnear : {r : ℝ | ‖u r‖<m} ∈ 𝓝[Ico 0 b] (0:ℝ) :=
    (hu.norm 0 ⟨le_rfl,hb⟩) (Iio_mem_nhds hxm)
  refine local_chart_positive_radius_transport (Metric.mem_nhdsWithin_iff.mp hnear) ?_
  intro ε hε hεnear
  let d₀ := min (b/2) (ε/2)
  have hd₀ : 0<d₀ := lt_min (half_pos hb) (half_pos hε)
  have hd₀b : d₀<b := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd₀ε : d₀<ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨d₀,hd₀,hd₀b,?_⟩
  intro d hd hdd₀
  have hdb : d<b := hdd₀.trans_lt hd₀b
  have hdε : d<ε := hdd₀.trans_lt hd₀ε
  have hscale (r : unitInterval) : d*(r:ℝ)∈Ico (0:ℝ) b :=
    ⟨mul_nonneg hd.le r.property.1,
      (mul_le_of_le_one_right hd.le r.property.2).trans_lt hdb⟩
  have hscaledSmall (r : unitInterval) : ‖u (d*(r:ℝ))‖<m := by
    apply hεnear
    refine ⟨?_,hscale r⟩
    change dist (d*(r:ℝ)) (0:ℝ)<ε
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (hscale r).1]
    exact (mul_le_of_le_one_right hd.le r.property.2).trans_lt hdε
  have hpositive (r : ℝ) (hr : r∈Ioo (0:ℝ) 1) : d*r∈Ioo (0:ℝ) b := by
    have hlt : d*r<d := by simpa only [mul_one] using mul_lt_mul_of_pos_left hr.2 hd
    exact ⟨mul_pos hd hr.1,hlt.trans hdb⟩
  let Wd : C(unitInterval,CircleSobolevSpace T 4) :=
    ⟨fun r => W (d*(r:ℝ)),hW.comp_continuous
      (continuous_const.mul continuous_subtype_val) hscale⟩
  let ud : C(unitInterval,CircleSobolevSpace T 2) :=
    ⟨fun r => low (Wd r),low.continuous.comp Wd.continuous⟩
  let H := fun r : unitInterval => F (d*(r:ℝ))
  have hreal (r : ℝ) (hr : r∈Ico (0:ℝ) b) :
      ∀ j x,((F r j x).re:ℂ)=F r j x := by
    have hwreal : circleSobolevConjugation T 4 (W r)=W r := by
      apply circle_sobolev_value_injective T 4
      calc
        circleSobolevCoordinate T 4 0 (circleSobolevConjugation T 4 (W r))=
            circleConjugate T (circleSobolevCoordinate T 4 0 (W r)) := rfl
        _=circleConjugate T (circleContinuousL2 T (F r 0)) :=
          congrArg (circleConjugate T) (hcoord r hr 0)
        _=circleContinuousL2 T (F r 0) := circle_conjugate_continuous_real T (F r 0)
          (fun x => Complex.conj_eq_iff_re.mpr (hreal₀ r hr x))
        _=circleSobolevCoordinate T 4 0 (W r) := (hcoord r hr 0).symm
    intro j x
    have hstar : star (F r j)=F r j := by
      apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
      change circleContinuousL2 T (star (F r j))=circleContinuousL2 T (F r j)
      calc
        circleContinuousL2 T (star (F r j))=
            circleConjugate T (circleContinuousL2 T (F r j)) := circle_continuous_l2_star T _
        _=circleConjugate T (circleSobolevCoordinate T 4 j (W r)) :=
          congrArg (circleConjugate T) (hcoord r hr j).symm
        _=circleSobolevCoordinate T 4 j (circleSobolevConjugation T 4 (W r)) := rfl
        _=circleSobolevCoordinate T 4 j (W r) :=
          congrArg (circleSobolevCoordinate T 4 j) hwreal
        _=circleContinuousL2 T (F r j) := hcoord r hr j
    exact Complex.conj_eq_iff_re.mp (congrArg (fun f : C(AddCircle T,ℂ) => f x) hstar)
  have hspatial (r : unitInterval) (j : Fin 4) :
      HasCircleDeriv T (H r j.castSucc) (H r j.succ) := by
    apply circle_classical_deriv_of_continuous_weak T
    change HasWeakCircleDeriv T (circleContinuousL2 T (F (d*(r:ℝ)) j.castSucc))
      (circleContinuousL2 T (F (d*(r:ℝ)) j.succ))
    rw [← hcoord _ (hscale r) j.castSucc,← hcoord _ (hscale r) j.succ]
    exact circle_sobolev_weak_deriv T 4 (Wd r) j
  have hjet (r : unitInterval) (j : Fin 4) :
      circleSobolevContinuousJet T (Wd r) j=H r j.castSucc := by
    apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
    exact (circle_sobolev_classical_jet_l2 T 3 (Wd r) j).trans (hcoord _ (hscale r) j.castSucc)
  let Vd := fun r : ℝ => V (d*r)
  let od := fun r : ℝ => omega (d*r)
  have hVd : ContinuousOn Vd (Ioo (0:ℝ) 1) := hV.comp
    (continuous_const.mul continuous_id).continuousOn hpositive
  have hpoint (r : ℝ) (hr : r∈Ioo (0:ℝ) 1) (x : AddCircle T) :
      HasDerivAt (fun s => H (Set.projIcc (0:ℝ) 1 zero_le_one s) 0 x)
        (d • Vd r x) r := by
    have hh := (ContinuousMap.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt (d*r)
      (htime (d*r) (hpositive r hr))
    have hc : HasDerivAt (fun s => F (d*s) 0 x) (d • Vd r x) r := by
      simpa only [Function.comp_def,mul_one,Vd] using!
        hh.scomp r ((hasDerivAt_id r).const_mul d)
    apply hc.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
    simp only [H,Set.projIcc_of_mem zero_le_one ⟨hs.1.le,hs.2.le⟩]
  have hclosedMod : Continuous (fun r : unitInterval =>
      circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ (Wd r)) :=
    hmod.comp_continuous Wd.continuous (fun r => (hscaledSmall r).trans hmη)
  have hraw (r : ℝ) (hr : r∈Ioo (0:ℝ) 1) := hscalar (d*r) (hpositive r hr)
  have hraw' : ∀ r ∈ Ioo (0:ℝ) 1,
      let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
      let β := bernoulliCurve ∘ φ
      let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
      let n := fun s : ℝ => I*t s
      let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
      let h := fun s : ℝ => (H (Set.projIcc (0:ℝ) 1 zero_le_one r) 0
        ((Real.sqrt 2*s):AddCircle T)).re
      let h₁ := fun s : ℝ => Real.sqrt 2*(H (Set.projIcc (0:ℝ) 1 zero_le_one r) 1
        ((Real.sqrt 2*s):AddCircle T)).re
      ∀ x : ℝ,(Vd r (x:AddCircle T)).re+
        od r*((conj (t (x/Real.sqrt 2))*β (x/Real.sqrt 2)).re+
          ((conj (t (x/Real.sqrt 2))*β (x/Real.sqrt 2)).im+h (x/Real.sqrt 2))*
            h₁ (x/Real.sqrt 2)/(1-k (x/Real.sqrt 2)*h (x/Real.sqrt 2)))=
        normalGraphFlowRHS β n k h (15/2) (x/Real.sqrt 2) := by
    intro r hr
    simpa only [H,Vd,od,Set.projIcc_of_mem zero_le_one ⟨hr.1.le,hr.2.le⟩] using! hraw r hr
  refine Exists.elim (bernoulli_classical_parabolic_solution T e he q p hq hp ψ d hd ud Wd
    (fun _ => rfl) H (fun r => hreal _ (hscale r)) hspatial hjet
    (fun r => hcoord _ (hscale r) 4)
    (fun r => hdomain _ ((hscaledSmall r).trans hmη))
    (fun r => hregular _ (hscale r)) Vd hVd
    (fun r hr => hVreal _ (hpositive r hr)) od hpoint
    (fun r => hphase _ (hscale r))
    (fun r => hden _ ((hscaledSmall r).trans hmη)) hraw' hclosedMod) ?_
  intro U hU
  refine ⟨U,?_,?_,?_,?_,hU.2.2.2.1,?_⟩
  · intro r
    exact congrArg (fun f : C(unitInterval,CircleSobolevSpace T 2) => f r) hU.1
  · change circleParabolicCurve T d U 0=x₀
    rw [hU.1]
    change circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (W (d*(0:ℝ))))=x₀
    rw [mul_zero]
    exact hinit
  · rw [hU.1]
    exact ((ContinuousMap.norm_le _ hm₀).mpr (fun r => (hscaledSmall r).le)).trans_lt hmη
  · rw [hU.2.1]
    exact ContinuousMap.coeFn_toLp (p:=2) volume (𝕜:=ℂ) Wd
  · intro r hr
    simpa only [od,Wd,Set.projIcc_of_mem zero_le_one ⟨hr.1.le,hr.2.le⟩] using! hU.2.2.2.2 r hr

end Lemniscate
