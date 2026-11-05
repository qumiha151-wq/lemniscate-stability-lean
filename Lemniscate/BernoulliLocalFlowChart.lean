import Lemniscate.BernoulliLocalFlowChartData
import Lemniscate.PhaseFixedNormalGraphCoordinates
import Lemniscate.PhysicalChartRealization
import Lemniscate.PeriodicSmoothFamilyPathDerivative
import Lemniscate.BernoulliLocalParabolicChart

noncomputable section
namespace Lemniscate
open Complex Set Filter MeasureTheory
open scoped ContDiff Topology ComplexConjugate ENNReal

/-- A genuine physical free elastic flow in the explicit normalized
neighborhood has actual phase-fixed parabolic comparison charts of every
sufficiently short duration. Only its initial H2 norm is small. -/
theorem bernoulli_local_flow_chart
    (S : ℝ) [Fact (0<S)] (e : ℝ ≃o ℝ)
    (he : ∀ u,e u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    (q p : C(AddCircle S,ℂ))
    (hq : ∀ x : ℝ,q (x:AddCircle S)=(bernoulliProfileQ (e.symm x):ℂ))
    (hp : ∀ x : ℝ,p (x:AddCircle S)=(bernoulliProfileP (e.symm x):ℂ))
    (ψ : CircleL2 S) (hψ : circleConjugate S ψ=ψ)
    (a σ₀ α₀ : ℝ) (ha : 0<a) (hσ₀ : 0≤σ₀)
    (ρ : ℝ → ℝ) (p₀ : ℂ) (χ₀ : ℝ ≃o ℝ) (Y : ℝ → ℝ → ℂ) (h₀ : ℝ → ℝ)
    (N : BernoulliLocalFlowNeighborhood S e a σ₀ α₀ ρ p₀ χ₀ Y h₀ ψ)
    (x₀ : CircleSobolevSpace S 2)
    (hvalue : circleSobolevCoordinate S 2 0 x₀=circleContinuousL2 S
      (periodicCircleFunction S (fun x => (h₀ x:ℂ))
        (fun x => congrArg Complex.ofReal (N.initialPeriodic x))
        (Complex.continuous_ofReal.comp N.initialSmooth.continuous)))
    (hphase : inner ℂ ψ (circleSobolevCoordinate S 2 0 x₀)=0)
    (η : ℝ) (hη : 0<η) (hsmall : ‖x₀‖<η)
    (hdomain : ∀ f : CircleSobolevSpace S 4,
      ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖<η →
        f∈circleNormalGraphDomain S (circleBernoulliBackground S q p))
    (hden : ∀ g : CircleSobolevSpace S 2,‖g‖<η →
      circleNormalGraphRotationFunctional S ψ
        (circleNormalGraphRotationField S (circleBernoulliBackground S q p) g)≠0)
    (hmod : ContinuousOn
      (circleNormalGraphModulatedFlow S (circleBernoulliBackground S q p) (15/2) ψ)
      {f : CircleSobolevSpace S 4 |
        ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖<η}) :
    Nonempty (BernoulliLocalFlowChart S e q p ψ η x₀ a σ₀ α₀ ρ p₀ χ₀ Y) := by
  let b : ℝ := Real.sqrt 2
  have hb : 0<b := Real.sqrt_pos.mpr (by norm_num)
  have hb₀ : b≠0 := hb.ne'
  have hbC : (b:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb₀
  let U : Set (ℝ × ℝ) := Ioo 0 N.timeRadius ×ˢ Ioo (-N.angleRadius) N.angleRadius
  let C := insert ((0:ℝ),0) U
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hUC : U⊆C := subset_insert (0,0) U
  have hbase : ((0:ℝ),0)∈C := mem_insert _ _
  let f₀ : C(AddCircle S,ℂ) := periodicCircleFunction S (fun x => (h₀ x:ℂ))
    (fun x => congrArg Complex.ofReal (N.initialPeriodic x))
    (Complex.continuous_ofReal.comp N.initialSmooth.continuous)
  have hf₀ (x : ℝ) : f₀ (x:AddCircle S)=(h₀ x:ℂ) := rfl
  let Q₀ := (b:ℂ) • f₀
  have hQ₀ (x : ℝ) : Q₀ (x:AddCircle S)=((b*h₀ x:ℝ):ℂ) := by
    simp only [Q₀,ContinuousMap.smul_apply,smul_eq_mul,hf₀,Complex.ofReal_mul]
  have hphaseQ₀ : inner ℂ ψ (circleContinuousL2 S Q₀)=0 := by
    have hc : inner ℂ ψ (circleContinuousL2 S f₀)=0 := by rw [← hvalue]; exact hphase
    have hm : circleContinuousL2 S Q₀=(b:ℂ) • circleContinuousL2 S f₀ :=
      map_smul (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ) (b:ℂ) f₀
    rw [hm,inner_smul_right,hc,mul_zero]
  let Yn : ℝ → ℝ → ℂ := fun r x => (b:ℂ)*Complex.exp ((-α₀:ℝ)*I)*
    (Y (physicalTime a (σ₀+r)) (χ₀ (x/b))-p₀)/(ρ (physicalTime a (σ₀+r)):ℂ)
  have hΓYn (z : ℝ × ℝ) (hz : z∈C) (x : ℝ) :
      N.gamma (z,x)=Complex.exp ((-z.2:ℝ)*I)*Yn z.1 x := by
    rw [N.coupling z hz x]
    have he : Complex.exp ((-(α₀+z.2):ℝ)*I)=
        Complex.exp ((-z.2:ℝ)*I)*Complex.exp ((-α₀:ℝ)*I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    dsimp only [Yn]
    ring
  have hhaux : ContDiff ℝ ∞ (fun x => b*h₀ x) := contDiff_const.mul N.initialSmooth
  have hhpaux : Function.Periodic (fun x => b*h₀ x) S := by
    intro x
    change b*h₀ (x+S)=b*h₀ x
    rw [N.initialPeriodic x]
  obtain ⟨χ,H,F,u,G,hinit,hχc,hHc,hχs,hHs,hdata,hFc,hFeval,hu,hcoord,
      hQbase,hGbase,hGc,hGe,τ,hτ,hτT,aa,haa,haa₀,θ,hθ,hθtrace,hθzero,hpathU,hpathH4,hroot⟩ :=
    phase_fixed_normal_graph_coordinates S N.timeRadius N.angleRadius N.timePositive N.anglePositive
      N.gamma N.velocity Yn (bernoulliAuxiliaryCurve e) (bernoulliAuxiliaryTangent e)
      (bernoulliAuxiliaryCurvature e) (fun x => b*h₀ x) N.delta N.curvatureBound N.speedBound
      N.gammaSmooth N.referenceSmooth N.tangentSmooth N.curvatureSmooth hhaux N.gammaDerivative
      N.referenceDerivative N.tangentDerivative N.tangentUnit N.speed N.gammaPeriodic
      N.referencePeriodic N.tangentPeriodic N.curvaturePeriodic hhpaux N.initial N.deltaPositive
      N.curvatureNonnegative N.projectionSmall N.graphRegular N.positionClose N.tangentClose
      N.curvatureBounded hΓYn Q₀ N.initialRotation hQ₀ N.initialRotationValue ψ hψ hphaseQ₀ N.initialPair
  let z : ℝ → ℝ × ℝ := fun r => (r,θ r)
  have hzC : MapsTo z (Ico 0 τ) C := by
    intro r hr
    by_cases hzr : r=0
    · subst r
      change ((0:ℝ),θ 0)∈C
      rw [hθzero]
      exact hbase
    · exact hUC (hpathU ⟨lt_of_le_of_ne hr.1 (Ne.symm hzr),hr.2⟩)
  let scalar : ℂ := (b:ℂ)⁻¹
  let W : ℝ → CircleSobolevSpace S 4 := fun r => scalar • u (z r)
  let J : ℝ → Fin 5 → C(AddCircle S,ℂ) := fun r j => scalar • F j (z r)
  have hW : ContinuousOn W (Ico 0 τ) := by
    have hc : ContinuousOn (fun _ : ℝ => scalar) (Ico 0 τ) := continuousOn_const
    simpa only [W,z,Pi.smul_apply] using! hc.smul hpathH4
  have hJcoord (r : ℝ) (hr : r∈Ico 0 τ) (j : Fin 5) :
      circleSobolevCoordinate S 4 j (W r)=circleContinuousL2 S (J r j) := by
    simp only [W,J,map_smul,hcoord (z r) (hzC hr) j,circleContinuousL2,map_smul]
  have hF₀ (p : ℝ × ℝ) (hpc : p∈C) (x : ℝ) : F 0 p (x:AddCircle S)=(H (p,x):ℂ) := by
    simpa only [Fin.val_zero,iteratedDeriv_zero] using! hFeval p hpc 0 x
  have hF₁ (p : ℝ × ℝ) (hpc : p∈C) (x : ℝ) :
      F 1 p (x:AddCircle S)=((deriv (fun s : ℝ => H (p,s)) x:ℝ):ℂ) := by
    have hd : HasDerivAt (fun s : ℝ => (H (p,s):ℂ))
        ((deriv (fun s : ℝ => H (p,s)) x:ℝ):ℂ) x :=
      ((hdata p hpc).2.1.differentiable (by simp) x).hasDerivAt.ofReal_comp
    calc
      _ = deriv (fun s => (H (p,s):ℂ)) x := by
        simpa only [Fin.val_one,iteratedDeriv_one] using! hFeval p hpc 1 x
      _ = ((deriv (fun s : ℝ => H (p,s)) x:ℝ):ℂ) := hd.deriv
  have hJ₀ (r : ℝ) (hr : r∈Ico 0 τ) (x : ℝ) :
      J r 0 (x:AddCircle S)=((H (z r,x)/b:ℝ):ℂ) := by
    simp only [J,ContinuousMap.smul_apply,smul_eq_mul,hF₀ (z r) (hzC hr) x,scalar]
    push_cast
    ring
  have hJ₁ (r : ℝ) (hr : r∈Ico 0 τ) (x : ℝ) :
      J r 1 (x:AddCircle S)=((deriv (fun s : ℝ => H (z r,s)) x/b:ℝ):ℂ) := by
    simp only [J,ContinuousMap.smul_apply,smul_eq_mul,hF₁ (z r) (hzC hr) x,scalar]
    push_cast
    ring
  have hJbase : J 0 0=f₀ := by
    apply ContinuousMap.ext
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i x
    rw [hJ₀ 0 ⟨le_rfl,hτ⟩ x,hf₀]
    simp only [z,hθzero]
    rw [(hinit x).2]
    congr 1
    field_simp [hb₀]
  have hWinit : circleSobolevInclusion S 2 (circleSobolevInclusion S 3 (W 0))=x₀ := by
    apply circle_sobolev_value_injective S 2
    change circleSobolevCoordinate S 4 0 (W 0)=circleSobolevCoordinate S 2 0 x₀
    rw [hJcoord 0 ⟨le_rfl,hτ⟩ 0,hvalue,hJbase]
  have hJreal (r : ℝ) (hr : r∈Ico 0 τ) (x : AddCircle S) : ((J r 0 x).re:ℂ)=J r 0 x := by
    induction x using QuotientAddGroup.induction_on
    rename_i x
    rw [hJ₀ r hr x]
    simp only [Complex.ofReal_re]
  have hJphase (r : ℝ) (hr : r∈Ico 0 τ) :
      circleNormalGraphRotationFunctional S ψ (circleContinuousL2 S (J r 0))=0 := by
    change inner ℂ ψ (circleContinuousL2 S (J r 0))=0
    by_cases hzr : r=0
    · subst r
      rw [hJbase,← hvalue]
      exact hphase
    · have hrp : r∈Ioo 0 τ := ⟨lt_of_le_of_ne hr.1 (Ne.symm hzr),hr.2⟩
      have hm : circleContinuousL2 S (J r 0)=scalar • circleContinuousL2 S (F 0 (z r)) :=
        map_smul (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ) scalar (F 0 (z r))
      rw [hm,inner_smul_right,(hroot r hrp).2,mul_zero]
  have hRegular (r : ℝ) (hr : r∈Ico 0 τ) (x : ℝ) :
      0<1-3*bernoulliProfileQ (e.symm x)*(J r 0 (x:AddCircle S)).re := by
    rw [hJ₀ r hr x,Complex.ofReal_re]
    have hA := ((hdata (z r) (hzC hr)).2.2.2.2 x).2.2.1
    change 0<1-(3/b)*bernoulliProfileQ (e.symm x)*H (z r,x) at hA
    convert hA using 1 <;> ring
  let HR : (ℝ × ℝ) × ℝ → ℝ := fun p => H p/b
  have hHR : ContDiffOn ℝ ∞ HR (U ×ˢ (univ : Set ℝ)) := hHs.div_const b
  have hHRper (p : ℝ × ℝ) (hpU : p∈U) : Function.Periodic (fun x => HR (p,x)) S := by
    intro x
    change H (p,x+S)/b=H (p,x)/b
    exact congrArg (fun y : ℝ => y/b) ((hdata p (hUC hpU)).2.2.2.1 x)
  have hzSmooth : ContDiffOn ℝ 1 z (Ioo 0 τ) := contDiffOn_id.prodMk hθ
  obtain ⟨V,hVc,hVtime,hVvalue⟩ := periodic_smooth_family_path_derivative S U hU HR hHR hHRper
    0 τ z hzSmooth hpathU (fun r => J r 0)
    (fun r hr x => hJ₀ r ⟨hr.1.le,hr.2⟩ x)
  have hVreal (r : ℝ) (hr : r∈Ioo 0 τ) (x : AddCircle S) : ((V r x).re:ℂ)=V r x := by
    induction x using QuotientAddGroup.induction_on
    rename_i x
    rw [hVvalue r hr x]
    simp only [Complex.ofReal_re]
  let φ : ℝ → ℝ := fun s => e.symm (b*s)
  let βp : ℝ → ℂ := bernoulliCurve ∘ φ
  let tp : ℝ → ℂ := fun s => bernoulliAuxiliaryTangent e (b*s)
  let np : ℝ → ℂ := fun s => I*tp s
  let kp : ℝ → ℝ := fun s => 3*bernoulliProfileQ (φ s)
  let h : ℝ → ℝ → ℝ := fun σ s => H ((σ-σ₀,θ (σ-σ₀)),b*s)/b
  have hβp (s : ℝ) : HasDerivAt βp (tp s) s := (bernoulli_arclength_frame e he s).1
  have hnp (s : ℝ) : HasDerivAt np (-(kp s:ℂ)*tp s) s :=
    (bernoulli_arclength_frame e he s).2.2.2.1
  have hup (s : ℝ) : ‖tp s‖=1 := (bernoulli_arclength_frame e he s).2.1
  have hScaledGraph (p : ℝ × ℝ) (hpc : p∈C) (s : ℝ) :
      N.gamma (p,χ (p,b*s))=(b:ℂ)*βp s+I*(H (p,b*s):ℂ)*tp s := by
    simpa only [bernoulliAuxiliaryCurve,βp,φ,tp,b,Function.comp_def] using
      ((hdata p hpc).2.2.2.2 (b*s)).1
  have hCoreRegular (r : ℝ) (hr : r∈Ioo 0 τ) (s : ℝ) :
      0<1-kp s*(H (z r,b*s)/b) := by
    have hh := ((hdata (z r) (hUC (hpathU hr))).2.2.2.2 (b*s)).2.2.1
    change 0<1-(3/b)*bernoulliProfileQ (φ s)*H (z r,b*s) at hh
    convert hh using 1 <;> dsimp only [kp]; ring
  have hCore := physical_chart_scalar_equation b a σ₀ α₀ τ (15/2) hb ha hσ₀ ρ p₀ χ₀
    N.originalParameterSmooth N.originalParameterInverseSmooth Y N.gamma χ H θ U hU hθ hpathU
    hχs hHs (fun r hr x => ((hdata (z r) (hUC (hpathU hr))).2.2.2.2 x).2.2.2.1)
    βp tp np kp hβp hnp hup (fun _ => rfl) hCoreRegular
    (fun t ht => (N.scale t ht).1)
    (fun t ht => ((N.scale t ht.le).2.2 ht).1)
    (fun t ht => ((N.scale t ht.le).2.2 ht).2)
    N.flowSpace N.flowRegular N.flowDifferentiable N.flowEquation
    (fun p hpU => N.coupling p (hUC hpU))
    (fun p hpU => hScaledGraph p (hUC hpU))
  dsimp only at hCore
  have hVelocity (r : ℝ) (hr : r∈Ioo 0 τ) (s : ℝ) :
      deriv (fun σ => h σ s) (σ₀+r)=(V r ((b*s):AddCircle S)).re := by
    let E : C(AddCircle S,ℂ) →L[ℝ] ℝ := Complex.reCLM.comp
      ((ContinuousMap.evalCLM ℂ ((b*s):AddCircle S)).restrictScalars ℝ)
    have hd : HasDerivAt (fun u => (J u 0 ((b*s):AddCircle S)).re)
        (V r ((b*s):AddCircle S)).re r := by
      simpa only [E,Function.comp_def,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars',ContinuousMap.evalCLM_apply,Complex.reCLM_apply] using!
        E.hasFDerivAt.comp_hasDerivAt r (hVtime r hr)
    have hshift : HasDerivAt (fun σ : ℝ => σ-σ₀) 1 (σ₀+r) :=
      (hasDerivAt_id (σ₀+r)).sub_const σ₀
    have hd' : HasDerivAt (fun u => (J u 0 ((b*s):AddCircle S)).re)
        (V r ((b*s):AddCircle S)).re (σ₀+r-σ₀) := by
      simpa only [add_sub_cancel_left] using hd
    have hcomposed : HasDerivAt (fun σ => (J (σ-σ₀) 0 ((b*s):AddCircle S)).re)
        (V r ((b*s):AddCircle S)).re (σ₀+r) := by
      simpa only [Function.comp_def,mul_one] using! hd'.comp (σ₀+r) hshift
    have hmap : Tendsto (fun σ : ℝ => σ-σ₀) (𝓝 (σ₀+r)) (𝓝 r) := by
      have hh : Tendsto (fun σ : ℝ => σ-σ₀) (𝓝 (σ₀+r)) (𝓝 (σ₀+r-σ₀)) :=
        hshift.continuousAt
      simpa only [add_sub_cancel_left] using hh
    have hevent : (fun σ => h σ s) =ᶠ[𝓝 (σ₀+r)]
        (fun σ => (J (σ-σ₀) 0 ((b*s):AddCircle S)).re) := by
      filter_upwards [hmap.eventually (isOpen_Ioo.mem_nhds hr)] with σ hσ
      rw [hJ₀ (σ-σ₀) ⟨hσ.1.le,hσ.2⟩ (b*s)]
      simp only [h,z,Complex.ofReal_re]
    exact (hcomposed.congr_of_eventuallyEq hevent).deriv
  have hSpatial (r : ℝ) (hr : r∈Ioo 0 τ) (s : ℝ) :
      deriv (h (σ₀+r)) s=b*(J r 1 ((b*s):AddCircle S)).re := by
    have hpC := hUC (hpathU hr)
    have hd : HasDerivAt (fun x : ℝ => H (z r,x))
        (deriv (fun x : ℝ => H (z r,x)) (b*s)) (b*s) :=
      ((hdata (z r) hpC).2.1.differentiable (by simp) (b*s)).hasDerivAt
    have hscale : HasDerivAt (fun x : ℝ => b*x) b s := by
      simpa only [id_eq,mul_one] using! (hasDerivAt_id s).const_mul b
    have hd' : HasDerivAt (fun x : ℝ => H (z r,b*x)/b)
        (deriv (fun x : ℝ => H (z r,x)) (b*s)) s := by
      apply ((hd.comp s hscale).div_const b).congr_deriv
      field_simp [hb₀]
    have hh : HasDerivAt (h (σ₀+r))
        (deriv (fun x : ℝ => H (z r,x)) (b*s)) s := by
      simpa only [h,z,add_sub_cancel_left] using! hd'
    rw [hh.deriv,hJ₁ r ⟨hr.1.le,hr.2⟩ (b*s),Complex.ofReal_re]
    field_simp [hb₀]
  have hHeight (r : ℝ) (hr : r∈Ico 0 τ) :
      h (σ₀+r)=(fun s : ℝ => (J r 0 ((b*s):AddCircle S)).re) := by
    funext s
    rw [hJ₀ r hr (b*s)]
    simp only [h,z,add_sub_cancel_left,Complex.ofReal_re]
  have hScalarInput : ∀ r∈Ioo 0 τ,
      let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
      let β := bernoulliCurve ∘ φ
      let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
      let n := fun s : ℝ => I*t s
      let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
      let hf := fun s : ℝ => (J r 0 ((Real.sqrt 2*s):AddCircle S)).re
      let h₁ := fun s : ℝ => Real.sqrt 2*(J r 1 ((Real.sqrt 2*s):AddCircle S)).re
      ∀ x : ℝ,(V r (x:AddCircle S)).re+deriv θ r*
        ((conj (t (x/Real.sqrt 2))*β (x/Real.sqrt 2)).re+
          ((conj (t (x/Real.sqrt 2))*β (x/Real.sqrt 2)).im+hf (x/Real.sqrt 2))*
            h₁ (x/Real.sqrt 2)/(1-k (x/Real.sqrt 2)*hf (x/Real.sqrt 2)))=
        normalGraphFlowRHS β n k hf (15/2) (x/Real.sqrt 2) := by
    intro r hr
    dsimp only
    have hPhysical (s : ℝ) : (V r ((b*s):AddCircle S)).re+deriv θ r*
        ((conj (tp s)*βp s).re+
          ((conj (tp s)*βp s).im+(J r 0 ((b*s):AddCircle S)).re)*
            (b*(J r 1 ((b*s):AddCircle S)).re)/
              (1-kp s*(J r 0 ((b*s):AddCircle S)).re))=
        normalGraphFlowRHS βp np kp (fun x => (J r 0 ((b*x):AddCircle S)).re) (15/2) s := by
      have hv := hVelocity r hr s
      have hs := hSpatial r hr s
      have hh := congrArg (fun f : ℝ → ℝ => f s) (hHeight r ⟨hr.1.le,hr.2⟩)
      have hforce := congrArg (fun f : ℝ → ℝ => normalGraphFlowRHS βp np kp f (15/2) s)
        (hHeight r ⟨hr.1.le,hr.2⟩)
      calc
        _ = deriv (fun σ => h σ s) (σ₀+r)+deriv θ r*
            ((conj (tp s)*βp s).re+((conj (tp s)*βp s).im+h (σ₀+r) s)*
              deriv (h (σ₀+r)) s/(1-kp s*h (σ₀+r) s)) := by rw [hv,hs,hh]
        _ = normalGraphFlowRHS βp np kp (h (σ₀+r)) (15/2) s := hCore r hr s
        _ = _ := hforce
    intro x
    have hscale : b*(x/b)=x := by field_simp [hb₀]
    simpa only [βp,np,tp,kp,φ,bernoulliAuxiliaryTangent,b,Function.comp_def,hscale]
      using! hPhysical (x/b)
  obtain ⟨d₀,hd₀,hd₀τ,hComparison⟩ := bernoulli_local_parabolic_chart S e he q p hq hp ψ τ η hτ hη
    W hW J hJcoord hJreal x₀ hWinit hsmall hdomain hden hmod hRegular V hVc hVreal
    (deriv θ) hVtime hJphase hScalarInput
  have hPhysicalGraph (r : ℝ) (hr : r∈Ico 0 τ) (s : ℝ) :
      Y (physicalTime a (σ₀+r)) (χ₀ (χ (z r,b*s)/b))=
        p₀+(ρ (physicalTime a (σ₀+r)):ℂ)*
          (Complex.exp (((α₀+θ r):ℂ)*I)*
            (βp s+((J r 0 ((b*s):AddCircle S)).re:ℂ)*(I*tp s))) := by
    have htime : 0≤physicalTime a (σ₀+r) :=
      ((physical_time_inverse a ha).2.1 (σ₀+r)).2.2.1 (add_nonneg hσ₀ hr.1)
    have hh := projected_physical_graph_identity b a σ₀ α₀ r ha hb₀ ρ p₀ χ₀ Y N.gamma χ H θ
      βp tp C (hzC hr) (N.scale _ htime).1.ne' N.coupling hScaledGraph
    rw [hJ₀ r hr (b*s),Complex.ofReal_re]
    exact hh s
  refine ⟨{
    timeRadius := τ
    timePositive := hτ
    chiAux := χ
    heightAux := H
    angle := θ
    angleZero := hθzero
    angleTrace := hθtrace
    angleSmooth := hθ
    chiInitial := fun x => (hinit x).1
    chiSmooth := fun r hr => (hdata (z r) (hzC hr)).1
    chiPositive := fun r hr x => ((hdata (z r) (hzC hr)).2.2.2.2 x).2.2.2.1
    chiDeck := fun r hr => (hdata (z r) (hzC hr)).2.2.1
    chiBound := ⟨3*N.delta,fun r hr x => (((hdata (z r) (hzC hr)).2.2.2.2 x).2.1).le⟩
    high := W
    jet := J
    highContinuous := hW
    coordinates := hJcoord
    initial := hWinit
    heightValue := hJ₀
    phase := hJphase
    physicalGraph := hPhysicalGraph
    comparisonRadius := d₀
    comparisonPositive := hd₀
    comparisonShort := hd₀τ
    comparison := hComparison
  }⟩

end Lemniscate
