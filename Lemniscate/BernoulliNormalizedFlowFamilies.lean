import Lemniscate.NormalizedCurveFamilyRegularity
import Lemniscate.NormalGraphSobolevFamilyContinuity
import Lemniscate.BernoulliPhysicalGraphStability

/-! Regularity of the two actual normalized families compared by geometric
uniqueness. The constructed family needs continuity of its H2 height;
its spatial smoothness comes from the already constructed physical flow. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff NNReal ComplexConjugate

private theorem normalized_slice_geometry
    (y : ℝ → ℂ) (hy : ContDiff ℝ ∞ y)
    (hreg : ∀ s,deriv y s≠0) (p : ℂ) (r : ℝ) (hr : 0<r) :
    ContDiff ℝ ∞ (fun s => (y s-p)/(r:ℂ)) ∧
      ∀ s,deriv (fun u => (y u-p)/(r:ℂ)) s≠0 := by
  refine ⟨(hy.sub contDiff_const).div_const (r:ℂ),?_⟩
  intro s
  rw [deriv_div_const,deriv_sub_const]
  exact div_ne_zero (hreg s) (Complex.ofReal_ne_zero.mpr hr.ne')

/-- A given smooth regular periodic physical flow, normalized by the
actual inverse clock and scale, is continuous together with its true
spatial derivative on the closed normalized time axis. -/
theorem normalized_physical_flow_family_regularity
    (a : ℝ) (ha : 0<a) (ρ : ℝ → ℝ)
    (hρ : ∀ t : ℝ,0≤t → ρ t=(a^4+30*t)^(1/4:ℝ))
    (Y : ℝ × ℝ → ℂ)
    (hY : ContDiffOn ℝ ∞ Y ((Ici (0:ℝ)) ×ˢ (univ : Set ℝ)))
    (hYreg : ∀ t : ℝ,0≤t → ∀ s,deriv (fun u => Y (t,u)) s≠0)
    (P : ℝ) (hYper : ∀ t : ℝ,0≤t → Function.Periodic (fun s => Y (t,s)) P)
    (p : ℂ) :
    let X : ℝ≥0 × ℝ → ℂ := fun z =>
      (Y (physicalTime a (z.1:ℝ),z.2)-p)/(ρ (physicalTime a (z.1:ℝ)):ℂ)
    Continuous X ∧
      Continuous (fun z : ℝ≥0 × ℝ => deriv (fun s => X (z.1,s)) z.2) ∧
      (∀ σ,ContDiff ℝ ∞ (fun s => X (σ,s))) ∧
      (∀ σ s,deriv (fun u => X (σ,u)) s≠0) ∧
      ∀ σ,Function.Periodic (fun s => X (σ,s)) P := by
  dsimp only
  let X : ℝ≥0 × ℝ → ℂ := fun z =>
    (Y (physicalTime a (z.1:ℝ),z.2)-p)/(ρ (physicalTime a (z.1:ℝ)):ℂ)
  let Xr : ℝ × ℝ → ℂ := fun z =>
    (ρ (physicalTime a z.1):ℂ)⁻¹*(Y (physicalTime a z.1,z.2)-p)
  obtain ⟨hXr,V,hV,hderiv⟩ := normalized_curve_family_regularity a ha ρ hρ Y hY p
  let embed : ℝ≥0 × ℝ → ℝ × ℝ := fun z => ((z.1:ℝ),z.2)
  have hembed : Continuous embed :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hmaps (z : ℝ≥0 × ℝ) : embed z∈(Ici (0:ℝ)) ×ˢ (univ : Set ℝ) :=
    ⟨z.1.property,mem_univ z.2⟩
  have hX : Continuous X := by
    simpa only [X,embed,Function.comp_def,div_eq_mul_inv,mul_comm] using!
      hXr.continuousOn.comp_continuous hembed hmaps
  have hvelocity (σ : ℝ≥0) (s : ℝ) :
      deriv (fun u => X (σ,u)) s=V ((σ:ℝ),s) := by
    have hd : HasDerivAt (fun u => X (σ,u)) (V ((σ:ℝ),s)) s := by
      simpa only [X,div_eq_mul_inv,mul_comm] using!
        hderiv (σ:ℝ) σ.property s
    exact hd.deriv
  have hvelocityContinuous :
      Continuous (fun z : ℝ≥0 × ℝ => deriv (fun s => X (z.1,s)) z.2) := by
    have heq : (fun z : ℝ≥0 × ℝ => deriv (fun s => X (z.1,s)) z.2)=V ∘ embed :=
      funext fun z => hvelocity z.1 z.2
    rw [heq]
    exact hV.continuousOn.comp_continuous hembed hmaps
  have htime (σ : ℝ≥0) : 0≤physicalTime a (σ:ℝ) :=
    (physical_time_inverse a ha).2.1 (σ:ℝ) |>.2.2.1 σ.property
  have hscale (σ : ℝ≥0) : 0<ρ (physicalTime a (σ:ℝ)) := by
    rw [hρ _ (htime σ)]
    exact Real.rpow_pos_of_pos
      (add_pos_of_pos_of_nonneg (pow_pos ha 4) (mul_nonneg (by norm_num) (htime σ))) _
  have hslices (σ : ℝ≥0) : ContDiff ℝ ∞ (fun s => Y (physicalTime a (σ:ℝ),s)) := by
    apply contDiffOn_univ.mp
    exact hY.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun s _ => ⟨htime σ,mem_univ s⟩)
  have hgeometry (σ : ℝ≥0) := normalized_slice_geometry
    (fun s => Y (physicalTime a (σ:ℝ),s)) (hslices σ)
      (hYreg _ (htime σ)) p (ρ (physicalTime a (σ:ℝ))) (hscale σ)
  refine ⟨hX,hvelocityContinuous,fun σ => (hgeometry σ).1,
    fun σ s => (hgeometry σ).2 s,?_⟩
  intro σ s
  change (Y (physicalTime a (σ:ℝ),s+P)-p)/(ρ (physicalTime a (σ:ℝ)):ℂ)=_
  exact congrArg (fun y : ℂ => (y-p)/(ρ (physicalTime a (σ:ℝ)):ℂ))
    (hYper _ (htime σ) s)

variable (T : ℝ) [Fact (0<T)]

/-- The normalized graph of the constructed evolution has jointly
continuous positions and spatial velocities. Its true physical-flow
realization supplies spatial smoothness and regularity at every time. -/
theorem bernoulli_normal_graph_family_regularity
    (q p : C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (τ : ℝ) (hτ : 0<τ) (η : ℝ) (x₀ : CircleSobolevSpace T 2)
    (D : BernoulliNormalGraphEvolution T q p ψ τ hτ η x₀)
    (a : ℝ) (ha : 0<a) (α : ℝ) (ρ : ℝ → ℝ) (p₀ : ℂ)
    (hρ : ∀ σ : ℝ≥0,0<ρ (physicalTime a (σ:ℝ)))
    (β ν : ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hν : ContDiff ℝ ∞ ν)
    (hβper : Function.Periodic β (T/Real.sqrt 2))
    (hνper : Function.Periodic ν (T/Real.sqrt 2))
    (Y : ℝ → ℝ → ℂ)
    (hYs : ∀ t : ℝ,0≤t → ContDiff ℝ ∞ (Y t))
    (hYreg : ∀ t : ℝ,0≤t → ∀ s,deriv (Y t) s≠0)
    (hphysical : ∀ σ : ℝ≥0,∀ s,
      Y (physicalTime a (σ:ℝ)) s=p₀+(ρ (physicalTime a (σ:ℝ)):ℂ)*
        (Complex.exp (((α+D.theta (σ:ℝ)):ℂ)*I)*
          (β s+((circleSobolevH1Embedding T (circleSobolevInclusion T 1 (D.u σ))
            ((Real.sqrt 2*s):AddCircle T)).re:ℂ)*ν s))) :
    let Z : ℝ≥0 × ℝ → ℂ := fun z =>
      Complex.exp (((α+D.theta (z.1:ℝ)):ℂ)*I)*
        (β z.2+((circleSobolevH1Embedding T (circleSobolevInclusion T 1 (D.u z.1))
          ((Real.sqrt 2*z.2):AddCircle T)).re:ℂ)*ν z.2)
    Continuous Z ∧
      Continuous (fun z : ℝ≥0 × ℝ => deriv (fun s => Z (z.1,s)) z.2) ∧
      (∀ σ,ContDiff ℝ ∞ (fun s => Z (σ,s))) ∧
      (∀ σ s,deriv (fun u => Z (σ,u)) s≠0) ∧
      ∀ σ,Function.Periodic (fun s => Z (σ,s)) (T/Real.sqrt 2) := by
  dsimp only
  let Z : ℝ≥0 × ℝ → ℂ := fun z =>
    Complex.exp (((α+D.theta (z.1:ℝ)):ℂ)*I)*
      (β z.2+((circleSobolevH1Embedding T (circleSobolevInclusion T 1 (D.u z.1))
        ((Real.sqrt 2*z.2):AddCircle T)).re:ℂ)*ν z.2)
  let rotation : ℝ≥0 → ℂ := fun σ => Complex.exp (((α+D.theta (σ:ℝ)):ℂ)*I)
  have hrotation : Continuous rotation := by
    have hangle : Continuous (fun σ : ℝ≥0 => α+D.theta (σ:ℝ)) :=
      continuous_const.add (D.thetaContinuous.comp continuous_subtype_val)
    have hc : Continuous (fun σ : ℝ≥0 => ((α+D.theta (σ:ℝ)):ℂ)) :=
      by simpa only [Function.comp_def,Complex.ofReal_add] using!
        Complex.continuous_ofReal.comp hangle
    have hm : Continuous (fun σ : ℝ≥0 => ((α+D.theta (σ:ℝ)):ℂ)*I) :=
      hc.mul (continuous_const : Continuous (fun _ : ℝ≥0 => (I:ℂ)))
    simpa only [rotation] using! hm.cexp
  have hjet (σ : ℝ≥0) : circleSobolevClassicalJet T 1 (D.u σ) 0=
      circleSobolevH1Embedding T (circleSobolevInclusion T 1 (D.u σ)) := by
    apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 T (circleSobolevClassicalJet T 1 (D.u σ) 0)=
      circleContinuousL2 T (circleSobolevH1Embedding T (circleSobolevInclusion T 1 (D.u σ)))
    rw [circle_sobolev_classical_jet_l2,circle_sobolev_h1_embedding_l2]
    rfl
  have hreal (σ : ℝ≥0) (x : AddCircle T) :
      ((circleSobolevClassicalJet T 1 (D.u σ) 0 x).re:ℂ)=
        circleSobolevClassicalJet T 1 (D.u σ) 0 x := by
    have hstar : star (circleSobolevClassicalJet T 1 (D.u σ) 0)=
        circleSobolevClassicalJet T 1 (D.u σ) 0 :=
      (circle_sobolev_classical_jet_conjugation T 1 (D.u σ) 0).symm.trans
        (congrArg (fun f => circleSobolevClassicalJet T 1 f 0) (D.real σ))
    exact Complex.conj_eq_iff_re.mp (congrArg (fun f : C(AddCircle T,ℂ) => f x) hstar)
  have horder : (1:ℕ∞ω)≤(∞:ℕ∞ω) :=
    (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)).le
  have hC := normal_graph_sobolev_family_continuity T D.u D.u.continuous
    (fun _ => 0) rotation continuous_const hrotation β ν (hβ.of_le horder) (hν.of_le horder)
      (Real.sqrt 2)
  let Zj : ℝ≥0 × ℝ → ℂ := fun z => (0:ℂ)+rotation z.1*
    (β z.2+circleSobolevClassicalJet T 1 (D.u z.1) 0
      ((Real.sqrt 2*z.2):AddCircle T)*ν z.2)
  have hZeq : Z=Zj := by
    funext z
    dsimp only [Z,Zj,rotation]
    rw [← hjet z.1,hreal z.1,zero_add]
  have hZ : Continuous Z := by
    rw [hZeq]
    exact hC.1
  have hZv : Continuous (fun z : ℝ≥0 × ℝ => deriv (fun s => Z (z.1,s)) z.2) := by
    rw [hZeq]
    exact hC.2
  have htime (σ : ℝ≥0) : 0≤physicalTime a (σ:ℝ) :=
    (physical_time_inverse a ha).2.1 (σ:ℝ) |>.2.2.1 σ.property
  have hnormalized (σ : ℝ≥0) : (fun s => Z (σ,s))=
      (fun s => (Y (physicalTime a (σ:ℝ)) s-p₀)/(ρ (physicalTime a (σ:ℝ)):ℂ)) := by
    funext s
    have hp : Y (physicalTime a (σ:ℝ)) s=
        p₀+(ρ (physicalTime a (σ:ℝ)):ℂ)*Z (σ,s) := hphysical σ s
    rw [hp]
    field_simp [Complex.ofReal_ne_zero.mpr (hρ σ).ne']
    <;> ring
  have hgeometry (σ : ℝ≥0) : ContDiff ℝ ∞ (fun s => Z (σ,s)) ∧
      ∀ s,deriv (fun u => Z (σ,u)) s≠0 := by
    rw [hnormalized σ]
    exact normalized_slice_geometry (Y (physicalTime a (σ:ℝ)))
      (hYs _ (htime σ)) (hYreg _ (htime σ)) p₀ (ρ (physicalTime a (σ:ℝ))) (hρ σ)
  refine ⟨hZ,hZv,fun σ => (hgeometry σ).1,fun σ s => (hgeometry σ).2 s,?_⟩
  intro σ s
  have hscale : Real.sqrt 2*(s+T/Real.sqrt 2)=Real.sqrt 2*s+T := by
    have hsqrt : Real.sqrt (2:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp [hsqrt]
    <;> ring
  change rotation σ*(β (s+T/Real.sqrt 2)+
    ((circleSobolevH1Embedding T (circleSobolevInclusion T 1 (D.u σ))
      ((Real.sqrt 2*(s+T/Real.sqrt 2)):AddCircle T)).re:ℂ)*ν (s+T/Real.sqrt 2))=_
  rw [hβper s,hνper s,hscale,AddCircle.coe_add_period]

end Lemniscate
