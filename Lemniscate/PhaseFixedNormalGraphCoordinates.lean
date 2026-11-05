import Lemniscate.ParametricNormalGraphClosedCoordinates
import Lemniscate.NormalProjectionSobolevTrace
import Lemniscate.NormalGraphPhaseFixedFamily
import Lemniscate.PeriodicCoefficientAlgebra
import Lemniscate.BernoulliCircleProfile
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Order.LeftRight

/-! Actual closed normal coordinates and their fourth-order Sobolev trace
admit a small phase-fixed path. All circle representatives and the
continuous rotation field are constructed from the selected coordinates. -/
noncomputable section
namespace Lemniscate
open Complex Set Filter
open scoped ContDiff Topology ComplexConjugate

/-- Uniform geometric proximity constructs actual normal coordinates,
their continuous H4 trace and a C1 phase-fixed angle with zero initial
value. The initial height and rotation representatives are prescribed
only by their actual initial spatial values. -/
theorem phase_fixed_normal_graph_coordinates
    (L : ℝ) [Fact (0<L)]
    (T₀ a₀ : ℝ) (hT₀ : 0<T₀) (ha₀ : 0<a₀)
    (Γ V : (ℝ × ℝ) × ℝ → ℂ) (Y : ℝ → ℝ → ℂ)
    (β T : ℝ → ℂ) (κ h₀ : ℝ → ℝ) (δ K v : ℝ)
    (hΓsmooth : ContDiffOn ℝ ∞ Γ
      ((insert ((0:ℝ),0) (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀)) ×ˢ (univ : Set ℝ)))
    (hβsmooth : ContDiff ℝ ∞ β) (hTsmooth : ContDiff ℝ ∞ T)
    (hκsmooth : ContDiff ℝ ∞ κ) (hh₀smooth : ContDiff ℝ ∞ h₀)
    (hΓ : ∀ p ∈ insert ((0:ℝ),0) (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀), ∀ s : ℝ,
      HasDerivAt (fun x => Γ (p,x)) (V (p,s)) s)
    (hβ : ∀ s, HasDerivAt β (T s) s)
    (hTd : ∀ s, HasDerivAt T (I*(κ s:ℂ)*T s) s)
    (hunit : ∀ s, ‖T s‖=1)
    (hspeed : ∀ p ∈ insert ((0:ℝ),0) (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀), ∀ s : ℝ,
      ‖V (p,s)‖≤v)
    (hΓper : ∀ p ∈ insert ((0:ℝ),0) (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀),
      Function.Periodic (fun s => Γ (p,s)) L)
    (hβper : Function.Periodic β L) (hTper : Function.Periodic T L)
    (hκper : Function.Periodic κ L) (hh₀per : Function.Periodic h₀ L)
    (hinitial : ∀ s, Γ ((0,0),s)=β s+I*(h₀ s:ℂ)*T s)
    (hδ : 0<δ) (hK : 0≤K) (hsmall : δ+2*K*δ<1/2)
    (hregular : K*(δ+2*v*δ)<1)
    (hposition : ∀ p ∈ insert ((0:ℝ),0) (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀), ∀ s : ℝ,
      ‖Γ (p,s)-β s‖≤δ)
    (htangent : ∀ p ∈ insert ((0:ℝ),0) (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀), ∀ s : ℝ,
      ‖V (p,s)-T s‖≤δ)
    (hcurvature : ∀ s, |κ s|≤K)
    (hΓY : ∀ p ∈ insert ((0:ℝ),0) (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀), ∀ s : ℝ,
      Γ (p,s)=Complex.exp ((-p.2:ℝ)*I)*Y p.1 s)
    (Q₀ G₀ : C(AddCircle L,ℂ))
    (hQ₀ : ∀ s : ℝ, Q₀ (s:AddCircle L)=(h₀ s:ℂ))
    (hG₀ : ∀ s : ℝ, G₀ (s:AddCircle L)=
      (((conj (T s)*β s).re+((conj (T s)*β s).im+h₀ s)*deriv h₀ s/
        (1-κ s*h₀ s):ℝ):ℂ))
    (ψ : CircleL2 L) (hψ : circleConjugate L ψ=ψ)
    (hphase₀ : inner ℂ ψ (circleContinuousL2 L Q₀)=0)
    (hpair₀ : (inner ℂ ψ (circleContinuousL2 L G₀)).re≠0) :
    let U : Set (ℝ × ℝ) := Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀
    let S := insert ((0:ℝ),0) U
    ∃ χ H : (ℝ × ℝ) × ℝ → ℝ,
      ∃ F : Fin 5 → (ℝ × ℝ) → C(AddCircle L,ℂ),
      ∃ u : (ℝ × ℝ) → CircleSobolevSpace L 4,
      ∃ G : (ℝ × ℝ) → C(AddCircle L,ℂ),
      (∀ s, χ ((0,0),s)=s ∧ H ((0,0),s)=h₀ s) ∧
      ContinuousOn χ (S ×ˢ (univ : Set ℝ)) ∧
      ContinuousOn H (S ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ χ (U ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ H (U ×ˢ (univ : Set ℝ)) ∧
      (∀ p ∈ S,
        ContDiff ℝ ∞ (fun s => χ (p,s)) ∧ ContDiff ℝ ∞ (fun s => H (p,s)) ∧
        (∀ s, χ (p,s+L)=χ (p,s)+L) ∧ Function.Periodic (fun s => H (p,s)) L ∧
        ∀ s : ℝ,
          Γ (p,χ (p,s))=β s+I*(H (p,s):ℂ)*T s ∧ |χ (p,s)-s|<3*δ ∧
          0<1-κ s*H (p,s) ∧ 0<deriv (fun x => χ (p,x)) s ∧
          HasDerivAt (fun x => (x,(χ (p,x)-x,H (p,x))))
            (normalProjectionVectorField T κ V (p,(s,(χ (p,s)-s,H (p,s))))) s) ∧
      (∀ j, ContinuousOn (F j) S) ∧
      (∀ p ∈ S, ∀ (j : Fin 5) (s : ℝ),
        F j p (s:AddCircle L)=iteratedDeriv j.val (fun x => (H (p,x):ℂ)) s) ∧
      ContinuousOn u S ∧
      (∀ p ∈ S, ∀ j : Fin 5,
        circleSobolevCoordinate L 4 j (u p)=circleContinuousL2 L (F j p)) ∧
      F 0 (0,0)=Q₀ ∧ G (0,0)=G₀ ∧ ContinuousOn G S ∧
      (∀ p ∈ S, ∀ s : ℝ, G p (s:AddCircle L)=
        (((conj (T s)*β s).re+((conj (T s)*β s).im+H (p,s))*
          deriv (fun x => H (p,x)) s/(1-κ s*H (p,s)):ℝ):ℂ)) ∧
      ∃ τ>0, τ≤T₀ ∧ ∃ a>0, a≤a₀ ∧ ∃ θ : ℝ → ℝ,
        ContDiffOn ℝ 1 θ (Ioo 0 τ) ∧
        Tendsto θ (𝓝[>] (0:ℝ)) (𝓝 0) ∧ θ 0=0 ∧
        MapsTo (fun r => (r,θ r)) (Ioo 0 τ) U ∧
        ContinuousOn (fun r => u (r,θ r)) (Ico 0 τ) ∧
        ∀ r ∈ Ioo 0 τ, |θ r|<a/2 ∧
          inner ℂ ψ (circleContinuousL2 L (F 0 (r,θ r)))=0 := by
  let U : Set (ℝ × ℝ) := Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀
  let S := insert ((0:ℝ),0) U
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hUS : U ⊆ S := subset_insert (0,0) U
  have hbase : ((0:ℝ),0) ∈ S := mem_insert _ _
  have hnotU : ((0:ℝ),0) ∉ U := by simp [U]
  have hconv : Convex ℝ U := (convex_Ioo (0:ℝ) T₀).prod (convex_Ioo (-a₀) a₀)
  have hinterior : (interior U).Nonempty := by
    rw [hU.interior_eq]
    refine ⟨(T₀/2,0),⟨⟨by linarith only [hT₀],by linarith only [hT₀]⟩,
      ⟨by linarith only [ha₀],ha₀⟩⟩⟩
  have hbaseclosure : ((0:ℝ),0) ∈ closure U := by
    rw [show U=Ioo (0:ℝ) T₀ ×ˢ Ioo (-a₀) a₀ from rfl,closure_prod_eq,
      closure_Ioo hT₀.ne,closure_Ioo (by linarith only [ha₀] : -a₀≠a₀)]
    exact ⟨⟨le_rfl,hT₀.le⟩,⟨by linarith only [ha₀],ha₀.le⟩⟩
  have hS : UniqueDiffOn ℝ S := by
    intro p hp
    have hc : p ∈ closure U := by
      rcases hp with rfl|hp
      · exact hbaseclosure
      · exact subset_closure hp
    exact (uniqueDiffWithinAt_convex hconv hinterior hc).mono hUS
  have hV : ContDiffOn ℝ ∞ V (S ×ˢ (univ : Set ℝ)) := by
    have hd := spatial_derivative_within_smooth S univ hS isOpen_univ Γ hΓsmooth
    have heval : ContDiffOn ℝ ∞
        (fun z => spatialDerivativeWithin S univ Γ z (1:ℝ)) (S ×ˢ (univ : Set ℝ)) :=
      hd.1.clm_apply contDiffOn_const
    apply heval.congr
    intro z hz
    exact (hΓ z.1 hz.1 z.2).unique (hd.2 z.1 hz.1 z.2 (mem_univ _)).hasDerivAt
  obtain ⟨χ,H,hinit,hχc,hHc,hχs,hHs,hdata⟩ :=
    parametric_normal_graph_closed_coordinates U hU (0,0) hnotU Γ V β T κ h₀ L δ K v
      hΓsmooth hβsmooth hTsmooth hκsmooth hh₀smooth hΓ hβ hTd hunit hspeed
      hΓper hβper hh₀per hinitial hδ hK hsmall hregular hposition htangent hcurvature
  let y : S → ℝ → NormalProjectionState := fun p s => (s,(χ (p.val,s)-s,H (p.val,s)))
  have hy : Continuous (fun z : S × ℝ => y z.1 z.2) := by
    have hi : Continuous (fun z : S × ℝ => (z.1.val,z.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hm : ∀ z : S × ℝ, (z.1.val,z.2) ∈ S ×ˢ (univ : Set ℝ) :=
      fun z => ⟨z.1.property,mem_univ _⟩
    exact continuous_snd.prodMk (((hχc.comp_continuous hi hm).sub continuous_snd).prodMk
      (hHc.comp_continuous hi hm))
  have hys (p : S) : ContDiff ℝ ∞ (y p) :=
    contDiff_id.prodMk ((((hdata p.val p.property).1).sub contDiff_id).prodMk
      (hdata p.val p.property).2.1)
  have hysmall (p : S) (s : ℝ) : |(y p s).2.1|<3*δ :=
    ((hdata p.val p.property).2.2.2.2 s).2.1
  have hyODE (p : S) (s : ℝ) : HasDerivAt (y p)
      (normalProjectionVectorField T κ V (p.val,y p s)) s :=
    ((hdata p.val p.property).2.2.2.2 s).2.2.2.2
  have hsmall3 : δ+K*(3*δ)<1 := by nlinarith only [hsmall,mul_nonneg hK hδ.le,hδ]
  obtain ⟨F,hFc,hFeval,u,hu,hcoord⟩ := normal_projection_sobolev_trace L S hS V hV
    T κ hTsmooth hκsmooth hTd hunit δ K (3*δ) hK hsmall3 hcurvature htangent
    y hy hys hysmall hyODE (fun z => (H z:ℂ)) (fun _ _ _ => rfl)
    (fun p hp s => congrArg Complex.ofReal ((hdata p hp).2.2.2.1 s))
  have hF₀ (p : ℝ × ℝ) (hp : p ∈ S) (s : ℝ) : F 0 p (s:AddCircle L)=(H (p,s):ℂ) := by
    simpa only [Fin.val_zero,iteratedDeriv_zero] using! hFeval p hp 0 s
  have hF₁ (p : ℝ × ℝ) (hp : p ∈ S) (s : ℝ) :
      F 1 p (s:AddCircle L)=((deriv (fun x : ℝ => H (p,x)) s:ℝ):ℂ) := by
    have hd : HasDerivAt (fun x : ℝ => (H (p,x):ℂ))
        ((deriv (fun x : ℝ => H (p,x)) s:ℝ):ℂ) s :=
      ((hdata p hp).2.1.differentiable (by simp) s).hasDerivAt.ofReal_comp
    calc
      _ = deriv (fun x => (H (p,x):ℂ)) s := by
        simpa only [Fin.val_one,iteratedDeriv_one] using! hFeval p hp 1 s
      _ = ((deriv (fun x : ℝ => H (p,x)) s:ℝ):ℂ) := hd.deriv
  have hframe : Continuous (fun s => conj (T s)*β s) :=
    (Complex.continuous_conj.comp hTsmooth.continuous).mul hβsmooth.continuous
  let bc : C(AddCircle L,ℂ) := periodicCircleFunction L
    (fun s => ((conj (T s)*β s).re:ℂ))
    (fun s => by
      change ((conj (T (s+L))*β (s+L)).re:ℂ)=((conj (T s)*β s).re:ℂ)
      rw [hTper s,hβper s])
    (Complex.continuous_ofReal.comp (Complex.reCLM.continuous.comp hframe))
  let ηc : C(AddCircle L,ℂ) := periodicCircleFunction L
    (fun s => ((conj (T s)*β s).im:ℂ))
    (fun s => by
      change ((conj (T (s+L))*β (s+L)).im:ℂ)=((conj (T s)*β s).im:ℂ)
      rw [hTper s,hβper s])
    (Complex.continuous_ofReal.comp (Complex.imCLM.continuous.comp hframe))
  let kc : C(AddCircle L,ℂ) := periodicCircleFunction L (fun s => (κ s:ℂ))
    (fun s => congrArg Complex.ofReal (hκper s))
    (Complex.continuous_ofReal.comp hκsmooth.continuous)
  have hb (s : ℝ) : bc (s:AddCircle L)=((conj (T s)*β s).re:ℂ) := rfl
  have hη (s : ℝ) : ηc (s:AddCircle L)=((conj (T s)*β s).im:ℂ) := rfl
  have hk (s : ℝ) : kc (s:AddCircle L)=(κ s:ℂ) := rfl
  let A : (ℝ × ℝ) → C(AddCircle L,ℂ) := fun p => 1-kc*F 0 p
  let G : (ℝ × ℝ) → C(AddCircle L,ℂ) := fun p =>
    bc+(ηc+F 0 p)*F 1 p*Ring.inverse (A p)
  have hAe (p : ℝ × ℝ) (hp : p ∈ S) (s : ℝ) :
      A p (s:AddCircle L)=((1-κ s*H (p,s):ℝ):ℂ) := by
    simp only [A,ContinuousMap.sub_apply,ContinuousMap.one_apply,ContinuousMap.mul_apply,
      hk,hF₀ p hp s,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul]
  have hAu (p : ℝ × ℝ) (hp : p ∈ S) : IsUnit (A p) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i s
    rw [hAe p hp s]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (((hdata p hp).2.2.2.2 s).2.2.1))
  have hGe (p : ℝ × ℝ) (hp : p ∈ S) (s : ℝ) :
      G p (s:AddCircle L)=
        (((conj (T s)*β s).re+((conj (T s)*β s).im+H (p,s))*
          deriv (fun x => H (p,x)) s/(1-κ s*H (p,s)):ℝ):ℂ) := by
    change bc (s:AddCircle L)+(ηc (s:AddCircle L)+F 0 p (s:AddCircle L))*
      F 1 p (s:AddCircle L)*Ring.inverse (A p) (s:AddCircle L)=_
    rw [continuous_map_ring_inverse_apply (A p) (hAu p hp),hAe p hp s,
      hb s,hη s,hF₀ p hp s,hF₁ p hp s]
    simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_inv,div_eq_mul_inv]
  have hAc : ContinuousOn A S := continuousOn_const.sub (continuousOn_const.mul (hFc 0))
  have hGc : ContinuousOn G S := by
    intro p hp
    have hi : ContinuousAt (Ring.inverse : C(AddCircle L,ℂ) → C(AddCircle L,ℂ)) (A p) := by
      have hh := NormedRing.inverse_continuousAt (hAu p hp).unit
      rw [(hAu p hp).unit_spec] at hh
      exact hh
    have hInv : ContinuousWithinAt (fun q => Ring.inverse (A q)) S p :=
      hi.comp_continuousWithinAt (hAc p hp)
    exact continuousWithinAt_const.add
      (((continuousWithinAt_const.add (hFc 0 p hp)).mul (hFc 1 p hp)).mul hInv)
  have hHbase : (fun s => H ((0,0),s))=h₀ := funext fun s => (hinit s).2
  have hQbase : F 0 (0,0)=Q₀ := by
    apply ContinuousMap.ext
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i s
    rw [hF₀ (0,0) hbase s,hQ₀ s,(hinit s).2]
  have hGbase : G (0,0)=G₀ := by
    apply ContinuousMap.ext
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i s
    rw [hGe (0,0) hbase s,hG₀ s,(hinit s).2,hHbase]
  have hΓU := hΓsmooth.mono (prod_mono_left hUS)
  have hΓslice (p : ℝ × ℝ) (hp : p ∈ U) : ContDiff ℝ ∞ (fun s => Γ (p,s)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro s
    have hdomain : (U ×ˢ (univ : Set ℝ)) ∈ 𝓝 (p,s) :=
      (hU.prod isOpen_univ).mem_nhds ⟨hp,mem_univ s⟩
    exact (hΓU.contDiffAt hdomain).comp s (contDiffAt_const.prodMk contDiffAt_id)
  have hYeq (r : ℝ) (hr : r ∈ Ioo 0 T₀) : (fun s => Γ ((r,0),s))=Y r := by
    funext s
    have hp : (r,(0:ℝ)) ∈ S := hUS ⟨hr,⟨by linarith only [ha₀],ha₀⟩⟩
    simpa only [neg_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul] using hΓY (r,0) hp s
  have hYsmooth (r : ℝ) (hr : r ∈ Ioo 0 T₀) : ContDiff ℝ ∞ (Y r) := by
    rw [← hYeq r hr]
    exact hΓslice (r,0) ⟨hr,⟨by linarith only [ha₀],ha₀⟩⟩
  have hδone : δ<1 := by nlinarith only [hsmall,mul_nonneg hK hδ.le]
  have hYreg (r : ℝ) (hr : r ∈ Ioo 0 T₀) (s : ℝ) : deriv (Y r) s≠0 := by
    have hp : (r,(0:ℝ)) ∈ S := hUS ⟨hr,⟨by linarith only [ha₀],ha₀⟩⟩
    rw [← hYeq r hr,(hΓ (r,0) hp s).deriv]
    intro hz
    have hh := htangent (r,0) hp s
    rw [hz,zero_sub,norm_neg,hunit s] at hh
    linarith only [hh,hδone]
  let n : ℝ → ℂ := fun s => I*T s
  have hn (s : ℝ) : HasDerivAt n (-(κ s:ℂ)*T s) s := by
    apply ((hTd s).const_mul I).congr_deriv
    calc
      I*(I*(κ s:ℂ)*T s) = I^2*((κ s:ℂ)*T s) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hYgraph (p : ℝ × ℝ) (hp : p ∈ U) (s : ℝ) :
      Y p.1 (χ (p,s))=Complex.exp ((p.2:ℂ)*I)*normalGraphCurve β n (fun x => H (p,x)) s := by
    have heq := ((hdata p (hUS hp)).2.2.2.2 s).1
    rw [hΓY p (hUS hp) (χ (p,s))] at heq
    have hR : Complex.exp ((p.2:ℂ)*I)*Complex.exp ((-p.2:ℝ)*I)=1 := by
      rw [Complex.ofReal_neg,neg_mul,Complex.exp_neg]
      exact mul_inv_cancel₀ (Complex.exp_ne_zero _)
    have hh := congrArg (fun z : ℂ => Complex.exp ((p.2:ℂ)*I)*z) heq
    calc
      _ = (Complex.exp ((p.2:ℂ)*I)*Complex.exp ((-p.2:ℝ)*I))*Y p.1 (χ (p,s)) := by
        rw [hR,one_mul]
      _ = Complex.exp ((p.2:ℂ)*I)*(β s+I*(H (p,s):ℂ)*T s) := by
        simpa only [mul_assoc] using hh
      _ = _ := by dsimp only [normalGraphCurve,n]; congr 1; ring
  let E : C(AddCircle L,ℂ) →L[ℂ] CircleL2 L := ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
  have hQtrace : ContinuousWithinAt (fun p => circleContinuousL2 L (F 0 p)) S (0,0) :=
    E.continuous.continuousAt.comp_continuousWithinAt (hFc 0 (0,0) hbase)
  have hGtrace : ContinuousWithinAt (fun p => circleContinuousL2 L (G p)) S (0,0) :=
    E.continuous.continuousAt.comp_continuousWithinAt (hGc (0,0) hbase)
  obtain ⟨τ,hτ,hτT,a,ha,haa₀,θ,hθ,hθtrace,hθzero,hroot⟩ :=
    normal_graph_phase_fixed_family L T₀ a₀ hT₀ ha₀ Y β T n κ χ H hYsmooth hYreg hχs hHs
      (fun p hp s => ((hdata p (hUS hp)).2.2.2.2 s).2.2.2.1) hβ hn hunit (fun _ => rfl)
      (fun p hp s => ((hdata p (hUS hp)).2.2.2.2 s).2.2.1) hYgraph
      (F 0) G ψ hψ hF₀ (fun p hp => hGe p (hUS hp)) hQtrace hGtrace
      (by simpa only [hQbase] using hphase₀) (by simpa only [hGbase] using hpair₀)
  have hpathU : MapsTo (fun r => (r,θ r)) (Ioo 0 τ) U := by
    intro r hr
    refine ⟨⟨hr.1,hr.2.trans_le hτT⟩,?_⟩
    apply abs_lt.mp
    exact (hroot r hr).1.trans_le (by linarith only [ha,haa₀])
  have hθci : ContinuousOn θ (Ico 0 τ) := by
    intro r hr
    by_cases hz : r=0
    · subst r
      have hi : ContinuousWithinAt θ (Ioi (0:ℝ)) 0 := by
        change Tendsto θ (𝓝[>] (0:ℝ)) (𝓝 (θ 0))
        rw [hθzero]
        exact hθtrace
      exact (continuousWithinAt_Ioi_iff_Ici.mp hi).mono (fun s hs => hs.1)
    · have hp : 0<r := lt_of_le_of_ne hr.1 (Ne.symm hz)
      have hneigh : Ioo (0:ℝ) τ ∈ 𝓝 r := isOpen_Ioo.mem_nhds ⟨hp,hr.2⟩
      exact (hθ.contDiffAt hneigh).continuousAt.continuousWithinAt
  have hpathS : MapsTo (fun r => (r,θ r)) (Ico 0 τ) S := by
    intro r hr
    by_cases hz : r=0
    · subst r
      change ((0:ℝ),θ 0) ∈ S
      rw [hθzero]
      exact hbase
    · exact hUS (hpathU ⟨lt_of_le_of_ne hr.1 (Ne.symm hz),hr.2⟩)
  have hpathH4 : ContinuousOn (fun r => u (r,θ r)) (Ico 0 τ) :=
    hu.comp (continuous_id.continuousOn.prodMk hθci) hpathS
  exact ⟨χ,H,F,u,G,hinit,hχc,hHc,hχs,hHs,hdata,hFc,hFeval,hu,hcoord,
    hQbase,hGbase,hGc,hGe,τ,hτ,hτT,a,ha,haa₀,θ,hθ,hθtrace,hθzero,hpathU,hpathH4,hroot⟩

end Lemniscate
