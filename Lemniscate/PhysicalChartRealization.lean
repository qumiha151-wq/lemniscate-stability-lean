import Lemniscate.PhysicalNormalGraphPDEConverse
import Lemniscate.PhysicalTimeInverse
import Lemniscate.OrderIsoDerivative

/-! A local normal chart of a given physical free elastic flow. The graph
identity is obtained from the actual normalized projection coordinates. -/
noncomputable section
namespace Lemniscate
open Complex Set Filter
open scoped ContDiff Topology ComplexConjugate ENNReal

private theorem local_rotation_inverse (θ : ℝ) :
    Complex.exp ((θ:ℂ)*I)*Complex.exp ((-θ:ℝ)*I)=1 := by
  rw [Complex.ofReal_neg,neg_mul,Complex.exp_neg]
  exact mul_inv_cancel₀ (Complex.exp_ne_zero _)

private theorem local_auxiliary_graph_identity
    (a r θ h : ℝ) (ha : a≠0) (hr : r≠0) (z p β t : ℂ)
    (heq : (a:ℂ)*Complex.exp ((-θ:ℝ)*I)*(z-p)/(r:ℂ)=
      (a:ℂ)*β+I*(h:ℂ)*t) :
    z=p+(r:ℂ)*(Complex.exp ((θ:ℂ)*I)*(β+((h/a:ℝ):ℂ)*(I*t))) := by
  have haC : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  let R := Complex.exp ((θ:ℂ)*I)
  let Ri := Complex.exp ((-θ:ℝ)*I)
  have hR : R*Ri=1 := local_rotation_inverse θ
  have he := congrArg (fun w : ℂ => (r:ℂ)*R*w) heq
  have hleft : (r:ℂ)*R*((a:ℂ)*Ri*(z-p)/(r:ℂ))=(a:ℂ)*(z-p) := by
    calc
      _ = (a:ℂ)*(R*Ri)*(z-p)*((r:ℂ)/(r:ℂ)) := by ring
      _ = _ := by rw [hR,div_self hrC]; ring
  change (r:ℂ)*R*((a:ℂ)*Ri*(z-p)/(r:ℂ))=
    (r:ℂ)*R*((a:ℂ)*β+I*(h:ℂ)*t) at he
  rw [hleft] at he
  apply mul_left_cancel₀ haC
  calc
    (a:ℂ)*z=(a:ℂ)*(z-p)+(a:ℂ)*p := by ring
    _ = (r:ℂ)*R*((a:ℂ)*β+I*(h:ℂ)*t)+(a:ℂ)*p := by rw [he]
    _ = (a:ℂ)*(p+(r:ℂ)*(R*(β+((h/a:ℝ):ℂ)*(I*t)))) := by
      push_cast
      field_simp [haC]
      <;> ring

/-- The auxiliary projection identity gives the actual graph of the
original physical curve after its fixed original parameter change. -/
theorem projected_physical_graph_identity
    (S₀ a σ₀ α₀ r₀ : ℝ) (ha : 0<a) (hS₀ : S₀≠0)
    (ρ : ℝ → ℝ) (p₀ : ℂ) (χ₀ : ℝ → ℝ)
    (Y : ℝ → ℝ → ℂ) (Γ : (ℝ × ℝ) × ℝ → ℂ)
    (χ H : (ℝ × ℝ) × ℝ → ℝ) (θ : ℝ → ℝ)
    (β T : ℝ → ℂ) (U : Set (ℝ × ℝ))
    (hr : (r₀,θ r₀)∈U)
    (hρ : ρ (physicalTime a (σ₀+r₀))≠0)
    (hΓY : ∀ p ∈ U, ∀ x : ℝ,
      Γ (p,x)=(S₀:ℂ)*Complex.exp ((-(α₀+p.2):ℝ)*I)*
        (Y (physicalTime a (σ₀+p.1)) (χ₀ (x/S₀))-p₀)/
          (ρ (physicalTime a (σ₀+p.1)):ℂ))
    (hgraph : ∀ p ∈ U, ∀ s : ℝ,
      Γ (p,χ (p,S₀*s))=(S₀:ℂ)*β s+I*(H (p,S₀*s):ℂ)*T s) :
    ∀ s : ℝ,
      Y (physicalTime a (σ₀+r₀)) (χ₀ (χ ((r₀,θ r₀),S₀*s)/S₀))=
        p₀+(ρ (physicalTime a (σ₀+r₀)):ℂ)*
          (Complex.exp (((α₀+θ r₀):ℂ)*I)*
            (β s+((H ((r₀,θ r₀),S₀*s)/S₀:ℝ):ℂ)*(I*T s))) := by
  intro s
  have heq := (hΓY (r₀,θ r₀) hr (χ ((r₀,θ r₀),S₀*s))).symm.trans
    (hgraph (r₀,θ r₀) hr s)
  have hresult := local_auxiliary_graph_identity S₀ (ρ (physicalTime a (σ₀+r₀)))
    (α₀+θ r₀) (H ((r₀,θ r₀),S₀*s)) hS₀ hρ
    (Y (physicalTime a (σ₀+r₀)) (χ₀ (χ ((r₀,θ r₀),S₀*s)/S₀)))
    p₀ (β s) (T s) heq
  simpa only [Complex.ofReal_add] using hresult

private def localChartHeight (b σ₀ : ℝ) (θ : ℝ → ℝ)
    (H : (ℝ × ℝ) × ℝ → ℝ) (σ s : ℝ) : ℝ :=
  H ((σ-σ₀,θ (σ-σ₀)),b*s)/b

private def localChartParameter (b σ₀ : ℝ) (θ : ℝ → ℝ)
    (χ : (ℝ × ℝ) × ℝ → ℝ) (χ₀ σ : ℝ → ℝ) (z s : ℝ) : ℝ :=
  χ₀ (χ ((σ z-σ₀,θ (σ z-σ₀)),b*s)/b)

private theorem local_chart_regularity
    (b σ₀ r z₀ : ℝ) (hb : 0<b) (θ σ : ℝ → ℝ)
    (χ H : (ℝ × ℝ) × ℝ → ℝ) (χ₀ : ℝ ≃o ℝ)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hr : (r,θ r)∈U)
    (hχ : ContDiffOn ℝ ∞ χ (U ×ˢ (univ : Set ℝ)))
    (hH : ContDiffOn ℝ ∞ H (U ×ˢ (univ : Set ℝ)))
    (hθ : DifferentiableAt ℝ θ r)
    (hσ : DifferentiableAt ℝ σ z₀) (hσvalue : σ z₀=σ₀+r)
    (hχ₀ : ContDiff ℝ ∞ (χ₀ : ℝ → ℝ))
    (hχ₀inv : ContDiff ℝ ∞ (χ₀.symm : ℝ → ℝ))
    (hpos : ∀ s, 0<deriv (fun x => χ ((r,θ r),x)) s) :
    ContDiff ℝ ∞ (localChartParameter b σ₀ θ χ χ₀ σ z₀) ∧
      ∀ s : ℝ,
        0<deriv (localChartParameter b σ₀ θ χ χ₀ σ z₀) s ∧
        DifferentiableAt ℝ (fun z => localChartParameter b σ₀ θ χ χ₀ σ z s) z₀ ∧
        HasDerivAt (localChartHeight b σ₀ θ H (σ₀+r))
          (deriv (localChartHeight b σ₀ θ H (σ₀+r)) s) s ∧
        HasDerivAt (fun u => localChartHeight b σ₀ θ H u s)
          (deriv (fun u => localChartHeight b σ₀ θ H u s) (σ₀+r)) (σ₀+r) := by
  let q : ℝ → ℝ × ℝ := fun u => (u-σ₀,θ (u-σ₀))
  have hqvalue : q (σ₀+r)=(r,θ r) := by simp only [q,add_sub_cancel_left]
  have hshift : HasDerivAt (fun u : ℝ => u-σ₀) 1 (σ₀+r) :=
    (hasDerivAt_id (σ₀+r)).sub_const σ₀
  have hθAt : HasDerivAt θ (deriv θ r) (σ₀+r-σ₀) := by
    simpa only [add_sub_cancel_left] using hθ.hasDerivAt
  have hθcomp : HasDerivAt (fun u : ℝ => θ (u-σ₀)) (deriv θ r) (σ₀+r) := by
    simpa only [Function.comp_def,mul_one] using! hθAt.comp (σ₀+r) hshift
  have hqD : HasDerivAt q ((1:ℝ),deriv θ r) (σ₀+r) := hshift.prodMk hθcomp
  have hq : DifferentiableAt ℝ q (σ₀+r) := hqD.differentiableAt
  have hsmooth (F : (ℝ × ℝ) × ℝ → ℝ)
      (hF : ContDiffOn ℝ ∞ F (U ×ˢ (univ : Set ℝ))) :
      ContDiff ℝ ∞ (fun s => F ((r,θ r),s)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro s
    have hd : (U ×ˢ (univ : Set ℝ)) ∈ 𝓝 ((r,θ r),s) :=
      (hU.prod isOpen_univ).mem_nhds ⟨hr,mem_univ s⟩
    exact (hF.contDiffAt hd).comp s (contDiffAt_const.prodMk contDiffAt_id)
  have hscaledχ : ContDiff ℝ ∞ (fun s : ℝ => χ ((r,θ r),b*s)/b) :=
    ((hsmooth χ hχ).comp (contDiff_const.mul contDiff_id)).div_const b
  have hparamEq : localChartParameter b σ₀ θ χ χ₀ σ z₀=
      fun s => χ₀ (χ ((r,θ r),b*s)/b) := by
    funext s
    simp only [localChartParameter,hσvalue,add_sub_cancel_left]
  refine ⟨by rw [hparamEq]; exact hχ₀.comp hscaledχ,?_⟩
  intro s
  have hχspace : HasDerivAt (fun x => χ ((r,θ r),x))
      (deriv (fun x => χ ((r,θ r),x)) (b*s)) (b*s) :=
    ((hsmooth χ hχ).differentiable (by simp) (b*s)).hasDerivAt
  have hscale : HasDerivAt (fun x : ℝ => b*x) b s := by
    simpa only [id_eq,mul_one] using! (hasDerivAt_id s).const_mul b
  have hχ₀d : HasDerivAt (χ₀ : ℝ → ℝ)
      (deriv (χ₀ : ℝ → ℝ) (χ ((r,θ r),b*s)/b)) (χ ((r,θ r),b*s)/b) :=
    (hχ₀.differentiable (by simp) _).hasDerivAt
  have hparamD : HasDerivAt (fun x => χ₀ (χ ((r,θ r),b*x)/b))
      (deriv (χ₀ : ℝ → ℝ) (χ ((r,θ r),b*s)/b)*
        deriv (fun x => χ ((r,θ r),x)) (b*s)) s := by
    apply (hχ₀d.comp s ((hχspace.comp s hscale).div_const b)).congr_deriv
    field_simp [hb.ne']
  have hparamPos : 0<deriv (localChartParameter b σ₀ θ χ χ₀ σ z₀) s := by
    rw [hparamEq,hparamD.deriv]
    exact mul_pos (order_iso_deriv_pos χ₀ (hχ₀.differentiable (by simp))
      (hχ₀inv.differentiable (by simp)) _) (hpos (b*s))
  have htime (F : (ℝ × ℝ) × ℝ → ℝ)
      (hF : ContDiffOn ℝ ∞ F (U ×ˢ (univ : Set ℝ))) :
      DifferentiableAt ℝ (fun u => F (q u,b*s)) (σ₀+r) := by
    have hd : (U ×ˢ (univ : Set ℝ)) ∈ 𝓝 ((r,θ r),b*s) :=
      (hU.prod isOpen_univ).mem_nhds ⟨hr,mem_univ _⟩
    have hFAt : DifferentiableAt ℝ F (q (σ₀+r),b*s) := by
      rw [hqvalue]
      exact (hF.contDiffAt hd).differentiableAt (by simp)
    exact hFAt.comp (σ₀+r) (hq.prodMk (differentiableAt_const (b*s)))
  have hnormχ : DifferentiableAt ℝ (fun u => χ₀ (χ (q u,b*s)/b)) (σ₀+r) :=
    (hχ₀.differentiable (by simp) _).comp (σ₀+r) ((htime χ hχ).div_const b)
  have hphysicalχ : DifferentiableAt ℝ
      (fun z => localChartParameter b σ₀ θ χ χ₀ σ z s) z₀ := by
    have hh : DifferentiableAt ℝ (fun u => χ₀ (χ (q u,b*s)/b)) (σ z₀) := by
      rw [hσvalue]
      exact hnormχ
    exact hh.comp z₀ hσ
  have hheightSpace : ContDiff ℝ ∞ (localChartHeight b σ₀ θ H (σ₀+r)) := by
    change ContDiff ℝ ∞ (fun x => H (q (σ₀+r),b*x)/b)
    rw [hqvalue]
    exact ((hsmooth H hH).comp (contDiff_const.mul contDiff_id)).div_const b
  refine ⟨hparamPos,hphysicalχ,(hheightSpace.differentiable (by simp) s).hasDerivAt,?_⟩
  exact ((htime H hH).div_const b).hasDerivAt

/-- Actual auxiliary normal-projection coordinates of a given physical
free elastic flow satisfy the physical scalar height equation. The
physical graph, its time derivatives and its orientation are derived
from the coupling, rather than assumed as an evolution equation. -/
theorem physical_chart_scalar_equation
    (b a σ₀ α₀ T₀ c : ℝ) (hb : 0<b) (ha : 0<a) (hσ₀ : 0≤σ₀)
    (ρ : ℝ → ℝ) (p₀ : ℂ) (χ₀ : ℝ ≃o ℝ)
    (hχ₀ : ContDiff ℝ ∞ (χ₀ : ℝ → ℝ))
    (hχ₀inv : ContDiff ℝ ∞ (χ₀.symm : ℝ → ℝ))
    (Y : ℝ → ℝ → ℂ) (Γ : (ℝ × ℝ) × ℝ → ℂ)
    (χ H : (ℝ × ℝ) × ℝ → ℝ) (θ : ℝ → ℝ)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hθ : ContDiffOn ℝ 1 θ (Ioo 0 T₀))
    (hpath : MapsTo (fun r => (r,θ r)) (Ioo 0 T₀) U)
    (hχ : ContDiffOn ℝ ∞ χ (U ×ˢ (univ : Set ℝ)))
    (hH : ContDiffOn ℝ ∞ H (U ×ˢ (univ : Set ℝ)))
    (hχpos : ∀ r ∈ Ioo 0 T₀, ∀ x, 0<deriv (fun s => χ ((r,θ r),s)) x)
    (β t n : ℝ → ℂ) (k : ℝ → ℝ)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (hn : ∀ s, HasDerivAt n (-(k s:ℂ)*t s) s)
    (hu : ∀ s, ‖t s‖=1) (hN : ∀ s, n s=I*t s)
    (hregular : ∀ r ∈ Ioo 0 T₀, ∀ s,
      0<1-k s*(H ((r,θ r),b*s)/b))
    (hρ : ∀ z : ℝ, 0≤z → 0<ρ z)
    (hρd : ∀ z : ℝ, 0<z → HasDerivAt ρ (c*(ρ z)⁻¹^3) z)
    (hσd : ∀ z : ℝ, 0<z → HasDerivAt (normalizedTime a) ((ρ z)⁻¹^4) z)
    (hYspace : ∀ z : ℝ, 0<z → ContDiff ℝ ∞ (Y z))
    (hYreg : ∀ z : ℝ, 0<z → ∀ s, deriv (Y z) s≠0)
    (hYjoint : ∀ z : ℝ, 0<z → ∀ s,
      DifferentiableAt ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (z,s))
    (hYflow : ∀ z : ℝ, 0<z → ∀ s,
      (conj (deriv (fun u => Y u s) z)*
        (I*deriv (Y z) s/(‖deriv (Y z) s‖:ℂ))).re=-planarElasticForce (Y z) s)
    (hΓY : ∀ p ∈ U, ∀ x : ℝ,
      Γ (p,x)=(b:ℂ)*Complex.exp ((-(α₀+p.2):ℝ)*I)*
        (Y (physicalTime a (σ₀+p.1)) (χ₀ (x/b))-p₀)/
          (ρ (physicalTime a (σ₀+p.1)):ℂ))
    (hgraph : ∀ p ∈ U, ∀ s : ℝ,
      Γ (p,χ (p,b*s))=(b:ℂ)*β s+I*(H (p,b*s):ℂ)*t s) :
    let h : ℝ → ℝ → ℝ := fun σ s => H ((σ-σ₀,θ (σ-σ₀)),b*s)/b
    ∀ r ∈ Ioo 0 T₀, ∀ s : ℝ,
      deriv (fun σ => h σ s) (σ₀+r)+deriv θ r*
        ((conj (t s)*β s).re+((conj (t s)*β s).im+h (σ₀+r) s)*
          deriv (h (σ₀+r)) s/(1-k s*h (σ₀+r) s))=
        normalGraphFlowRHS β n k (h (σ₀+r)) c s := by
  dsimp only
  let h : ℝ → ℝ → ℝ := localChartHeight b σ₀ θ H
  let Θ : ℝ → ℝ := fun σ => α₀+θ (σ-σ₀)
  let χp : ℝ → ℝ → ℝ := localChartParameter b σ₀ θ χ χ₀ (normalizedTime a)
  have hInv := physical_time_inverse a ha
  intro r hr
  let z₀ := physicalTime a (σ₀+r)
  have hσr : 0<σ₀+r := add_pos_of_nonneg_of_pos hσ₀ hr.1
  have hz : 0<z₀ := (hInv.2.1 (σ₀+r)).2.2.2 hσr
  have hσvalue : normalizedTime a z₀=σ₀+r := (hInv.2.1 (σ₀+r)).1
  have hθAt : DifferentiableAt ℝ θ r :=
    (hθ.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by simp)
  have hreg := local_chart_regularity b σ₀ r z₀ hb θ (normalizedTime a) χ H χ₀ U hU
    (hpath hr) hχ hH hθAt (hσd z₀ hz).differentiableAt hσvalue hχ₀ hχ₀inv
    (hχpos r hr)
  have hspace : ∀ s, HasDerivAt (h (normalizedTime a z₀))
      (deriv (h (σ₀+r)) s) s := by
    intro s
    rw [hσvalue]
    exact (hreg.2 s).2.2.1
  have htime : ∀ s, HasDerivAt (fun σ => h σ s)
      (deriv (fun σ => h σ s) (σ₀+r)) (normalizedTime a z₀) := by
    intro s
    rw [hσvalue]
    exact (hreg.2 s).2.2.2
  have hΘ : HasDerivAt Θ (deriv θ r) (normalizedTime a z₀) := by
    rw [hσvalue]
    have hθd : HasDerivAt θ (deriv θ r) (σ₀+r-σ₀) := by
      simpa only [add_sub_cancel_left] using hθAt.hasDerivAt
    simpa only [Θ,Function.comp_def,id_eq,mul_one] using!
      (hθd.comp (σ₀+r) ((hasDerivAt_id (σ₀+r)).sub_const σ₀)).const_add α₀
  have hsub : normalizedTime a z₀-σ₀=r := by rw [hσvalue]; ring
  have hmapr : Tendsto (fun z => normalizedTime a z-σ₀) (𝓝 z₀) (𝓝 r) := by
    have hh : Tendsto (fun z => normalizedTime a z-σ₀) (𝓝 z₀)
        (𝓝 (normalizedTime a z₀-σ₀)) := (hσd z₀ hz).continuousAt.sub_const σ₀
    simpa only [hsub] using hh
  have hgerm : ∀ᶠ z : ℝ in 𝓝 z₀, ∀ s : ℝ,
      Y z (χp z s)=p₀+(ρ z:ℂ)*
        (Complex.exp ((Θ (normalizedTime a z):ℂ)*I)*
          normalGraphCurve β n (h (normalizedTime a z)) s) := by
    have hpos : Ioi (0:ℝ) ∈ 𝓝 z₀ := isOpen_Ioi.mem_nhds hz
    filter_upwards [hmapr.eventually (isOpen_Ioo.mem_nhds hr),hpos] with z hzr hzpos
    have hclock : physicalTime a (σ₀+(normalizedTime a z-σ₀))=z := by
      rw [show σ₀+(normalizedTime a z-σ₀)=normalizedTime a z by ring]
      exact hInv.2.2 z hzpos.le
    have hscale : ρ (physicalTime a (σ₀+(normalizedTime a z-σ₀)))≠0 := by
      rw [hclock]
      exact (hρ z hzpos.le).ne'
    have hh := projected_physical_graph_identity b a σ₀ α₀
      (normalizedTime a z-σ₀) ha hb.ne' ρ p₀ χ₀ Y Γ χ H θ β t U
      (hpath hzr) hscale hΓY hgraph
    rw [hclock] at hh
    intro s
    simpa only [χp,localChartParameter,h,localChartHeight,Θ,normalGraphCurve,hN s,
      Complex.ofReal_add] using hh s
  have hscalar := physical_normal_graph_pde_converse Y χp
    (fun s => deriv (fun z => χp z s) z₀) β t n k h Θ ρ (normalizedTime a) p₀ z₀ c
    (deriv θ r) (fun s => deriv (fun σ => h σ s) (σ₀+r))
    (fun s => deriv (h (σ₀+r)) s)
    (hYspace z₀ hz) hreg.1 (hYreg z₀ hz) (fun s => (hreg.2 s).1)
    (fun s => hYjoint z₀ hz (χp z₀ s))
    (fun s => (hreg.2 s).2.1.hasDerivAt) (hYflow z₀ hz)
    hβ hn hu hN hspace htime hΘ (hρ z₀ hz.le) (hρd z₀ hz) (hσd z₀ hz)
    (fun s => by
      rw [hσvalue]
      simpa only [h,localChartHeight,add_sub_cancel_left] using hregular r hr s) hgerm
  simpa only [hσvalue,h,localChartHeight] using! hscalar

end Lemniscate
