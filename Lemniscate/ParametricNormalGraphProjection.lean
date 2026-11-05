import Lemniscate.UniformScalarImplicitRoot
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Basic

/-! A nearby family of parametrized immersed curves has a jointly smooth
normal projection. The moving curve need not have unit speed. -/
noncomputable section
namespace Lemniscate
open Complex Filter Set Function
open scoped Topology ContDiff ComplexConjugate NNReal

/-- Uniform C1 proximity gives actual normal-graph coordinates, jointly
smooth in the open parameter set and the spatial variable. The residual
bound retains continuous identification with an initially aligned graph. -/
theorem parametric_normal_graph_projection
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    (U : Set P) (hU : IsOpen U) (Γ V : P × ℝ → ℂ)
    (β Tβ : ℝ → ℂ) (κ : ℝ → ℝ) (L δ K v : ℝ)
    (hΓsmooth : ContDiffOn ℝ ∞ Γ (U ×ˢ (univ : Set ℝ)))
    (hβsmooth : ContDiff ℝ ∞ β)
    (hΓ : ∀ p ∈ U, ∀ s : ℝ, HasDerivAt (fun x => Γ (p,x)) (V (p,s)) s)
    (hβ : ∀ s, HasDerivAt β (Tβ s) s)
    (hTβ : ∀ s, HasDerivAt Tβ (I*(κ s:ℂ)*Tβ s) s)
    (hspeed : ∀ p ∈ U, ∀ s : ℝ, ‖V (p,s)‖ ≤ v)
    (huβ : ∀ s, ‖Tβ s‖ = 1)
    (hΓper : ∀ p ∈ U, Function.Periodic (fun s => Γ (p,s)) L)
    (hβper : Function.Periodic β L)
    (hδ : 0 < δ) (hK : 0 ≤ K) (hsmall : δ+2*K*δ < 1/2)
    (hregular : K*(δ+2*v*δ) < 1)
    (hposition : ∀ p ∈ U, ∀ s : ℝ, ‖Γ (p,s)-β s‖ ≤ δ)
    (htangent : ∀ p ∈ U, ∀ s : ℝ, ‖V (p,s)-Tβ s‖ ≤ δ)
    (hcurvature : ∀ s, |κ s| ≤ K) :
    ∃ χ H : P × ℝ → ℝ,
      ContDiffOn ℝ ∞ χ (U ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ H (U ×ˢ (univ : Set ℝ)) ∧
      ∀ p ∈ U,
        Function.Periodic (fun s => χ (p,s)-s) L ∧
        Function.Periodic (fun s => H (p,s)) L ∧
        ∀ s : ℝ,
          Γ (p,χ (p,s)) = β s+I*(H (p,s):ℂ)*Tβ s ∧
          |χ (p,s)-s| ≤ 2*|(conj (Tβ s)*(Γ (p,s)-β s)).re| ∧
          |H (p,s)| ≤ δ+2*v*δ ∧ 0 < 1-κ s*H (p,s) ∧
          HasDerivAt (fun x => χ (p,x))
            ((1-κ s*H (p,s))/(conj (Tβ s)*V (p,χ (p,s))).re) s ∧
          0 < deriv (fun x => χ (p,x)) s ∧
          HasDerivAt (fun x => H (p,x))
            (deriv (fun x => χ (p,x)) s*(conj (Tβ s)*V (p,χ (p,s))).im) s := by
  let D : Set (P × ℝ) := U ×ˢ (univ : Set ℝ)
  have hD : IsOpen D := hU.prod isOpen_univ
  have hTsmooth : ContDiff ℝ ∞ Tβ := by
    have heq : deriv β = Tβ := funext fun s => (hβ s).deriv
    rw [← heq]
    exact (contDiff_infty_iff_deriv.mp hβsmooth).2
  have hself (s : ℝ) : conj (Tβ s)*Tβ s = 1 := by
    rw [Complex.conj_mul',huβ s]
    simp
  have hTper : Function.Periodic Tβ L := by
    intro s
    have hshift : HasDerivAt (fun x => β (x+L)) (Tβ (s+L)) s := by
      simpa only [one_smul] using! (hβ (s+L)).scomp s ((hasDerivAt_id s).add_const L)
    exact hshift.unique ((hβ s).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => hβper x))
  have hΓlip (p : P) (hp : p ∈ U) (a b : ℝ) : ‖Γ (p,b)-Γ (p,a)‖ ≤ v*|b-a| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := (univ : Set ℝ)) (C := v)
        (fun x _ => (hΓ p hp x).hasDerivWithinAt)
        (fun x _ => hspeed p hp x) convex_univ (mem_univ a) (mem_univ b)
  have hTlip (a b : ℝ) : ‖Tβ b-Tβ a‖ ≤ K*|b-a| := by
    have hb (x : ℝ) : ‖I*(κ x:ℂ)*Tβ x‖ ≤ K := by
      simpa only [norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
        huβ,mul_one,one_mul] using hcurvature x
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := (univ : Set ℝ)) (C := K)
        (fun x _ => (hTβ x).hasDerivWithinAt) (fun x _ => hb x)
        convex_univ (mem_univ a) (mem_univ b)
  have htshift (p : P) (hp : p ∈ U) (s x : ℝ) :
      ‖V (p,s+x)-Tβ s‖ ≤ δ+K*|x| := by
    calc
      _ = ‖(V (p,s+x)-Tβ (s+x))+(Tβ (s+x)-Tβ s)‖ := by congr 1; ring
      _ ≤ ‖V (p,s+x)-Tβ (s+x)‖+‖Tβ (s+x)-Tβ s‖ := norm_add_le _ _
      _ ≤ δ+K*|x| := add_le_add (htangent p hp (s+x)) (by simpa using hTlip s (s+x))
  let f : (P × ℝ) × ℝ → ℝ := fun z =>
    (conj (Tβ z.1.2)*(Γ (z.1.1,z.1.2+z.2)-β z.1.2)).re
  have hf : ContDiffOn ℝ ∞ f (D ×ˢ (univ : Set ℝ)) := by
    have hmap : ContDiff ℝ ∞ (fun z : (P × ℝ) × ℝ => (z.1.1,z.1.2+z.2)) :=
      contDiff_fst.fst.prodMk (contDiff_fst.snd.add contDiff_snd)
    have hΓcomp := hΓsmooth.comp hmap.contDiffOn
      (show MapsTo (fun z : (P × ℝ) × ℝ => (z.1.1,z.1.2+z.2))
        (D ×ˢ (univ : Set ℝ)) D from fun z hz => ⟨hz.1.1,mem_univ _⟩)
    exact Complex.reCLM.contDiff.comp_contDiffOn
      ((Complex.conjCLE.contDiff.comp (hTsmooth.comp contDiff_fst.snd)).contDiffOn.mul
        (hΓcomp.sub (hβsmooth.comp contDiff_fst.snd).contDiffOn))
  have hdf (p : P) (hp : p ∈ U) (s x : ℝ) : HasDerivAt (fun y => f ((p,s),y))
      (conj (Tβ s)*V (p,s+x)).re x := by
    have hd := (((hΓ p hp (s+x)).scomp x ((hasDerivAt_id x).const_add s)).sub_const
      (β s)).const_mul (conj (Tβ s))
    simpa only [one_smul] using! Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  have hdclose (p : P) (hp : p ∈ U) (s x : ℝ) :
      |1-(conj (Tβ s)*V (p,s+x)).re| ≤ δ+K*|x| := by
    have heq : 1-(conj (Tβ s)*V (p,s+x)).re =
        (conj (Tβ s)*(Tβ s-V (p,s+x))).re := by
      rw [mul_sub,hself,Complex.sub_re,Complex.one_re]
    rw [heq]
    calc
      _ ≤ ‖conj (Tβ s)*(Tβ s-V (p,s+x))‖ := Complex.abs_re_le_norm _
      _ = ‖V (p,s+x)-Tβ s‖ := by rw [norm_mul,Complex.norm_conj,huβ,one_mul,norm_sub_rev]
      _ ≤ _ := htshift p hp s x
  let c : ℝ≥0 := ⟨δ+2*K*δ,by positivity⟩
  have hzero (z : P × ℝ) (hz : z ∈ D) : |f (z,0)| ≤ (2*δ)/2 := by
    have hb : |f (z,0)| ≤ δ := by
      calc
        _ ≤ ‖conj (Tβ z.2)*(Γ (z.1,z.2)-β z.2)‖ := by
          simpa only [f,add_zero] using
            (Complex.abs_re_le_norm (conj (Tβ z.2)*(Γ (z.1,z.2)-β z.2)))
        _ = ‖Γ (z.1,z.2)-β z.2‖ := by rw [norm_mul,Complex.norm_conj,huβ,one_mul]
        _ ≤ δ := hposition z.1 hz.1 z.2
    linarith only [hb]
  have hd (z : P × ℝ) (hz : z ∈ D) (x : ℝ) (hx : |x| ≤ 2*δ) :
      |1-deriv (fun y => f (z,y)) x| ≤ (c:ℝ) := by
    rw [(hdf z.1 hz.1 z.2 x).deriv]
    apply (hdclose z.1 hz.1 z.2 x).trans
    change δ+K*|x| ≤ δ+2*K*δ
    calc
      _ ≤ δ+K*(2*δ) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hx hK)
      _ = _ := by ring
  obtain ⟨ξ,hξsmooth,hξ,huniq⟩ := uniform_scalar_implicit_root (∞ : ℕ∞ω) (by simp)
    D hD univ isOpen_univ f hf (2*δ) (by positivity) (subset_univ _) c hsmall hzero hd
  let χ : P × ℝ → ℝ := fun z => z.2+ξ z
  let C : P × ℝ → ℂ := fun z => conj (Tβ z.2)*(Γ (z.1,χ z)-β z.2)
  let H : P × ℝ → ℝ := fun z => (C z).im
  have hχsmooth : ContDiffOn ℝ ∞ χ D := contDiff_snd.contDiffOn.add hξsmooth
  have hCsmooth : ContDiffOn ℝ ∞ C D :=
    (Complex.conjCLE.contDiff.comp (hTsmooth.comp contDiff_snd)).contDiffOn.mul
      ((hΓsmooth.comp (contDiff_fst.contDiffOn.prodMk hχsmooth)
        (fun z hz => ⟨hz.1,mem_univ _⟩)).sub (hβsmooth.comp contDiff_snd).contDiffOn)
  have hHsmooth : ContDiffOn ℝ ∞ H D := Complex.imCLM.contDiff.comp_contDiffOn hCsmooth
  have hre (p : P) (hp : p ∈ U) (s : ℝ) : (C (p,s)).re = 0 :=
    (hξ (p,s) ⟨hp,mem_univ s⟩).2.1
  have hgraph (p : P) (hp : p ∈ U) (s : ℝ) :
      Γ (p,χ (p,s))-β s = I*(H (p,s):ℂ)*Tβ s := by
    have hC : C (p,s) = I*(H (p,s):ℂ) := by
      apply Complex.ext
      · simpa only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
          Complex.ofReal_im,zero_mul,mul_zero,sub_zero] using hre p hp s
      · simp [H,Complex.mul_im]
    calc
      _ = Tβ s*C (p,s) := by dsimp only [C]; rw [← mul_assoc,mul_comm (Tβ s),hself,one_mul]
      _ = I*(H (p,s):ℂ)*Tβ s := by rw [hC]; ring
  refine ⟨χ,H,hχsmooth,hHsmooth,?_⟩
  intro p hp
  have hΓperiod (s : ℝ) : Γ (p,s+L)=Γ (p,s) := hΓper p hp s
  have hξper (s : ℝ) : ξ (p,s+L) = ξ (p,s) := by
    have heq : f ((p,s+L),ξ (p,s)) = f ((p,s),ξ (p,s)) := by
      dsimp only [f]
      rw [hTper s,hβper s,show (s+L)+ξ (p,s) = (s+ξ (p,s))+L by ring,
        hΓperiod (s+ξ (p,s))]
    exact (huniq (p,s+L) ⟨hp,mem_univ _⟩ (ξ (p,s))
      (hξ (p,s) ⟨hp,mem_univ _⟩).1.le
      (heq.trans (hξ (p,s) ⟨hp,mem_univ _⟩).2.1)).symm
  have hχper (s : ℝ) : χ (p,s+L) = χ (p,s)+L := by dsimp only [χ]; rw [hξper]; ring
  have hHper : Function.Periodic (fun s => H (p,s)) L := by
    intro s
    dsimp only [H,C]
    rw [hTper,hχper,hΓperiod,hβper]
  refine ⟨?_,hHper,?_⟩
  · intro s
    dsimp only [χ]
    rw [hξper]
    ring
  intro s
  have hχAt : ContDiffAt ℝ ∞ (fun x => χ (p,x)) s :=
    (hχsmooth.contDiffAt (hD.mem_nhds ⟨hp,mem_univ s⟩)).comp s
      (contDiffAt_const.prodMk contDiffAt_id)
  have hχd := (hχAt.differentiableAt (by simp)).hasDerivAt
  have hχsmall : |χ (p,s)-s| ≤ 2*δ := by
    simpa [χ] using (hξ (p,s) ⟨hp,mem_univ s⟩).1.le
  have hχresidual : |χ (p,s)-s| ≤ 2*|(conj (Tβ s)*(Γ (p,s)-β s)).re| := by
    simpa only [χ,add_sub_cancel_left,f,add_zero] using
      (hξ (p,s) ⟨hp,mem_univ s⟩).2.2
  have hv : 0 ≤ v := (norm_nonneg (V (p,s))).trans (hspeed p hp s)
  have hdistance : ‖Γ (p,χ (p,s))-β s‖ ≤ δ+2*v*δ := by
    calc
      _ ≤ ‖Γ (p,χ (p,s))-Γ (p,s)‖+‖Γ (p,s)-β s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ v*|χ (p,s)-s|+δ := add_le_add (hΓlip p hp s (χ (p,s))) (hposition p hp s)
      _ ≤ v*(2*δ)+δ := add_le_add (mul_le_mul_of_nonneg_left hχsmall hv) le_rfl
      _ = _ := by ring
  have hHsmall : |H (p,s)| ≤ δ+2*v*δ := by
    calc
      _ ≤ ‖C (p,s)‖ := Complex.abs_im_le_norm _
      _ = ‖Γ (p,χ (p,s))-β s‖ := by dsimp only [C]; rw [norm_mul,Complex.norm_conj,huβ,one_mul]
      _ ≤ _ := hdistance
  have hκH : |κ s*H (p,s)| ≤ K*(δ+2*v*δ) := by
    rw [abs_mul]
    exact mul_le_mul (hcurvature s) hHsmall (abs_nonneg _) hK
  have hA : 0 < 1-κ s*H (p,s) := by
    have hh := (le_abs_self (κ s*H (p,s))).trans_lt (hκH.trans_lt hregular)
    linarith only [hh]
  let W := conj (Tβ s)*V (p,χ (p,s))
  let d := W.re
  have hdclose' : |1-d| ≤ (c:ℝ) := by
    have hc := hdclose p hp s (ξ (p,s))
    apply hc.trans
    change δ+K*|ξ (p,s)| ≤ δ+2*K*δ
    calc
      _ ≤ δ+K*(2*δ) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hξ (p,s) ⟨hp,mem_univ s⟩).1.le hK)
      _ = _ := by ring
  have hdpos : 0 < d := by
    have hb := abs_le.mp hdclose'
    change (c:ℝ) < 1/2 at hsmall
    linarith
  have hraw := (hTβ s).star.mul (((hΓ p hp (χ (p,s))).scomp s hχd).sub (hβ s))
  have hraw' : HasDerivAt (fun x => C (p,x))
      (conj (I*(κ s:ℂ)*Tβ s)*(Γ (p,χ (p,s))-β s)+
        conj (Tβ s)*(((deriv (fun x => χ (p,x)) s:ℝ):ℂ)*V (p,χ (p,s))-Tβ s)) s := by
    simpa only [Complex.star_def,real_smul] using! hraw
  have hnice : HasDerivAt (fun x => C (p,x))
      (((κ s*H (p,s):ℝ):ℂ)+((deriv (fun x => χ (p,x)) s:ℝ):ℂ)*W-1) s := by
    apply hraw'.congr_deriv
    simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]
    rw [hgraph p hp s]
    calc
      _ = (κ s:ℂ)*(H (p,s):ℂ)*(conj (Tβ s)*Tβ s)+
          ((deriv (fun x => χ (p,x)) s:ℝ):ℂ)*W-conj (Tβ s)*Tβ s := by
        dsimp only [W]
        ring_nf
        rw [Complex.I_sq]
        ring
      _ = _ := by rw [hself]; push_cast; ring
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hnice
  have himag := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hnice
  simp only [Function.comp_def,Complex.reCLM_apply] at hreal
  simp only [Function.comp_def,Complex.imCLM_apply] at himag
  have hreEq : (fun x => (C (p,x)).re) = fun _ => (0:ℝ) := funext (hre p hp)
  rw [hreEq] at hreal
  have hz := hreal.unique (hasDerivAt_const s (0:ℝ))
  have hχeq : κ s*H (p,s)+deriv (fun x => χ (p,x)) s*d-1 = 0 := by
    simpa only [Complex.add_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,zero_mul,sub_zero,Complex.one_re,d] using hz
  have hχformula : deriv (fun x => χ (p,x)) s = (1-κ s*H (p,s))/d :=
    (eq_div_iff hdpos.ne').mpr (by linarith only [hχeq])
  have hχpos : 0 < deriv (fun x => χ (p,x)) s := by rw [hχformula]; exact div_pos hA hdpos
  have hHderiv : HasDerivAt (fun x => H (p,x))
      (deriv (fun x => χ (p,x)) s*W.im) s := by
    apply himag.congr_deriv
    simp only [Complex.add_im,Complex.sub_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,zero_mul,add_zero,zero_add,Complex.one_im,sub_zero]
  exact ⟨(sub_eq_iff_eq_add.mp (hgraph p hp s)).trans (add_comm _ _),
    hχresidual,hHsmall,hA,hχd.congr_deriv hχformula,hχpos,hHderiv⟩

end Lemniscate
