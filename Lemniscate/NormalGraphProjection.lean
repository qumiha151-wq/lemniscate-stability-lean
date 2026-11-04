import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Local normal projection of a nearby parametrized curve onto a smooth
unit-speed reference curve.  Uniqueness is only in a short parameter
interval.  It does not require the reference curve to be embedded.

-/
noncomputable section
namespace Lemniscate
open Complex Filter Set Function
open scoped Topology ContDiff ComplexConjugate NNReal

private theorem scalar_map_invertible (d : ℝ) (hd : d ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ d).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ d⁻¹)
  · ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    field_simp
  · ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    field_simp

private theorem scalar_projection_root
    (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (r : ℝ) (hr : 0 < r) (c : ℝ≥0) (hc : (c:ℝ) < 1/2)
    (hzero : ∀ s, |f (s,0)| ≤ r/2)
    (hderiv : ∀ s x, |x| ≤ r →
      |1-deriv (fun y => f (s,y)) x| ≤ c) :
    ∃ ξ : ℝ → ℝ, ContDiff ℝ ∞ ξ ∧
      (∀ s, |ξ s| < r ∧ f (s,ξ s) = 0) ∧
      ∀ s x, |x| ≤ r → f (s,x) = 0 → x = ξ s := by
  let F : ℝ → ℝ → ℝ := fun s x => x-f (s,x)
  have hp (s x : ℝ) : HasDerivAt (fun y => f (s,y))
      (deriv (fun y => f (s,y)) x) x :=
    ((hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x).hasDerivAt
  have hFd (s x : ℝ) : HasDerivAt (F s)
      (1-deriv (fun y => f (s,y)) x) x := (hasDerivAt_id x).sub (hp s x)
  let Ball := Metric.closedBall (0:ℝ) r
  have hzeroBall : (0:ℝ) ∈ Ball := by simp [Ball,hr.le]
  have hLip (s : ℝ) : LipschitzOnWith c (F s) Ball := by
    apply (convex_closedBall (0:ℝ) r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (hFd s x).hasDerivWithinAt)
    intro x hx
    have hx' : |x| ≤ r := by simpa [Ball,Real.dist_eq] using hx
    have hb : ‖1-deriv (fun y => f (s,y)) x‖ ≤ (c:ℝ) := by
      simpa only [Real.norm_eq_abs] using hderiv s x hx'
    exact_mod_cast hb
  have hstrict (s x : ℝ) (hx : x ∈ Ball) : |F s x| < r := by
    have hx' : |x| ≤ r := by simpa [Ball,Real.dist_eq] using hx
    have hl : |F s x-F s 0| ≤ (c:ℝ)*|x| := by
      simpa only [Real.dist_eq,sub_zero] using (hLip s).dist_le_mul x hx 0 hzeroBall
    have hz : |F s 0| ≤ r/2 := by simpa [F] using hzero s
    have ht : |F s x| ≤ |F s x-F s 0|+|F s 0| := by
      simpa only [Real.norm_eq_abs] using norm_le_norm_sub_add (F s x) (F s 0)
    have hc0 : (0:ℝ) ≤ c := c.2
    have hcr := mul_lt_mul_of_pos_right hc hr
    have hcx := mul_le_mul_of_nonneg_left hx' hc0
    linarith
  let G : ℝ → Ball → Ball := fun s x =>
    ⟨F s x,by simpa [Ball,Real.dist_eq] using (hstrict s x x.2).le⟩
  have hG (s : ℝ) : ContractingWith c (G s) := by
    refine ⟨by exact_mod_cast (hc.trans (by norm_num : (1/2:ℝ) < 1)),?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hLip s).dist_le_mul x x.2 y y.2
  letI : Nonempty Ball := ⟨⟨0,hzeroBall⟩⟩
  let ξ : ℝ → ℝ := fun s => ((hG s).fixedPoint (G s)).1
  have hfix (s : ℝ) : F s (ξ s) = ξ s :=
    congrArg Subtype.val (hG s).fixedPoint_isFixedPt
  have hξ (s : ℝ) : |ξ s| < r ∧ f (s,ξ s) = 0 := by
    have hb := ((hG s).fixedPoint (G s)).2
    have hs := hstrict s (ξ s) hb
    rw [hfix s] at hs
    exact ⟨hs,by have heq := hfix s; dsimp only [F] at heq; linarith⟩
  have huniq (s x : ℝ) (hx : |x| ≤ r) (heq : f (s,x) = 0) : x = ξ s := by
    let y : Ball := ⟨x,by simpa [Ball,Real.dist_eq] using hx⟩
    have hy : IsFixedPt (G s) y := by
      apply Subtype.ext
      change x-f (s,x) = x
      rw [heq,sub_zero]
    exact congrArg Subtype.val ((hG s).fixedPoint_unique hy)
  refine ⟨ξ,?_,hξ,huniq⟩
  apply contDiff_iff_contDiffAt.mpr
  intro s
  let d := deriv (fun y => f (s,y)) (ξ s)
  have hd : d ≠ 0 := by
    have hb := hderiv s (ξ s) (hξ s).1.le
    intro hz
    change d = 0 at hz
    change |1-d| ≤ (c:ℝ) at hb
    rw [hz,sub_zero,abs_one] at hb
    linarith
  have hpartial : fderiv ℝ f (s,ξ s) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ d := by
    exact ((hp s (ξ s)).hasFDerivAt.unique
      ((hf.differentiable (by simp) (s,ξ s)).hasFDerivAt.comp (ξ s)
        (hasFDerivAt_prodMk_right s (ξ s)))).symm
  have hinv : (fderiv ℝ f (s,ξ s) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hpartial]
    exact scalar_map_invertible d hd
  let g := (hf.contDiffAt (x := (s,ξ s))).implicitFunction (by simp) hinv
  have hg : ContDiffAt ℝ ∞ g s :=
    (hf.contDiffAt (x := (s,ξ s))).contDiffAt_implicitFunction (by simp) hinv
  have hgself : g s = ξ s :=
    (hf.contDiffAt (x := (s,ξ s))).implicitFunction_apply_self (by simp) hinv
  have hgin : ∀ᶠ t in 𝓝 s, |g t| < r :=
    hg.continuousAt.abs.eventually_lt continuousAt_const (by rw [hgself]; exact (hξ s).1)
  have hgeq := (hf.contDiffAt (x := (s,ξ s))).eventually_apply_implicitFunction (by simp) hinv
  have hevent : ξ =ᶠ[𝓝 s] g := by
    filter_upwards [hgin,hgeq] with t ht he
    exact (huniq t (g t) ht.le (he.trans (hξ s).2)).symm
  exact hg.congr_of_eventuallyEq hevent

/-- Sufficient C1 proximity of two smooth unit-speed periodic curves gives
a smooth orientation-preserving change of parameter and a small normal
height. The reference curve may have self-intersections. -/
theorem periodic_normal_graph_projection
    (γ β Tγ Tβ : ℝ → ℂ) (κ : ℝ → ℝ) (L δ K : ℝ)
    (hγsmooth : ContDiff ℝ ∞ γ) (hβsmooth : ContDiff ℝ ∞ β)
    (hγ : ∀ s, HasDerivAt γ (Tγ s) s) (hβ : ∀ s, HasDerivAt β (Tβ s) s)
    (hTβ : ∀ s, HasDerivAt Tβ (I*(κ s:ℂ)*Tβ s) s)
    (huγ : ∀ s, ‖Tγ s‖ = 1) (huβ : ∀ s, ‖Tβ s‖ = 1)
    (hγper : Function.Periodic γ L) (hβper : Function.Periodic β L)
    (hδ : 0 < δ) (hK : 0 ≤ K) (hsmall : δ+2*K*δ < 1/2)
    (hposition : ∀ s, ‖γ s-β s‖ ≤ δ)
    (htangent : ∀ s, ‖Tγ s-Tβ s‖ ≤ δ) (hcurvature : ∀ s, |κ s| ≤ K) :
    ∃ χ h : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ ContDiff ℝ ∞ h ∧
      Function.Periodic (fun s => χ s-s) L ∧ Function.Periodic h L ∧
      ∀ s,
        γ (χ s) = β s+I*(h s:ℂ)*Tβ s ∧
        |χ s-s| ≤ 2*δ ∧ |h s| ≤ 3*δ ∧
        |deriv h s| ≤ 4*(δ+2*K*δ) ∧
        HasDerivAt χ ((1-κ s*h s)/(conj (Tβ s)*Tγ (χ s)).re) s ∧
        (1/4:ℝ) ≤ deriv χ s ∧ deriv χ s ≤ 4 := by
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
  have hγlip (a b : ℝ) : ‖γ b-γ a‖ ≤ |b-a| := by
    simpa only [one_mul,Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := (Set.univ : Set ℝ)) (C := (1:ℝ))
        (fun x _ => (hγ x).hasDerivWithinAt)
        (fun x _ => (huγ x).le) convex_univ (mem_univ a) (mem_univ b)
  have hTlip (a b : ℝ) : ‖Tβ b-Tβ a‖ ≤ K*|b-a| := by
    have hb (x : ℝ) : ‖I*(κ x:ℂ)*Tβ x‖ ≤ K := by
      simpa only [norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
        huβ,mul_one,one_mul] using hcurvature x
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := (Set.univ : Set ℝ)) (C := K)
        (fun x _ => (hTβ x).hasDerivWithinAt) (fun x _ => hb x)
        convex_univ (mem_univ a) (mem_univ b)
  have htshift (s x : ℝ) : ‖Tγ (s+x)-Tβ s‖ ≤ δ+K*|x| := by
    calc
      _ = ‖(Tγ (s+x)-Tβ (s+x))+(Tβ (s+x)-Tβ s)‖ := by congr 1; ring
      _ ≤ ‖Tγ (s+x)-Tβ (s+x)‖+‖Tβ (s+x)-Tβ s‖ := norm_add_le _ _
      _ ≤ δ+K*|x| := add_le_add (htangent (s+x)) (by simpa using hTlip s (s+x))
  let f : ℝ × ℝ → ℝ := fun z => (conj (Tβ z.1)*(γ (z.1+z.2)-β z.1)).re
  have hf : ContDiff ℝ ∞ f := by
    exact Complex.reCLM.contDiff.comp
      ((Complex.conjCLE.contDiff.comp (hTsmooth.comp contDiff_fst)).mul
        ((hγsmooth.comp (contDiff_fst.add contDiff_snd)).sub
          (hβsmooth.comp contDiff_fst)))
  have hdf (s x : ℝ) : HasDerivAt (fun y => f (s,y))
      (conj (Tβ s)*Tγ (s+x)).re x := by
    have hd := (((hγ (s+x)).scomp x ((hasDerivAt_id x).const_add s)).sub_const (β s)).const_mul
      (conj (Tβ s))
    simpa only [one_smul] using! Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  have hdclose (s x : ℝ) : |1-(conj (Tβ s)*Tγ (s+x)).re| ≤ δ+K*|x| := by
    have heq : 1-(conj (Tβ s)*Tγ (s+x)).re =
        (conj (Tβ s)*(Tβ s-Tγ (s+x))).re := by
      rw [mul_sub,hself,Complex.sub_re,Complex.one_re]
    rw [heq]
    calc
      _ ≤ ‖conj (Tβ s)*(Tβ s-Tγ (s+x))‖ := Complex.abs_re_le_norm _
      _ = ‖Tγ (s+x)-Tβ s‖ := by rw [norm_mul,Complex.norm_conj,huβ,one_mul,norm_sub_rev]
      _ ≤ _ := htshift s x
  let c : ℝ≥0 := ⟨δ+2*K*δ,by positivity⟩
  have hzero (s : ℝ) : |f (s,0)| ≤ (2*δ)/2 := by
    have hb : |f (s,0)| ≤ δ := by
      calc
        _ ≤ ‖conj (Tβ s)*(γ s-β s)‖ := by
          simpa only [f,add_zero] using
            (Complex.abs_re_le_norm (conj (Tβ s)*(γ s-β s)))
        _ = ‖γ s-β s‖ := by rw [norm_mul,Complex.norm_conj,huβ,one_mul]
        _ ≤ δ := hposition s
    linarith
  have hd (s x : ℝ) (hx : |x| ≤ 2*δ) :
      |1-deriv (fun y => f (s,y)) x| ≤ (c:ℝ) := by
    rw [(hdf s x).deriv]
    apply (hdclose s x).trans
    change δ+K*|x| ≤ δ+2*K*δ
    calc
      _ ≤ δ+K*(2*δ) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hx hK)
      _ = _ := by ring
  obtain ⟨ξ,hξsmooth,hξ,huniq⟩ := scalar_projection_root f hf (2*δ)
    (by positivity) c hsmall hzero hd
  let χ : ℝ → ℝ := fun s => s+ξ s
  let H : ℝ → ℂ := fun s => conj (Tβ s)*(γ (χ s)-β s)
  let h : ℝ → ℝ := fun s => (H s).im
  have hχsmooth : ContDiff ℝ ∞ χ := contDiff_id.add hξsmooth
  have hHsmooth : ContDiff ℝ ∞ H :=
    (Complex.conjCLE.contDiff.comp hTsmooth).mul ((hγsmooth.comp hχsmooth).sub hβsmooth)
  have hhsmooth : ContDiff ℝ ∞ h := Complex.imCLM.contDiff.comp hHsmooth
  have hre (s : ℝ) : (H s).re = 0 := (hξ s).2
  have hgraph (s : ℝ) : γ (χ s)-β s = I*(h s:ℂ)*Tβ s := by
    have hH : H s = I*(h s:ℂ) := by
      apply Complex.ext
      · simpa only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
          Complex.ofReal_im,zero_mul,mul_zero,sub_zero] using hre s
      · simp [h,Complex.mul_im]
    calc
      _ = Tβ s*H s := by dsimp only [H]; rw [← mul_assoc,mul_comm (Tβ s),hself,one_mul]
      _ = I*(h s:ℂ)*Tβ s := by rw [hH]; ring
  have hξper (s : ℝ) : ξ (s+L) = ξ s := by
    have heq : f (s+L,ξ s) = f (s,ξ s) := by
      dsimp only [f]
      rw [hTper s,hβper s,show (s+L)+ξ s = (s+ξ s)+L by ring,hγper (s+ξ s)]
    exact (huniq (s+L) (ξ s) (hξ s).1.le (heq.trans (hξ s).2)).symm
  have hχper (s : ℝ) : χ (s+L) = χ s+L := by dsimp only [χ]; rw [hξper]; ring
  have hhper : Function.Periodic h L := by
    intro s
    dsimp only [h,H]
    rw [hTper,hχper,hγper,hβper]
  refine ⟨χ,h,hχsmooth,hhsmooth,?_,hhper,?_⟩
  · intro s
    dsimp only [χ]
    rw [hξper]
    ring
  intro s
  have hχd := (hχsmooth.differentiable (by simp) s).hasDerivAt
  have hχsmall : |χ s-s| ≤ 2*δ := by simpa [χ] using (hξ s).1.le
  have hdistance : ‖γ (χ s)-β s‖ ≤ 3*δ := by
    calc
      _ ≤ ‖γ (χ s)-γ s‖+‖γ s-β s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ |χ s-s|+δ := add_le_add (hγlip s (χ s)) (hposition s)
      _ ≤ 3*δ := by linarith
  have hhsmall : |h s| ≤ 3*δ := by
    calc
      _ ≤ ‖H s‖ := Complex.abs_im_le_norm _
      _ = ‖γ (χ s)-β s‖ := by dsimp only [H]; rw [norm_mul,Complex.norm_conj,huβ,one_mul]
      _ ≤ _ := hdistance
  let W := conj (Tβ s)*Tγ (χ s)
  let d := W.re
  have hdclose' : |1-d| ≤ (c:ℝ) := by
    have hc := hdclose s (ξ s)
    apply hc.trans
    change δ+K*|ξ s| ≤ δ+2*K*δ
    calc
      _ ≤ δ+K*(2*δ) := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hξ s).1.le hK)
      _ = _ := by ring
  have hdpos : 1/2 < d := by have hc := abs_le.mp hdclose'; change (c:ℝ) < 1/2 at hsmall; linarith
  have hdle : d ≤ 1 := by
    calc
      _ ≤ ‖W‖ := Complex.re_le_norm _
      _ = 1 := by dsimp only [W]; rw [norm_mul,Complex.norm_conj,huβ,huγ,one_mul]
  have hraw := (hTβ s).star.mul (((hγ (χ s)).scomp s hχd).sub (hβ s))
  have hraw' : HasDerivAt H
      (conj (I*(κ s:ℂ)*Tβ s)*(γ (χ s)-β s)+
        conj (Tβ s)*(((deriv χ s:ℝ):ℂ)*Tγ (χ s)-Tβ s)) s := by
    simpa only [Complex.star_def,real_smul] using! hraw
  have hnice : HasDerivAt H
      (((κ s*h s:ℝ):ℂ)+((deriv χ s:ℝ):ℂ)*W-1) s := by
    apply hraw'.congr_deriv
    simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]
    rw [hgraph]
    calc
      _ = (κ s:ℂ)*(h s:ℂ)*(conj (Tβ s)*Tβ s)+
          ((deriv χ s:ℝ):ℂ)*W-conj (Tβ s)*Tβ s := by
        dsimp only [W]
        ring_nf
        rw [Complex.I_sq]
        ring
      _ = _ := by rw [hself]; push_cast; ring
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hnice
  have himag := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hnice
  simp only [Function.comp_def,Complex.reCLM_apply] at hreal
  simp only [Function.comp_def,Complex.imCLM_apply] at himag
  have hreEq : (fun t => (H t).re) = fun _ => (0:ℝ) := funext hre
  rw [hreEq] at hreal
  have hz := hreal.unique (hasDerivAt_const s (0:ℝ))
  have hχeq : κ s*h s+deriv χ s*d-1 = 0 := by
    simpa only [Complex.add_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,zero_mul,sub_zero,Complex.one_re,d] using hz
  have hheq : deriv h s = deriv χ s*W.im := by
    simpa only [h,Complex.add_im,Complex.sub_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,zero_mul,add_zero,zero_add,Complex.one_im,sub_zero] using himag.deriv
  have hκh : |κ s*h s| ≤ 3*K*δ := by
    rw [abs_mul]
    exact (mul_le_mul (hcurvature s) hhsmall (abs_nonneg _) hK).trans_eq (by ring)
  have hKd : K*δ < 1/4 := by nlinarith [hK]
  have hprod : (1/4:ℝ) < deriv χ s*d := by
    nlinarith only [hχeq,(abs_le.mp hκh).2,hKd]
  have hχpos : 0 < deriv χ s := by
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
      (le_of_lt (lt_trans (by norm_num : (0:ℝ) < 1/2) hdpos))
    linarith
  have hχlower : (1/4:ℝ) ≤ deriv χ s := by
    have hm := mul_nonneg hχpos.le (sub_nonneg.mpr hdle)
    nlinarith only [hm,hprod]
  have hχupper : deriv χ s ≤ 4 := by
    have hprod' : deriv χ s*d < 7/4 := by
      nlinarith only [hχeq,(abs_le.mp hκh).1,hKd]
    have hm := mul_lt_mul_of_pos_left hdpos hχpos
    linarith
  have hχformula : deriv χ s = (1-κ s*h s)/d :=
    (eq_div_iff (ne_of_gt (lt_trans (by norm_num : (0:ℝ) < 1/2) hdpos))).mpr (by linarith)
  have hWim : |W.im| ≤ (c:ℝ) := by
    have hi : W.im = (conj (Tβ s)*(Tγ (χ s)-Tβ s)).im := by
      dsimp only [W]
      rw [mul_sub,hself,Complex.sub_im,Complex.one_im,sub_zero]
    rw [hi]
    calc
      _ ≤ ‖conj (Tβ s)*(Tγ (χ s)-Tβ s)‖ := Complex.abs_im_le_norm _
      _ = ‖Tγ (χ s)-Tβ s‖ := by rw [norm_mul,Complex.norm_conj,huβ,one_mul]
      _ ≤ δ+K*|ξ s| := htshift s (ξ s)
      _ ≤ _ := by
        change δ+K*|ξ s| ≤ δ+2*K*δ
        calc
          _ ≤ δ+K*(2*δ) := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hξ s).1.le hK)
          _ = _ := by ring
  have hheightDerivative : |deriv h s| ≤ 4*(δ+2*K*δ) := by
    rw [hheq,abs_mul,abs_of_nonneg (by linarith : 0 ≤ deriv χ s)]
    exact mul_le_mul hχupper hWim (abs_nonneg _) (by norm_num)
  refine ⟨(sub_eq_iff_eq_add.mp (hgraph s)).trans (add_comm _ _),
    hχsmall,hhsmall,hheightDerivative,?_,hχlower,hχupper⟩
  exact hχd.congr_deriv hχformula

end Lemniscate
