import Lemniscate.ParametricNormalGraphProjection

/-! The unit-speed projection bounds are a numerical specialization of
jointly smooth normal projection. The implicit-root and geometric
velocity identities are proved only in the general projection theorem. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff ComplexConjugate

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
  have hKd : K*δ < 1/4 := by nlinarith only [hsmall,hδ]
  have hregular : K*(δ+2*(1:ℝ)*δ) < 1 := by nlinarith only [hKd]
  obtain ⟨Χ,Η,hΧ,hΗ,hdata⟩ := parametric_normal_graph_projection
    (P:=ℝ) univ isOpen_univ (fun z : ℝ × ℝ => γ z.2)
      (fun z : ℝ × ℝ => Tγ z.2) β Tβ κ L δ K 1
      (hγsmooth.comp contDiff_snd).contDiffOn hβsmooth
      (fun _ _ s => hγ s) hβ hTβ (fun _ _ s => (huγ s).le) huβ
      (fun _ _ => hγper) hβper hδ hK hsmall hregular
      (fun _ _ => hposition) (fun _ _ => htangent) hcurvature
  let χ : ℝ → ℝ := fun s => Χ (0,s)
  let h : ℝ → ℝ := fun s => Η (0,s)
  have hχsmooth : ContDiff ℝ ∞ χ := by
    apply contDiffOn_univ.mp
    exact hΧ.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun s _ => ⟨mem_univ (0:ℝ),mem_univ s⟩)
  have hhsmooth : ContDiff ℝ ∞ h := by
    apply contDiffOn_univ.mp
    exact hΗ.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun s _ => ⟨mem_univ (0:ℝ),mem_univ s⟩)
  have hTlip (a b : ℝ) : ‖Tβ b-Tβ a‖ ≤ K*|b-a| := by
    have hb (x : ℝ) : ‖I*(κ x:ℂ)*Tβ x‖ ≤ K := by
      simpa only [norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
        huβ,mul_one,one_mul] using hcurvature x
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := (univ : Set ℝ)) (C := K)
        (fun x _ => (hTβ x).hasDerivWithinAt) (fun x _ => hb x)
        convex_univ (mem_univ a) (mem_univ b)
  have hd := hdata (0:ℝ) (mem_univ 0)
  refine ⟨χ,h,hχsmooth,hhsmooth,hd.1,hd.2.1,?_⟩
  intro s
  have hs := hd.2.2 s
  have hχsmall : |χ s-s| ≤ 2*δ := by
    calc
      _ ≤ 2*|(conj (Tβ s)*(γ s-β s)).re| := hs.2.1
      _ ≤ 2*‖conj (Tβ s)*(γ s-β s)‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
      _ = 2*‖γ s-β s‖ := by rw [norm_mul,Complex.norm_conj,huβ,one_mul]
      _ ≤ 2*δ := mul_le_mul_of_nonneg_left (hposition s) (by norm_num)
  have hhsmall : |h s| ≤ 3*δ := by
    calc
      _ ≤ δ+2*(1:ℝ)*δ := hs.2.2.1
      _ = 3*δ := by ring
  have hχd : HasDerivAt χ ((1-κ s*h s)/(conj (Tβ s)*Tγ (χ s)).re) s :=
    hs.2.2.2.2.1
  have hχpos : 0<deriv χ s := hs.2.2.2.2.2.1
  have hheq : deriv h s=deriv χ s*(conj (Tβ s)*Tγ (χ s)).im :=
    hs.2.2.2.2.2.2.deriv
  let c : ℝ := δ+2*K*δ
  let W : ℂ := conj (Tβ s)*Tγ (χ s)
  let d : ℝ := W.re
  have hshift : ‖Tγ (χ s)-Tβ s‖ ≤ c := by
    calc
      _ ≤ ‖Tγ (χ s)-Tβ (χ s)‖+‖Tβ (χ s)-Tβ s‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ+K*|χ s-s| := add_le_add (htangent (χ s)) (hTlip s (χ s))
      _ ≤ δ+K*(2*δ) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hχsmall hK)
      _ = c := by dsimp only [c]; ring
  have hself : conj (Tβ s)*Tβ s=1 := by rw [Complex.conj_mul',huβ]; simp
  have hWdiff : W-1=conj (Tβ s)*(Tγ (χ s)-Tβ s) := by
    rw [mul_sub,hself]
  have hWclose : ‖W-1‖ ≤ c := by
    rw [hWdiff,norm_mul,Complex.norm_conj,huβ,one_mul]
    exact hshift
  have hdclose : |1-d| ≤ c := by
    calc
      _ = |d-1| := abs_sub_comm _ _
      _ ≤ ‖W-1‖ := by
        simpa only [d,Complex.sub_re,Complex.one_re] using Complex.abs_re_le_norm (W-1)
      _ ≤ c := hWclose
  have hdpos : 1/2<d := by
    have hb := abs_le.mp hdclose
    change c<1/2 at hsmall
    linarith only [hb.2,hsmall]
  have hdle : d≤1 := by
    calc
      _ ≤ ‖W‖ := Complex.re_le_norm W
      _ = 1 := by dsimp only [W]; rw [norm_mul,Complex.norm_conj,huβ,huγ,one_mul]
  have hχformula : deriv χ s=(1-κ s*h s)/d := hχd.deriv
  have hχeq : κ s*h s+deriv χ s*d-1=0 := by
    have hh := (eq_div_iff (ne_of_gt (lt_trans (by norm_num : (0:ℝ)<1/2) hdpos))).mp hχformula
    linarith only [hh]
  have hκh : |κ s*h s| ≤ 3*K*δ := by
    rw [abs_mul]
    exact (mul_le_mul (hcurvature s) hhsmall (abs_nonneg _) hK).trans_eq (by ring)
  have hprod : (1/4:ℝ)<deriv χ s*d := by
    nlinarith only [hχeq,(abs_le.mp hκh).2,hKd]
  have hχlower : (1/4:ℝ)≤deriv χ s := by
    have hm := mul_nonneg hχpos.le (sub_nonneg.mpr hdle)
    nlinarith only [hm,hprod]
  have hχupper : deriv χ s≤4 := by
    have hprod' : deriv χ s*d<7/4 := by
      nlinarith only [hχeq,(abs_le.mp hκh).1,hKd]
    have hm := mul_lt_mul_of_pos_left hdpos hχpos
    linarith only [hprod',hm]
  have hWim : |W.im|≤c := by
    calc
      _ = |(W-1).im| := by simp only [Complex.sub_im,Complex.one_im,sub_zero]
      _ ≤ ‖W-1‖ := Complex.abs_im_le_norm _
      _ ≤ c := hWclose
  have hheightDerivative : |deriv h s|≤4*(δ+2*K*δ) := by
    rw [hheq,abs_mul,abs_of_nonneg hχpos.le]
    exact mul_le_mul hχupper hWim (abs_nonneg _) (by norm_num)
  exact ⟨hs.1,hχsmall,hhsmall,hheightDerivative,hχd,hχlower,hχupper⟩

end Lemniscate
