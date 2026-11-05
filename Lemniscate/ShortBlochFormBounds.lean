import Lemniscate.PeriodicBlochGreen
import Lemniscate.ShortFourierEnclosure

/-! Low-order form bounds for the actual differential operator. A single
integration by parts in the cubic term avoids an H4 approximation error. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem short_circle_frequency_bounds
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared) :
    ‖circleFrequencyFactor T 1‖ ≤ 17/20 ∧
      ‖circleFrequencyFactor T 1‖^2 ≤ 359/500 := by
  have hk : 0 < 2*Real.pi/T := by have := (Fact.out : 0 < T); positivity
  have hn : ‖circleFrequencyFactor T 1‖ = 2*Real.pi/T := by
    simp only [circleFrequencyFactor, Int.cast_one, mul_one, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, abs_of_pos hk]
  have hu := short_frequency_enclosure.2
  norm_num [shortFrequencyInterval] at hu
  rw [hn]
  constructor
  · nlinarith only [hu,hr,sq_nonneg (2*Real.pi/T-17/20)]
  · linarith only [hu,hr]

theorem short_profile_product_bound (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x) :
    ‖q*p‖ ≤ 4/9 := by
  apply (ContinuousMap.norm_le _ (by norm_num : (0:ℝ) ≤ 4/9)).mpr
  intro x
  obtain ⟨a,ha⟩ := Complex.conj_eq_iff_real.mp (hqreal x)
  obtain ⟨b,hb⟩ := Complex.conj_eq_iff_real.mp (hpreal x)
  have hc := he x
  rw [ha,hb] at hc
  have h : 2*b^2+a^4 = (1:ℝ) := by exact_mod_cast hc
  have hs : 0 ≤ a^2*(a^2-3/5)^2 := mul_nonneg (sq_nonneg a) (sq_nonneg _)
  have heq : 2*(a*b)^2 = a^2-a^6 := by
    have hm := congrArg (fun u : ℝ => a^2*u) h
    nlinarith only [hm]
  have hbnd : (a*b)^2 ≤ (4/9:ℝ)^2 := by
    nlinarith only [heq,hs,sq_nonneg (a^2-17/30)]
  change ‖q x*p x‖ ≤ _
  rw [ha,hb,← Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> nlinarith only [hbnd]

private theorem norm_three_terms (a b c : ℂ) :
    ‖a-b-c‖ ≤ ‖a‖+‖b‖+‖c‖ := by
  have h1 := norm_sub_le a b
  have h2 := norm_sub_le (a-b) c
  linarith only [h1,h2]

private theorem multiply_pairing_bound (h : C(AddCircle T, ℂ))
    (f g : CircleL2 T) :
    ‖inner ℂ g (circleMultiplyL2 T h f)‖ ≤ ‖g‖*‖h‖*‖f‖ := by
  calc
    _ ≤ ‖g‖*‖circleMultiplyL2 T h f‖ := norm_inner_le_norm _ _
    _ ≤ ‖g‖*(‖h‖*‖f‖) := mul_le_mul_of_nonneg_left
      (circle_multiply_l2_norm_le T h f) (norm_nonneg _)
    _ = _ := by ring

theorem short_bloch_one_form_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : ‖h‖ ≤ 1) (hh₁ : ‖h₁‖ ≤ 8/9)
    (hκ : ‖circleFrequencyFactor T 1‖ ≤ 17/20)
    (f g : circleH4Domain T) (V W : ℝ)
    (hf : ‖(f:CircleL2 T)‖ ≤ V)
    (hf₁ : ‖(circleH4Jet T f).first‖ ≤ (17/40:ℝ)*V)
    (hf₂ : ‖(circleH4Jet T f).second‖ ≤ (359/500:ℝ)*V)
    (hg : ‖(g:CircleL2 T)‖ ≤ W)
    (hg₁ : ‖(circleH4Jet T g).first‖ ≤ (17/20:ℝ)*W) :
    ‖inner ℂ (g:CircleL2 T) (circleBlochCoefficient T h h₁ h₂ 1 f)‖ ≤ 70*V*W := by
  have hV : 0 ≤ V := (norm_nonneg _).trans hf
  have hW : 0 ≤ W := (norm_nonneg _).trans hg
  have hthird : inner ℂ (g:CircleL2 T) (circleH4Jet T f).third =
      -inner ℂ (circleH4Jet T g).first (circleH4Jet T f).second := by
    have hb := circle_weak_integration_by_parts T _ _ _ _
      (circleH4Jet T g).hfirst (circleH4Jet T f).hthird
    exact neg_eq_iff_eq_neg.mp hb.symm
  have hd : ‖inner ℂ (g:CircleL2 T) (circleH4Jet T f).third‖ ≤
      ((17/20:ℝ)*W)*((359/500:ℝ)*V) := by
    rw [hthird,norm_neg]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul hg₁ hf₂ (norm_nonneg _) (by positivity))
  have hm : ‖inner ℂ (g:CircleL2 T)
      (circleMultiplyL2 T h (circleH4Jet T f).first)‖ ≤ W*((17/40:ℝ)*V) := by
    apply (multiply_pairing_bound T h _ _).trans
    have hgh := mul_le_mul hg hh (norm_nonneg _) hW
    simpa only [mul_one] using mul_le_mul hgh hf₁ (norm_nonneg _) (by positivity)
  have hm₁ : ‖inner ℂ (g:CircleL2 T) (circleMultiplyL2 T h₁ (f:CircleL2 T))‖ ≤
      W*(8/9:ℝ)*V := by
    apply (multiply_pairing_bound T h₁ _ _).trans
    exact mul_le_mul (mul_le_mul hg hh₁ (norm_nonneg _) hW) hf
      (norm_nonneg _) (by positivity)
  rw [circle_bloch_coefficient_one_apply,inner_smul_right,norm_mul]
  have hraw : ‖inner ℂ (g:CircleL2 T)
      ((-16:ℂ) • (circleH4Jet T f).third-
        (90:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).first-
        (75/2:ℂ) • circleMultiplyL2 T h₁ (f:CircleL2 T))‖ ≤
      (16*(17/20:ℝ)*(359/500)+90*(17/40)+(75/2)*(8/9))*V*W := by
    simp only [inner_sub_right,inner_smul_right]
    have ht := norm_three_terms
      ((-16:ℂ)*inner ℂ (g:CircleL2 T) (circleH4Jet T f).third)
      ((90:ℂ)*inner ℂ (g:CircleL2 T) (circleMultiplyL2 T h (circleH4Jet T f).first))
      ((75/2:ℂ)*inner ℂ (g:CircleL2 T) (circleMultiplyL2 T h₁ (f:CircleL2 T)))
    norm_num only [norm_mul,norm_neg,Complex.norm_ofNat,norm_div] at ht
    nlinarith only [ht,hd,hm,hm₁]
  have hb := mul_le_mul hκ hraw (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 17/20)
  nlinarith only [hb,mul_nonneg hV hW]

theorem short_bloch_two_form_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : ‖h‖ ≤ 1) (hκ : ‖circleFrequencyFactor T 1‖^2 ≤ 359/500)
    (f g : circleH4Domain T) (V W : ℝ)
    (hf : ‖(f:CircleL2 T)‖ ≤ V)
    (hf₂ : ‖(circleH4Jet T f).second‖ ≤ (359/500:ℝ)*V)
    (hg : ‖(g:CircleL2 T)‖ ≤ W) :
    ‖inner ℂ (g:CircleL2 T) (circleBlochCoefficient T h h₁ h₂ 2 f)‖ ≤ 45*V*W := by
  have hV : 0 ≤ V := (norm_nonneg _).trans hf
  have hW : 0 ≤ W := (norm_nonneg _).trans hg
  have hd : ‖inner ℂ (g:CircleL2 T) (circleH4Jet T f).second‖ ≤
      W*((359/500:ℝ)*V) := (norm_inner_le_norm _ _).trans
        (mul_le_mul hg hf₂ (norm_nonneg _) hW)
  have hm : ‖inner ℂ (g:CircleL2 T) (circleMultiplyL2 T h (f:CircleL2 T))‖ ≤ W*V := by
    apply (multiply_pairing_bound T h _ _).trans
    have hgh := mul_le_mul hg hh (norm_nonneg _) hW
    simpa only [mul_one] using mul_le_mul hgh hf (norm_nonneg _) (by positivity)
  rw [circle_bloch_coefficient_two_apply,inner_smul_right,norm_mul,norm_pow]
  have hraw : ‖inner ℂ (g:CircleL2 T)
      ((-24:ℂ) • (circleH4Jet T f).second-(45:ℂ) • circleMultiplyL2 T h (f:CircleL2 T))‖ ≤
      (24*(359/500:ℝ)+45)*V*W := by
    simp only [inner_sub_right,inner_smul_right]
    have ht := norm_sub_le
      ((-24:ℂ)*inner ℂ (g:CircleL2 T) (circleH4Jet T f).second)
      ((45:ℂ)*inner ℂ (g:CircleL2 T) (circleMultiplyL2 T h (f:CircleL2 T)))
    norm_num only [norm_mul,norm_neg,Complex.norm_ofNat] at ht
    nlinarith only [ht,hd,hm]
  have hb := mul_le_mul hκ hraw (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 359/500)
  nlinarith only [hb,mul_nonneg hV hW]

theorem short_bloch_three_form_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hκ : ‖circleFrequencyFactor T 1‖ ≤ 17/20)
    (hκ₂ : ‖circleFrequencyFactor T 1‖^2 ≤ 359/500)
    (f g : circleH4Domain T) (V W : ℝ) (hV : 0 ≤ V)
    (hf₁ : ‖(circleH4Jet T f).first‖ ≤ (17/40:ℝ)*V)
    (hg : ‖(g:CircleL2 T)‖ ≤ W) :
    ‖inner ℂ (g:CircleL2 T) (circleBlochCoefficient T h h₁ h₂ 3 f)‖ ≤ 5*V*W := by
  have hW : 0 ≤ W := (norm_nonneg _).trans hg
  have hd : ‖inner ℂ (g:CircleL2 T) (circleH4Jet T f).first‖ ≤ W*((17/40:ℝ)*V) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hg hf₁ (norm_nonneg _) hW)
  have hk₃ : ‖circleFrequencyFactor T 1‖^3 ≤ (359/500:ℝ)*(17/20) := by
    rw [pow_succ]
    exact mul_le_mul hκ₂ hκ (norm_nonneg _) (by norm_num)
  rw [circle_bloch_coefficient_three_apply,inner_smul_right,inner_smul_right]
  simp only [norm_mul,norm_pow,norm_neg,Complex.norm_ofNat]
  have hb := mul_le_mul hk₃ (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 16))
    (by positivity) (by norm_num : (0:ℝ) ≤ (359/500:ℝ)*(17/20))
  nlinarith only [hb,mul_nonneg hV hW]

theorem short_profile_coefficient_bounds (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x) :
    ‖q^2‖ ≤ 1 ∧ ‖(2:ℂ) • (q*p)‖ ≤ 8/9 ∧ ‖1-(3:ℂ) • (q^4)‖ ≤ 2 := by
  have hpoint (x : AddCircle T) : ‖(q x)^2‖ ≤ 1 ∧ ‖1-3*(q x)^4‖ ≤ 2 := by
    obtain ⟨a,ha⟩ := Complex.conj_eq_iff_real.mp (hqreal x)
    obtain ⟨b,hb⟩ := Complex.conj_eq_iff_real.mp (hpreal x)
    have hc := he x
    rw [ha,hb] at hc
    have h : 2*b^2+a^4 = (1:ℝ) := by exact_mod_cast hc
    have h4 : a^4 ≤ 1 := by nlinarith only [h,sq_nonneg b]
    have h2 : a^2 ≤ 1 := by nlinarith only [h4,sq_nonneg (a^2-1)]
    rw [ha,← Complex.ofReal_pow]
    constructor
    · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg a)]
      exact h2
    · have hr : (1-3*(a:ℂ)^4) = ((1-3*a^4:ℝ):ℂ) := by push_cast; rfl
      rw [hr,Complex.norm_real,Real.norm_eq_abs,abs_le]
      constructor <;> nlinarith only [h4,sq_nonneg (a^2)]
  refine ⟨?_,?_,?_⟩
  · exact (ContinuousMap.norm_le _ (by norm_num : (0:ℝ) ≤ 1)).mpr (fun x => (hpoint x).1)
  · rw [norm_smul]
    norm_num only [Complex.norm_ofNat]
    linarith only [short_profile_product_bound T q p he hqreal hpreal]
  · exact (ContinuousMap.norm_le _ (by norm_num : (0:ℝ) ≤ 2)).mpr (fun x => (hpoint x).2)

theorem short_symmetric_form_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (hhnorm : ‖h‖ ≤ 1) (hh₂norm : ‖h₂‖ ≤ 2)
    (f g : circleH4Domain T) (V W : ℝ)
    (hf : ‖(f:CircleL2 T)‖ ≤ V)
    (hf₁ : ‖(circleH4Jet T f).first‖ ≤ (17/40:ℝ)*V)
    (hf₂ : ‖(circleH4Jet T f).second‖ ≤ (359/500:ℝ)*V)
    (hg : ‖(g:CircleL2 T)‖ ≤ W)
    (hg₁ : ‖(circleH4Jet T g).first‖ ≤ (17/40:ℝ)*W)
    (hg₂ : ‖(circleH4Jet T g).second‖ ≤ (359/500:ℝ)*W) :
    ‖inner ℂ (g:CircleL2 T) (circleH4SymmetricOperator T h h₁ h₂ f)‖ ≤ 60*V*W := by
  have hV : 0 ≤ V := (norm_nonneg _).trans hf
  have hW : 0 ≤ W := (norm_nonneg _).trans hg
  have hfourth : inner ℂ (g:CircleL2 T) (circleH4Jet T f).fourth =
      inner ℂ (circleH4Jet T g).second (circleH4Jet T f).second := by
    have h1 := circle_weak_integration_by_parts T _ _ _ _
      (circleH4Jet T g).hfirst (circleH4Jet T f).hfourth
    have h2 := circle_weak_integration_by_parts T _ _ _ _
      (circleH4Jet T g).hsecond (circleH4Jet T f).hthird
    calc
      _ = -inner ℂ (circleH4Jet T g).first (circleH4Jet T f).third :=
        neg_eq_iff_eq_neg.mp h1.symm
      _ = _ := h2.symm
  have hd := circle_weak_integration_by_parts T _ _ _ _
    (circleH4Jet T g).hfirst
    (circle_real_multiply_weak_deriv T h h₁ hh hreal h₁real _ _ (circleH4Jet T f).hsecond)
  have hdiv : inner ℂ (g:CircleL2 T)
      (circleMultiplyL2 T h₁ (circleH4Jet T f).first+circleMultiplyL2 T h (circleH4Jet T f).second) =
      -inner ℂ (circleH4Jet T g).first (circleMultiplyL2 T h (circleH4Jet T f).first) := by
    rw [add_comm]
    exact neg_eq_iff_eq_neg.mp hd.symm
  have hid : inner ℂ (g:CircleL2 T) (circleH4SymmetricOperator T h h₁ h₂ f) =
      (-4:ℂ)*inner ℂ (circleH4Jet T g).second (circleH4Jet T f).second+
      45*inner ℂ (circleH4Jet T g).first (circleMultiplyL2 T h (circleH4Jet T f).first)-
      42*inner ℂ (g:CircleL2 T) (f:CircleL2 T)+
      (15/4:ℂ)*inner ℂ (g:CircleL2 T) (circleMultiplyL2 T h₂ (f:CircleL2 T)) := by
    rw [circle_h4_symmetric_operator_apply]
    unfold circleSymmetricL2Expression
    simp only [inner_add_right,inner_sub_right,inner_smul_right] at hdiv ⊢
    rw [hfourth,hdiv]
    ring
  have h2 : ‖inner ℂ (circleH4Jet T g).second (circleH4Jet T f).second‖ ≤
      ((359/500:ℝ)*W)*((359/500:ℝ)*V) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hg₂ hf₂ (norm_nonneg _) (by positivity))
  have h1 : ‖inner ℂ (circleH4Jet T g).first
      (circleMultiplyL2 T h (circleH4Jet T f).first)‖ ≤ ((17/40:ℝ)*W)*((17/40:ℝ)*V) := by
    apply (multiply_pairing_bound T h _ _).trans
    have hhg := mul_le_mul hg₁ hhnorm (norm_nonneg _) (by positivity : (0:ℝ) ≤ (17/40)*W)
    simpa only [mul_one] using mul_le_mul hhg hf₁ (norm_nonneg _) (by positivity)
  have h0 : ‖inner ℂ (g:CircleL2 T) (f:CircleL2 T)‖ ≤ W*V :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hg hf (norm_nonneg _) hW)
  have hv : ‖inner ℂ (g:CircleL2 T) (circleMultiplyL2 T h₂ (f:CircleL2 T))‖ ≤ W*2*V := by
    apply (multiply_pairing_bound T h₂ _ _).trans
    exact mul_le_mul (mul_le_mul hg hh₂norm (norm_nonneg _) hW) hf (norm_nonneg _) (by positivity)
  rw [hid]
  let a := (-4:ℂ)*inner ℂ (circleH4Jet T g).second (circleH4Jet T f).second
  let b := (45:ℂ)*inner ℂ (circleH4Jet T g).first (circleMultiplyL2 T h (circleH4Jet T f).first)
  let c := (42:ℂ)*inner ℂ (g:CircleL2 T) (f:CircleL2 T)
  let d := (15/4:ℂ)*inner ℂ (g:CircleL2 T) (circleMultiplyL2 T h₂ (f:CircleL2 T))
  have ht : ‖a+b-c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
    have h1 := norm_add_le a b
    have h2 := norm_sub_le (a+b) c
    have h3 := norm_add_le (a+b-c) d
    linarith only [h1,h2,h3]
  dsimp only [a,b,c,d] at ht
  norm_num only [norm_mul,norm_neg,Complex.norm_ofNat,norm_div] at ht
  nlinarith only [ht,h2,h1,h0,hv,mul_nonneg hV hW]

end Lemniscate
