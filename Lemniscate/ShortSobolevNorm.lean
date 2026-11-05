import Lemniscate.PeriodicH4Domain
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Seminorm

/-! Angular-coordinate norms on the actual weak H4 domain.  The product-jet
definitions give the triangle and duality inequalities directly, while
Parseval identifies their Fourier weights. -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

def shortAngularFrequency : ℝ := 2 * Real.pi / T

theorem short_angular_frequency_pos : 0 < shortAngularFrequency T := by
  have := (Fact.out : 0 < T)
  unfold shortAngularFrequency
  positivity

private theorem short_kappa_ne : shortAngularFrequency T ≠ 0 :=
  ne_of_gt (short_angular_frequency_pos T)

def shortVJet (f : circleH4Domain T) : WithLp 2 (ℂ × CircleL2 T) :=
  WithLp.toLp 2 (fourierCoeff (f : CircleL2 T) 0,
    ((shortAngularFrequency T)⁻¹ ^ 2 : ℝ) • (circleH4Jet T f).second)

def shortH1Jet (f : circleH4Domain T) : WithLp 2 (CircleL2 T × CircleL2 T) :=
  WithLp.toLp 2 ((f : CircleL2 T),
    (shortAngularFrequency T)⁻¹ • (circleH4Jet T f).first)

def shortVNorm (f : circleH4Domain T) : ℝ := ‖shortVJet T f‖

def shortH1Norm (f : circleH4Domain T) : ℝ := ‖shortH1Jet T f‖

theorem short_v_norm_nonneg (f : circleH4Domain T) : 0 ≤ shortVNorm T f :=
  norm_nonneg _

theorem short_h1_norm_nonneg (f : circleH4Domain T) : 0 ≤ shortH1Norm T f :=
  norm_nonneg _

theorem short_v_norm_sq (f : circleH4Domain T) :
    shortVNorm T f ^ 2 = ‖fourierCoeff (f : CircleL2 T) 0‖ ^ 2 +
      (shortAngularFrequency T)⁻¹ ^ 4 * ‖(circleH4Jet T f).second‖ ^ 2 := by
  rw [shortVNorm, WithLp.prod_norm_sq_eq_of_L2]
  change ‖fourierCoeff (f : CircleL2 T) 0‖ ^ 2 +
    ‖((shortAngularFrequency T)⁻¹ ^ 2 : ℝ) • (circleH4Jet T f).second‖ ^ 2 = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  ring

theorem short_h1_norm_sq (f : circleH4Domain T) :
    shortH1Norm T f ^ 2 = ‖(f : CircleL2 T)‖ ^ 2 +
      (shortAngularFrequency T)⁻¹ ^ 2 * ‖(circleH4Jet T f).first‖ ^ 2 := by
  rw [shortH1Norm, WithLp.prod_norm_sq_eq_of_L2]
  change ‖(f : CircleL2 T)‖ ^ 2 +
    ‖(shortAngularFrequency T)⁻¹ • (circleH4Jet T f).first‖ ^ 2 = _
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (short_angular_frequency_pos T))]
  ring

private theorem short_v_jet_add (f g : circleH4Domain T) :
    shortVJet T (f + g) = shortVJet T f + shortVJet T g := by
  have hc : fourierCoeff ((f + g : circleH4Domain T) : CircleL2 T) 0 =
      fourierCoeff (f : CircleL2 T) 0 + fourierCoeff (g : CircleL2 T) 0 := by
    simp only [← fourierBasis_repr, Submodule.coe_add, map_add]
    rfl
  unfold shortVJet
  rw [circle_h4_jet_add, hc]
  change WithLp.toLp 2 (_, (shortAngularFrequency T)⁻¹ ^ 2 •
      ((circleH4Jet T f).second + (circleH4Jet T g).second)) = _
  rw [smul_add]
  rfl

private theorem short_h1_jet_add (f g : circleH4Domain T) :
    shortH1Jet T (f + g) = shortH1Jet T f + shortH1Jet T g := by
  unfold shortH1Jet
  rw [circle_h4_jet_add]
  change WithLp.toLp 2 ((f : CircleL2 T) + (g : CircleL2 T),
    (shortAngularFrequency T)⁻¹ •
      ((circleH4Jet T f).first + (circleH4Jet T g).first)) = _
  rw [smul_add]
  rfl

theorem short_v_norm_add_le (f g : circleH4Domain T) :
    shortVNorm T (f + g) ≤ shortVNorm T f + shortVNorm T g := by
  unfold shortVNorm
  rw [short_v_jet_add]
  exact norm_add_le _ _

theorem short_h1_norm_add_le (f g : circleH4Domain T) :
    shortH1Norm T (f + g) ≤ shortH1Norm T f + shortH1Norm T g := by
  unfold shortH1Norm
  rw [short_h1_jet_add]
  exact norm_add_le _ _

theorem short_v_norm_smul (c : ℂ) (f : circleH4Domain T) :
    shortVNorm T (c • f) = ‖c‖ * shortVNorm T f := by
  have he : shortVJet T (c • f) = c • shortVJet T f := by
    unfold shortVJet
    rw [circle_h4_jet_smul]
    change WithLp.toLp 2 (fourierCoeff (c • (f : CircleL2 T)) 0,
      (shortAngularFrequency T)⁻¹ ^ 2 • (c • (circleH4Jet T f).second)) = _
    rw [circle_fourierCoeff_smul, smul_comm]
    rfl
  unfold shortVNorm
  rw [he, norm_smul]

theorem short_h1_norm_smul (c : ℂ) (f : circleH4Domain T) :
    shortH1Norm T (c • f) = ‖c‖ * shortH1Norm T f := by
  have he : shortH1Jet T (c • f) = c • shortH1Jet T f := by
    unfold shortH1Jet
    rw [circle_h4_jet_smul]
    change WithLp.toLp 2 (c • (f : CircleL2 T),
      (shortAngularFrequency T)⁻¹ • (c • (circleH4Jet T f).first)) = _
    rw [smul_comm]
    rfl
  unfold shortH1Norm
  rw [he, norm_smul]

def shortVSeminorm : Seminorm ℂ (circleH4Domain T) :=
  Seminorm.of (shortVNorm T) (short_v_norm_add_le T) (short_v_norm_smul T)

def shortH1Seminorm : Seminorm ℂ (circleH4Domain T) :=
  Seminorm.of (shortH1Norm T) (short_h1_norm_add_le T) (short_h1_norm_smul T)

@[simp] theorem short_v_seminorm_apply (f : circleH4Domain T) :
    shortVSeminorm T f = shortVNorm T f := rfl

@[simp] theorem short_h1_seminorm_apply (f : circleH4Domain T) :
    shortH1Seminorm T f = shortH1Norm T f := rfl

theorem short_v_inner_bound (f g : circleH4Domain T) :
    ‖inner ℂ (shortVJet T f) (shortVJet T g)‖ ≤ shortVNorm T f * shortVNorm T g :=
  norm_inner_le_norm _ _

theorem short_h1_inner_bound (f g : circleH4Domain T) :
    ‖inner ℂ (shortH1Jet T f) (shortH1Jet T g)‖ ≤
      shortH1Norm T f * shortH1Norm T g := norm_inner_le_norm _ _

theorem short_h4_first_fourier_sq (f : circleH4Domain T) (n : ℤ) :
    ‖fourierCoeff (circleH4Jet T f).first n‖ ^ 2 =
      shortAngularFrequency T ^ 2 * (n : ℝ) ^ 2 *
        ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2 := by
  rw [fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hfirst]
  simp only [circleFrequencyFactor, shortAngularFrequency, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    mul_pow, sq_abs]

theorem short_h4_second_fourier_sq (f : circleH4Domain T) (n : ℤ) :
    ‖fourierCoeff (circleH4Jet T f).second n‖ ^ 2 =
      shortAngularFrequency T ^ 4 * (n : ℝ) ^ 4 *
        ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2 := by
  rw [fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hsecond,
    norm_mul, mul_pow, short_h4_first_fourier_sq]
  simp only [circleFrequencyFactor, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one, mul_pow, sq_abs]
  unfold shortAngularFrequency
  ring

theorem short_fourier_fourth_summable (f : circleH4Domain T) :
    Summable (fun n : ℤ => (n : ℝ) ^ 4 * ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2) := by
  have hs := (circle_fourier_square_summable T (circleH4Jet T f).second).mul_left
    ((shortAngularFrequency T)⁻¹ ^ 4)
  apply hs.congr
  intro n
  rw [short_h4_second_fourier_sq]
  field_simp [short_kappa_ne T]

theorem short_fourier_second_summable (f : circleH4Domain T) :
    Summable (fun n : ℤ => (n : ℝ) ^ 2 * ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2) := by
  have hs := (circle_fourier_square_summable T (circleH4Jet T f).first).mul_left
    ((shortAngularFrequency T)⁻¹ ^ 2)
  apply hs.congr
  intro n
  rw [short_h4_first_fourier_sq]
  field_simp [short_kappa_ne T]

theorem short_fourier_second_sum (f : circleH4Domain T) :
    ∑' n : ℤ, (n : ℝ) ^ 2 * ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2 =
      (shortAngularFrequency T)⁻¹ ^ 2 * ‖(circleH4Jet T f).first‖ ^ 2 := by
  rw [circle_norm_sq_fourier, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [short_h4_first_fourier_sq]
  field_simp [short_kappa_ne T]

theorem short_fourier_fourth_sum (f : circleH4Domain T) :
    ∑' n : ℤ, (n : ℝ) ^ 4 * ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2 =
      (shortAngularFrequency T)⁻¹ ^ 4 * ‖(circleH4Jet T f).second‖ ^ 2 := by
  rw [circle_norm_sq_fourier, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [short_h4_second_fourier_sq]
  field_simp [short_kappa_ne T]

theorem short_h1_norm_sq_fourier (f : circleH4Domain T) :
    shortH1Norm T f ^ 2 = ∑' n : ℤ,
      (1 + (n : ℝ) ^ 2) * ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2 := by
  rw [short_h1_norm_sq, circle_norm_sq_fourier, ← short_fourier_second_sum]
  rw [← (circle_fourier_square_summable T (f : CircleL2 T)).tsum_add
    (short_fourier_second_summable T f)]
  apply tsum_congr
  intro n
  ring

private theorem short_weight_eq (n : ℤ) :
    max (1 : ℝ) ((n : ℝ) ^ 4) = (if n = 0 then 1 else 0) + (n : ℝ) ^ 4 := by
  by_cases hn : n = 0
  · subst n
    norm_num
  · have ha : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ha 4
    have hpow : |(n : ℝ)| ^ 4 = (n : ℝ) ^ 4 := by
      calc
        _ = (|(n : ℝ)| ^ 2) ^ 2 := by ring
        _ = ((n : ℝ) ^ 2) ^ 2 := by rw [sq_abs]
        _ = _ := by ring
    rw [hpow] at hp
    norm_num only [one_pow] at hp
    simp only [if_neg hn, zero_add, max_eq_right hp]

theorem short_v_weight_summable (f : circleH4Domain T) :
    Summable (fun n : ℤ => max (1 : ℝ) ((n : ℝ) ^ 4) *
      ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2) := by
  have hm : Summable (fun n : ℤ => if n = 0 then
      ‖fourierCoeff (f : CircleL2 T) 0‖ ^ 2 else 0) := (hasSum_ite_eq 0 _).summable
  apply (hm.add (short_fourier_fourth_summable T f)).congr
  intro n
  rw [short_weight_eq]
  split_ifs with hn
  · subst n
    norm_num
  · ring

theorem short_v_norm_sq_fourier (f : circleH4Domain T) :
    shortVNorm T f ^ 2 = ∑' n : ℤ, max (1 : ℝ) ((n : ℝ) ^ 4) *
      ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2 := by
  have hm : Summable (fun n : ℤ => if n = 0 then
      ‖fourierCoeff (f : CircleL2 T) 0‖ ^ 2 else 0) := (hasSum_ite_eq 0 _).summable
  rw [short_v_norm_sq, ← short_fourier_fourth_sum]
  calc
    _ = ∑' n : ℤ, ((if n = 0 then ‖fourierCoeff (f : CircleL2 T) 0‖ ^ 2 else 0) +
        (n : ℝ) ^ 4 * ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2) := by
      rw [hm.tsum_add (short_fourier_fourth_summable T f), tsum_ite_eq]
    _ = _ := by
      apply tsum_congr
      intro n
      rw [short_weight_eq]
      split_ifs with hn
      · subst n
        norm_num
      · ring

theorem short_h1_controls (f : circleH4Domain T) :
    ‖(f : CircleL2 T)‖ ≤ shortH1Norm T f ∧
      ‖(circleH4Jet T f).first‖ ≤ shortAngularFrequency T * shortH1Norm T f := by
  have hs := short_h1_norm_sq T f
  have hκ := short_angular_frequency_pos T
  have hk := short_kappa_ne T
  have hmul := congrArg (fun u : ℝ => shortAngularFrequency T ^ 2 * u) hs
  field_simp [hk] at hmul
  constructor
  · nlinarith [short_h1_norm_nonneg T f, norm_nonneg (f : CircleL2 T),
      mul_nonneg (sq_nonneg ((shortAngularFrequency T)⁻¹))
        (sq_nonneg ‖(circleH4Jet T f).first‖)]
  · apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hκ.le (short_h1_norm_nonneg T f))).mp
    nlinarith only [hmul, sq_nonneg (shortAngularFrequency T * ‖(f : CircleL2 T)‖)]

theorem short_v_controls (f : circleH4Domain T) :
    ‖(f : CircleL2 T)‖ ≤ shortVNorm T f ∧
      ‖(circleH4Jet T f).second‖ ≤ shortAngularFrequency T ^ 2 * shortVNorm T f := by
  have hl2 : ‖(f : CircleL2 T)‖ ^ 2 ≤ shortVNorm T f ^ 2 := by
    rw [circle_norm_sq_fourier, short_v_norm_sq_fourier]
    apply (circle_fourier_square_summable T (f : CircleL2 T)).tsum_le_tsum _
      (short_v_weight_summable T f)
    intro n
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (le_max_left (1 : ℝ) ((n : ℝ) ^ 4))
      (sq_nonneg ‖fourierCoeff (f : CircleL2 T) n‖)
  have hs := short_v_norm_sq T f
  have hmul := congrArg (fun u : ℝ => shortAngularFrequency T ^ 4 * u) hs
  field_simp [short_kappa_ne T] at hmul
  constructor
  · exact (sq_le_sq₀ (norm_nonneg _) (short_v_norm_nonneg T f)).mp hl2
  · apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (sq_nonneg _) (short_v_norm_nonneg T f))).mp
    nlinarith only [hmul,
      sq_nonneg (shortAngularFrequency T ^ 2 * ‖fourierCoeff (f : CircleL2 T) 0‖)]

theorem short_v_even_first_control (f : circleH4Domain T)
    (heven : ∀ n : ℤ, Odd n → fourierCoeff (f : CircleL2 T) n = 0) :
    ‖(circleH4Jet T f).first‖ ≤ shortAngularFrequency T / 2 * shortVNorm T f := by
  have hpoint (n : ℤ) : (n : ℝ) ^ 2 * ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2 ≤
      (1 / 4 : ℝ) * (max (1 : ℝ) ((n : ℝ) ^ 4) *
        ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2) := by
    by_cases hn : n = 0
    · subst n
      simp only [Int.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
      positivity
    by_cases ho : Odd n
    · rw [heven n ho, norm_zero]
      norm_num
    have h₁ : n ≠ 1 := by
      rintro rfl
      exact ho (by decide)
    have hminus : n ≠ -1 := by
      rintro rfl
      exact ho (by decide)
    have hn2 : n ≤ -2 ∨ 2 ≤ n := by omega
    have hsq : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases hn2 with hh | hh
      · have hh' : (n : ℝ) ≤ -2 := by exact_mod_cast hh
        nlinarith
      · have hh' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hh
        nlinarith
    have hsymbol : (n : ℝ) ^ 2 ≤ (1 / 4 : ℝ) * (n : ℝ) ^ 4 := by
      nlinarith only [mul_nonneg (sq_nonneg (n : ℝ))
        (sub_nonneg.mpr hsq)]
    rw [short_weight_eq, if_neg hn, zero_add]
    have hm := mul_le_mul_of_nonneg_right hsymbol
      (sq_nonneg ‖fourierCoeff (f : CircleL2 T) n‖)
    nlinarith only [hm]
  have hs := (short_fourier_second_summable T f).tsum_le_tsum hpoint
    ((short_v_weight_summable T f).mul_left (1 / 4 : ℝ))
  rw [short_fourier_second_sum, tsum_mul_left, ← short_v_norm_sq_fourier] at hs
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (shortAngularFrequency T))
  have hcancel : shortAngularFrequency T ^ 2 * (shortAngularFrequency T)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (short_kappa_ne T)]
    norm_num
  rw [← mul_assoc, hcancel, one_mul] at hm
  have hκ := short_angular_frequency_pos T
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by positivity : 0 ≤ shortAngularFrequency T / 2)
      (short_v_norm_nonneg T f))).mp
  nlinarith only [hm]

/-- Affine fourth-order weights, in particular the weighted adjoint energy,
are genuine Parseval sums on the weak H4 domain. -/
theorem short_fourier_affine_weight_summable (f : circleH4Domain T) (a b : ℝ) :
    Summable (fun n : ℤ => (a * (n : ℝ) ^ 4 + b) *
      ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2) := by
  apply (((short_fourier_fourth_summable T f).mul_left a).add
    ((circle_fourier_square_summable T (f : CircleL2 T)).mul_left b)).congr
  intro n
  ring

theorem short_fourier_affine_weight_sum (f : circleH4Domain T) (a b : ℝ) :
    (∑' n : ℤ, (a * (n : ℝ) ^ 4 + b) *
      ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2) =
    a * (shortAngularFrequency T)⁻¹ ^ 4 * ‖(circleH4Jet T f).second‖ ^ 2 +
      b * ‖(f : CircleL2 T)‖ ^ 2 := by
  calc
    _ = ∑' n : ℤ, (a * ((n : ℝ) ^ 4 * ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2) +
        b * ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2) := by
      apply tsum_congr
      intro n
      ring
    _ = _ := by
      rw [((short_fourier_fourth_summable T f).mul_left a).tsum_add
        ((circle_fourier_square_summable T (f : CircleL2 T)).mul_left b),
        tsum_mul_left, tsum_mul_left, short_fourier_fourth_sum, ← circle_norm_sq_fourier]
      ring

end Lemniscate
