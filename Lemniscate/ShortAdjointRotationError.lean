import Lemniscate.ShortAdjointRotation
import Lemniscate.ShortAdjointFiniteBounds
import Lemniscate.ShortAdjointProjectionError
import Lemniscate.ShortEvenFunctions

/-! The actual normalized seven-mode rotation approximation.  Its
normalization error is quadratic in the actual orthogonal L2 tail. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

theorem short_actual_rotation_approximation_error :
    ‖((circleShortRotationVector T q p hq hp-circleShortRotationApproximation T:
        circleH4Domain T):CircleL2 T)‖ < (1/160000:ℝ)/250 ∧
      shortH1Norm T (circleShortRotationVector T q p hq hp-
        circleShortRotationApproximation T) < (1/160000:ℝ)/16 ∧
      shortVNorm T (circleShortRotationVector T q p hq hp-
        circleShortRotationApproximation T) < (1/160000:ℝ) := by
  let e := -circleUnitRotationH4 T q p hq hp
  let g := circleSineTrialH4 T 7 (fun i => (shortRotationCoefficient i.val:ℂ))
  let E := circleSineTrialH4 T 7
    (fun i => (shortRotationSine shortActualCoefficient i:ℂ))
  let s := Real.sqrt (∑ i : Fin 7, shortActualRotationRaw i^2)
  let a := 2*s/shortRotationCoefficientNorm
  have hspos : 0 < s :=
    (by norm_num [shortRotationNormInput] : (0:ℝ) < (shortRotationNormInput.lo:ℝ)).trans_le
      short_rotation_norm_sound.1
  have hapos : 0 < a := div_pos (mul_pos (by norm_num) hspos)
    short_rotation_coefficient_norm_bounds.1
  have hcoef (i : Fin 7) : shortRotationCoefficient i.val =
      a*shortRotationSine shortActualCoefficient i := by
    have hs0 : s ≠ 0 := hspos.ne'
    have hn0 := short_rotation_coefficient_norm_bounds.1.ne'
    have hci : shortActualCoefficient (i.val+1) =
        evenCoefficient lemniscateFrequencySquared nome (i.val+1) := by
      simp only [shortActualCoefficient,fourierCoefficient,
        if_neg (by omega : i.val+1 ≠ 0)]
    change 2*((i.val+1:ℕ):ℝ)*evenCoefficient lemniscateFrequencySquared nome
      (i.val+1)/shortRotationCoefficientNorm =
        (2*s/shortRotationCoefficientNorm)*
          ((((i.val:ℝ)+1)*shortActualCoefficient (i.val+1))/s)
    rw [hci]
    push_cast
    field_simp
    <;> ring
  have hg : g = (a:ℂ) • E := by
    dsimp only [g,E,circleSineTrialH4]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoef,Complex.ofReal_mul,smul_smul]
  have hfinite := short_actual_finite_vector_bounds T
  have hE : ‖(E:CircleL2 T)‖ = 1 := by
    have h := hfinite.1
    change ‖I • (E:CircleL2 T)‖ = 1 at h
    simpa only [norm_smul,Complex.norm_I,one_mul] using h
  have hEV : shortVNorm T E < 5 := by
    have h := hfinite.2.2.1
    change shortVNorm T (I • E) < 5 at h
    simpa only [short_v_norm_smul,Complex.norm_I,one_mul] using h
  have hEven : E ∈ shortEvenDomain T := by
    have h : I • E ∈ shortEvenDomain T := (short_neutral_vectors_mem_even T).1
    have h' := (shortEvenDomain T).smul_mem (-I) h
    simpa only [smul_smul,show (-I)*I = 1 by simp,one_smul] using h'
  have hEH : shortH1Norm T E ≤ 5 := (short_even_h1_le_v T E hEven).trans hEV.le
  have hgn : ‖g‖ = a := by
    rw [hg,norm_smul]
    change ‖(a:ℂ)‖*‖(E:CircleL2 T)‖ = a
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hapos,hE,mul_one]
  have hgpos : 0 < ‖g‖ := by rw [hgn]; exact hapos
  have hnormalize : (‖g‖:ℂ)⁻¹ • g = E := by
    rw [hgn,hg,smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hapos.ne'),one_smul]
  have hi : (inner ℂ g e).re = ‖g‖^2 := by
    change (inner ℂ (g:CircleL2 T) (e:CircleL2 T)).re = _
    have hip : inner ℂ (g:CircleL2 T) (e:CircleL2 T) =
        ∑ i : Fin 7, ((shortRotationCoefficient i.val)^2:ℂ) := by
      change inner ℂ (∑ i : Fin 7,
        (shortRotationCoefficient i.val:ℂ) • circleEvenSineMode T i.val)
          (-circleUnitRotation T q p) = _
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_smul_left,
        circle_short_positive_rotation_pairing T q p hq hp he hqreal hpreal hs hc hr]
      simp only [Complex.conj_ofReal,Complex.ofReal_pow]
      ring
    rw [hip,Complex.re_sum]
    have hn := (short_sine_trial_norms_sq T
      (fun i : Fin 7 => (shortRotationCoefficient i.val:ℂ))).1
    simpa only [← Complex.ofReal_pow,Complex.ofReal_re,Complex.norm_real,
      Real.norm_eq_abs,sq_abs] using! hn.symm
  have hen : ‖e‖ = 1 := short_positive_rotation_norm T q p hq hp he hqreal hpreal hs hc ho hr
  have ht := short_positive_rotation_truncation_error T q p hq hp he hqreal hpreal hs hc ho hr
  have h0 := short_normalized_projection_error e g (normSeminorm ℂ (circleH4Domain T))
    (1/45000000) (1/45000000) 1 hen hgpos hi ht.1.le (by norm_num) ht.1.le
      (by norm_num) (by rw [hnormalize]; exact hE.le)
  have h1 := short_normalized_projection_error e g (shortH1Seminorm T)
    (1/45000000) (19/50000000) 5 hen hgpos hi ht.1.le (by norm_num) ht.2.1.le
      (by norm_num) (by rw [hnormalize]; exact hEH)
  have h2 := short_normalized_projection_error e g (shortVSeminorm T)
    (1/45000000) (3/500000) 5 hen hgpos hi ht.1.le (by norm_num) ht.2.2.le
      (by norm_num) (by rw [hnormalize]; exact hEV.le)
  rw [hnormalize] at h0 h1 h2
  have hphase : circleShortRotationVector T q p hq hp-circleShortRotationApproximation T =
      I • (e-E) := by
    dsimp only [circleShortRotationVector,circleShortRotationApproximation,e,E]
    module
  rw [hphase,short_h1_norm_smul,short_v_norm_smul]
  change ‖I • ((e-E:circleH4Domain T):CircleL2 T)‖ < _ ∧ _
  rw [norm_smul,Complex.norm_I,one_mul,one_mul,one_mul]
  exact ⟨h0.trans_lt (by norm_num),h1.trans_lt (by norm_num),
    h2.trans_lt (by norm_num)⟩

end Profile
end Lemniscate
