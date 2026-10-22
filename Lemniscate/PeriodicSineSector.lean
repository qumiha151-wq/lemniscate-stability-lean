import Lemniscate.PeriodicSineOperatorEnergy

/-! Completeness of the first-mode/tail synthesis in the actual Fourier-defined
even sine sector. The operator bound thus applies to every function in that
sector, without an extra assumed coefficient representation. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ENNReal ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

def InCircleEvenSineSector (f : CircleL2 T) : Prop :=
  (∀ n : ℤ, fourierCoeff f (-n) = -fourierCoeff f n) ∧
    ∀ n : ℤ, fourierCoeff f (2*n+1) = 0

theorem circle_sine_block_mem_sector (u : ℂ) (v : SineTailSpace) :
    InCircleEvenSineSector T (circleSineBlockFunction T u v) := by
  constructor
  · intro n
    simp only [circleSineBlockFunction, circle_fourierCoeff_add, circle_fourierCoeff_smul,
      circle_even_sine_mode_coeff_neg, circle_sine_tail_coeff_neg, mul_neg, neg_add]
  · intro n
    simp only [circleSineBlockFunction, circle_fourierCoeff_add, circle_fourierCoeff_smul,
      circle_even_sine_mode_coeff_odd, circle_sine_tail_coeff_odd, mul_zero, add_zero]

theorem circle_sine_block_coeff_first (u : ℂ) (v : SineTailSpace) :
    fourierCoeff (circleSineBlockFunction T u v) 2 = u*evenSineFactor := by
  have h := circle_even_sine_mode_coeff_pos T 0 0
  norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, mul_one, ite_true] at h
  simp only [circleSineBlockFunction, circle_fourierCoeff_add, circle_fourierCoeff_smul,
    h, circle_sine_tail_coeff_first, add_zero]

theorem circle_even_sine_sector_representation (f : CircleL2 T)
    (hf : InCircleEvenSineSector T f) :
    ∃ u : ℂ, ∃ v : SineTailSpace, f = circleSineBlockFunction T u v := by
  have hi : Function.Injective (fun j : ℕ => 2*((j+2:ℕ):ℤ)) := by
    intro a b h
    change 2*((a+2:ℕ):ℤ) = 2*((b+2:ℕ):ℤ) at h
    omega
  have hs := (circle_fourier_square_summable T f).comp_injective hi
  have hm : Memℓp (fun j : ℕ => fourierCoeff f (2*((j+2:ℕ):ℤ))) 2 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Function.comp_def] using hs
  let u : ℂ := evenSineFactor⁻¹*fourierCoeff f 2
  let v : SineTailSpace := ⟨fun j => evenSineFactor⁻¹*fourierCoeff f (2*((j+2:ℕ):ℤ)),
    hm.const_mul evenSineFactor⁻¹⟩
  have hz : fourierCoeff f 0 = 0 := by
    have h := hf.1 0
    simp only [neg_zero] at h
    linear_combination (1/2:ℂ)*h
  refine ⟨u, v, circle_sine_fourier_ext T f (circleSineBlockFunction T u v) ?_
    hf.1 (circle_sine_block_mem_sector T u v).1 hf.2 (circle_sine_block_mem_sector T u v).2⟩
  intro j
  by_cases hj : j = 0
  · subst j
    simp only [Nat.cast_zero, mul_zero, hz, circleSineBlockFunction,
      circle_fourierCoeff_add, circle_fourierCoeff_smul, circle_even_sine_mode_coeff_zero,
      circle_sine_tail_coeff_zero, mul_zero, add_zero]
  · by_cases hj1 : j = 1
    · subst j
      simp only [Nat.cast_one, mul_one, circle_sine_block_coeff_first]
      dsimp only [u]
      rw [mul_right_comm, inv_mul_cancel₀ evenSineFactor_ne_zero, one_mul]
    · have hk : j-2+2 = j := by omega
      rw [← hk, circle_sine_block_coeff_pos]
      change fourierCoeff f (2*((j-2+2:ℕ):ℤ)) =
        (evenSineFactor⁻¹*fourierCoeff f (2*((j-2+2:ℕ):ℤ)))*evenSineFactor
      rw [mul_right_comm, inv_mul_cancel₀ evenSineFactor_ne_zero, one_mul]

theorem circle_even_sine_sector_iff_representation (f : CircleL2 T) :
    InCircleEvenSineSector T f ↔ ∃ u : ℂ, ∃ v : SineTailSpace,
      f = circleSineBlockFunction T u v := by
  constructor
  · exact circle_even_sine_sector_representation T f
  · rintro ⟨u, v, rfl⟩
    exact circle_sine_block_mem_sector T u v

theorem circle_h4_operator_even_sine_sector_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T)
    (hsector : InCircleEvenSineSector T (f : CircleL2 T))
    (horth : inner ℂ (circleSineConstraintVector T) (f : CircleL2 T) = 0) :
    (inner ℂ (f : CircleL2 T) (circleH4Operator T h h₁ h₂ f)).re ≤
      -75*‖(f : CircleL2 T)‖^2 := by
  obtain ⟨u, v, hv⟩ := circle_even_sine_sector_representation T (f : CircleL2 T) hsector
  exact circle_h4_operator_sine_dissipative T h h₁ h₂ hh hh₁ hreal h₁real h₂real
    hs hc hr f u v hv horth

theorem paper_h4_operator_even_sine_sector_dissipative (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T)
    (hsector : InCircleEvenSineSector T (f : CircleL2 T))
    (horth : inner ℂ (circleContinuousL2 T (q*p)) (f : CircleL2 T) = 0) :
    (inner ℂ (f : CircleL2 T)
      (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f)).re ≤
        -75*‖(f : CircleL2 T)‖^2 := by
  obtain ⟨u, v, hv⟩ := circle_even_sine_sector_representation T (f : CircleL2 T) hsector
  exact paper_h4_operator_sine_dissipative T q p hq hp he hqreal hpreal hs hc ho hr f u v hv horth

end Lemniscate
