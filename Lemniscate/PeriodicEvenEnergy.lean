import Lemniscate.PeriodicReflectionSplit

/-! Dissipation for every H4 function supported on even Fourier frequencies
and orthogonal to the rotation vector. Reflection splitting and the vanishing
of operator cross terms are proved, not supplied as extra assumptions. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_h4_operator_reflection_parity (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (f : circleH4Domain T) (ε : ℂ)
    (hf : circleReflect T (f : CircleL2 T) = ε • (f : CircleL2 T)) :
    circleReflect T (circleH4Operator T h h₁ h₂ f) = ε • circleH4Operator T h h₁ h₂ f := by
  have he : circleReflectH4 T f = ε • f := Subtype.ext hf
  rw [← circle_h4_operator_reflect_of_even T h h₁ h₂ hh hh₁ hs, he, map_smul]

theorem circle_h4_operator_reflection_energy_split (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n) (f : circleH4Domain T) :
    inner ℂ (f : CircleL2 T) (circleH4Operator T h h₁ h₂ f) =
      inner ℂ (circleCosinePart T (f : CircleL2 T))
        (circleH4Operator T h h₁ h₂ (circleCosinePartH4 T f)) +
      inner ℂ (circleSinePart T (f : CircleL2 T))
        (circleH4Operator T h h₁ h₂ (circleSinePartH4 T f)) := by
  let A := circleH4Operator T h h₁ h₂
  let c := circleCosinePartH4 T f
  let s := circleSinePartH4 T f
  have hc : circleReflect T (c : CircleL2 T) = (c : CircleL2 T) :=
    circle_reflect_cosine_part T (f : CircleL2 T)
  have hs' : circleReflect T (s : CircleL2 T) = -(s : CircleL2 T) :=
    circle_reflect_sine_part T (f : CircleL2 T)
  have hAc : circleReflect T (A c) = A c := by
    simpa only [one_smul] using circle_h4_operator_reflection_parity T h h₁ h₂ hh hh₁ hs c 1
      (by simpa only [one_smul] using hc)
  have hAs : circleReflect T (A s) = -A s := by
    simpa only [neg_one_smul] using circle_h4_operator_reflection_parity T h h₁ h₂ hh hh₁ hs s (-1)
      (by simpa only [neg_one_smul] using hs')
  have hcs : inner ℂ (c : CircleL2 T) (A s) = 0 :=
    circle_reflection_orthogonal T _ _ hc hAs
  have hsc : inner ℂ (s : CircleL2 T) (A c) = 0 := by
    have hz := circle_reflection_orthogonal T _ _ hAc hs'
    rw [← inner_conj_symm, hz, map_zero]
  have he : c+s = f := circle_reflection_h4_parts_sum T f
  have he' := congrArg (fun z : circleH4Domain T => inner ℂ (z : CircleL2 T) (A z)) he
  change inner ℂ (f : CircleL2 T) (A f) =
    inner ℂ (c : CircleL2 T) (A c) + inner ℂ (s : CircleL2 T) (A s)
  simpa only [Submodule.coe_add, map_add, inner_add_left, inner_add_right,
    hcs, hsc, zero_add, add_zero] using he'.symm

theorem circle_h4_operator_even_frequencies_split_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T)
    (ho : ∀ n : ℤ, fourierCoeff (f : CircleL2 T) (2*n+1) = 0)
    (horth : inner ℂ (circleSineConstraintVector T) (f : CircleL2 T) = 0) :
    (inner ℂ (f : CircleL2 T) (circleH4Operator T h h₁ h₂ f)).re ≤
      -(21/4:ℝ)*‖circleCosinePart T (f : CircleL2 T)‖^2 -
        75*‖circleSinePart T (f : CircleL2 T)‖^2 := by
  have hcos := circle_h4_operator_even_cosine_sector_dissipative T h h₁ h₂
    hh hh₁ hreal h₁real h₂real hs hc hr (circleCosinePartH4 T f)
    (circle_cosine_part_mem_sector T (f : CircleL2 T) ho)
  have hsin := circle_h4_operator_even_sine_sector_dissipative T h h₁ h₂
    hh hh₁ hreal h₁real h₂real hs hc hr (circleSinePartH4 T f)
    (circle_sine_part_mem_sector T (f : CircleL2 T) ho)
    (circle_sine_part_constraint T (f : CircleL2 T) horth)
  rw [circle_h4_operator_reflection_energy_split T h h₁ h₂ hh hh₁ hs, Complex.add_re]
  simpa only [circle_cosine_part_h4_coe, circle_sine_part_h4_coe, sub_eq_add_neg,
    neg_mul] using add_le_add hcos hsin

theorem circle_h4_operator_even_frequencies_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T)
    (ho : ∀ n : ℤ, fourierCoeff (f : CircleL2 T) (2*n+1) = 0)
    (horth : inner ℂ (circleSineConstraintVector T) (f : CircleL2 T) = 0) :
    (inner ℂ (f : CircleL2 T) (circleH4Operator T h h₁ h₂ f)).re ≤
      -(21/4:ℝ)*‖(f : CircleL2 T)‖^2 := by
  have hb := circle_h4_operator_even_frequencies_split_bound T h h₁ h₂
    hh hh₁ hreal h₁real h₂real hs hc hr f ho horth
  rw [circle_reflection_parts_norm_sq T (f : CircleL2 T)]
  nlinarith [sq_nonneg ‖circleSinePart T (f : CircleL2 T)‖]

theorem paper_h4_operator_even_frequencies_dissipative (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T)
    (hf : ∀ n : ℤ, fourierCoeff (f : CircleL2 T) (2*n+1) = 0)
    (horth : inner ℂ (circleContinuousL2 T (q*p)) (f : CircleL2 T) = 0) :
    (inner ℂ (f : CircleL2 T)
      (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f)).re ≤
        -(21/4:ℝ)*‖(f : CircleL2 T)‖^2 := by
  apply circle_h4_operator_even_frequencies_dissipative T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
    (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
    _ _ _ hs hc hr f hf (circle_sine_profile_constraint T q p hq hs hc ho _ horth)
  · intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow, hqreal]
  · intro x
    change conj (2*(q x*p x)) = 2*(q x*p x)
    simp only [map_mul, map_ofNat, hqreal, hpreal]
  · intro x
    change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub, map_mul, map_one, map_ofNat, map_pow, hqreal]

end Lemniscate
