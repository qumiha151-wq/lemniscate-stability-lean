import Lemniscate.PeriodicH4Operator

/-! Completeness of cosine synthesis in the Fourier-defined even cosine sector.
The zero mode has its own normalization and is retained in the reconstruction. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ENNReal ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

def InCircleEvenCosineSector (f : CircleL2 T) : Prop :=
  (∀ n : ℤ, fourierCoeff f (-n) = fourierCoeff f n) ∧
    ∀ n : ℤ, fourierCoeff f (2*n+1) = 0

theorem evenCosineFactor_ne_zero : evenCosineFactor ≠ 0 := by
  intro h
  have hn := evenCosineFactor_normalization
  simp only [h, zero_mul] at hn
  exact zero_ne_one hn

theorem circle_cosine_synthesis_mem_sector (v : CosineSequenceSpace) :
    InCircleEvenCosineSector T (circleEvenCosineSynthesis T v) :=
  ⟨circle_even_cosine_coeff_neg T v, circle_even_cosine_coeff_odd T v⟩

theorem circle_cosine_fourier_ext (f g : CircleL2 T)
    (hpos : ∀ j : ℕ, fourierCoeff f (2*(j:ℤ)) = fourierCoeff g (2*(j:ℤ)))
    (hf : InCircleEvenCosineSector T f) (hg : InCircleEvenCosineSector T g) : f = g := by
  have hnat (n : ℕ) : fourierCoeff f (n:ℤ) = fourierCoeff g (n:ℤ) := by
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · have he : (n:ℤ) = 2*(j:ℤ) := by exact_mod_cast (by omega : n = 2*j)
      rw [he, hpos]
    · have he : (n:ℤ) = 2*(j:ℤ)+1 := by exact_mod_cast hj
      rw [he, hf.2, hg.2]
  apply circle_fourier_ext T
  intro n
  cases n with
  | ofNat n => exact hnat n
  | negSucc n =>
    change fourierCoeff f (-((n+1:ℕ):ℤ)) = fourierCoeff g (-((n+1:ℕ):ℤ))
    rw [hf.1, hg.1, hnat]

theorem circle_even_cosine_sector_representation (f : CircleL2 T)
    (hf : InCircleEvenCosineSector T f) :
    ∃ v : CosineSequenceSpace, f = circleEvenCosineSynthesis T v := by
  have hi : Function.Injective (fun j : ℕ => 2*(j:ℤ)) := by
    intro a b h
    change 2*(a:ℤ) = 2*(b:ℤ) at h
    omega
  have hs := (circle_fourier_square_summable T f).comp_injective hi
  have hm : Memℓp (fun j : ℕ => fourierCoeff f (2*(j:ℤ))) 2 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Function.comp_def] using hs
  let w : CosineSequenceSpace := ⟨fun j => evenCosineFactor⁻¹*fourierCoeff f (2*(j:ℤ)),
    hm.const_mul evenCosineFactor⁻¹⟩
  let v : CosineSequenceSpace := w + lp.single 2 0 (fourierCoeff f 0 - w 0)
  refine ⟨v, circle_cosine_fourier_ext T f (circleEvenCosineSynthesis T v) ?_
    hf (circle_cosine_synthesis_mem_sector T v)⟩
  intro j
  by_cases hj : j = 0
  · subst j
    simp only [Nat.cast_zero, mul_zero, circle_even_cosine_coeff_zero]
    change fourierCoeff f 0 = w 0 + lp.single (E := fun _ : ℕ => ℂ) 2 0 (fourierCoeff f 0 - w 0) 0
    rw [lp.single_apply_self]
    ring
  · rw [circle_even_cosine_coeff_pos T v j (Nat.pos_of_ne_zero hj)]
    change fourierCoeff f (2*(j:ℤ)) =
      (w j + lp.single (E := fun _ : ℕ => ℂ) 2 0 (fourierCoeff f 0 - w 0) j)*evenCosineFactor
    rw [lp.single_apply_ne _ _ _ hj, add_zero]
    change fourierCoeff f (2*(j:ℤ)) =
      (evenCosineFactor⁻¹*fourierCoeff f (2*(j:ℤ)))*evenCosineFactor
    rw [mul_right_comm, inv_mul_cancel₀ evenCosineFactor_ne_zero, one_mul]

theorem circle_even_cosine_sector_iff_representation (f : CircleL2 T) :
    InCircleEvenCosineSector T f ↔ ∃ v : CosineSequenceSpace,
      f = circleEvenCosineSynthesis T v := by
  constructor
  · exact circle_even_cosine_sector_representation T f
  · rintro ⟨v, rfl⟩
    exact circle_cosine_synthesis_mem_sector T v

theorem circle_h4_operator_even_cosine_sector_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T)
    (hsector : InCircleEvenCosineSector T (f : CircleL2 T)) :
    (inner ℂ (f : CircleL2 T) (circleH4Operator T h h₁ h₂ f)).re ≤
      -(21/4:ℝ)*‖(f : CircleL2 T)‖^2 := by
  obtain ⟨v, hv⟩ := circle_even_cosine_sector_representation T (f : CircleL2 T) hsector
  exact circle_h4_operator_cosine_dissipative T h h₁ h₂ hh hh₁ hreal h₁real h₂real
    hs hc hr f v hv

end Lemniscate
