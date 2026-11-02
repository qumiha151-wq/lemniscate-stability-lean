import Lemniscate.EvenFactorData
import Lemniscate.IntervalSoundness
import Lemniscate.FiniteEnergyCertificate

/-! Soundness of the finite factor data: an actual real symmetric matrix
in the listed intervals inherits the certified quadratic-form estimate. -/
namespace Lemniscate
open Complex Matrix CoarseArithmetic
open scoped ComplexConjugate

theorem even_factor_correction_symm (k : Fin 5) (i j : Fin 31) :
    evenFactorCorrection k i j = evenFactorCorrection k j i := by
  unfold evenFactorCorrection
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro r _
    ring
  · by_cases hij : i = j
    · subst j
      rfl
    · simp only [if_neg hij, if_neg (Ne.symm hij)]

theorem even_factor_data_energy (k : Fin 5) (B : Matrix (Fin 31) (Fin 31) ℝ)
    (hB : ∀ i j, B i j = B j i)
    (hI : ∀ i j, Contains (evenBernsteinInterval k i j) (B i j))
    (hd : ∀ i, 0 ≤ evenFactorDiagonal k i)
    (hrow : ∀ i, evenFactorRowBound k i ≤ 1) (v : Fin 31 → ℂ) :
    (∑ i, ∑ j, conj (v i)*(B i j:ℂ)*v j).re ≤
      ∑ i, (-1-(evenFactorPenalty i:ℝ))*‖v i‖^2 := by
  let L : Matrix (Fin 31) (Fin 31) ℝ := fun i j => (evenFactorLower k i j:ℝ)
  let d : Fin 31 → ℝ := fun i => (evenFactorDiagonal k i:ℝ)
  let δ : Fin 31 → ℝ := fun i => (evenFactorPenalty i:ℝ)
  let R : Matrix (Fin 31) (Fin 31) ℝ := fun i j => B i j+(evenFactorCorrection k i j:ℝ)
  have hc (i j : Fin 31) :
      (L*diagonal d*Lᵀ) i j+(if i = j then δ i+2 else 0) =
        (evenFactorCorrection k i j:ℝ) := by
    rw [mul_apply]
    simp only [mul_diagonal, transpose_apply]
    dsimp only [L, d, δ]
    unfold evenFactorCorrection
    split_ifs <;> push_cast <;> rfl
  have hR : ∀ i j, R i j = R j i := by
    intro i j
    dsimp only [R]
    rw [hB i j, even_factor_correction_symm k i j]
  have hr : ∀ i, ∑ j, |R i j| ≤ 1 := by
    intro i
    calc
      _ ≤ ∑ j : Fin 31, (absUpper (add (evenBernsteinInterval k i j)
          (point (evenFactorCorrection k i j))):ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        exact absUpper_sound _ _ (add_sound _ _ _ _ (hI i j)
          (point_sound (evenFactorCorrection k i j)))
      _ = (evenFactorRowBound k i:ℝ) := by
        simp only [evenFactorRowBound, Rat.cast_sum]
      _ ≤ 1 := by exact_mod_cast hrow i
  have hA : ∀ i j, B i j = -(L*diagonal d*Lᵀ) i j-
      (if i = j then δ i+2 else 0)+R i j := by
    intro i j
    dsimp only [R]
    linarith only [hc i j]
  have hd' : ∀ i, 0 ≤ d i := by
    intro i
    change (0:ℝ) ≤ (evenFactorDiagonal k i:ℝ)
    exact_mod_cast hd i
  have h := finite_factor_energy_bound B L R d δ 2 1 hd' hR hr hA v
  simpa only [show (1:ℝ)-2 = -1 by norm_num] using h

end Lemniscate
