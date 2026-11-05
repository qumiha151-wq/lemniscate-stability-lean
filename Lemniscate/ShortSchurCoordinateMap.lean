import Lemniscate.ShortSchurPolynomialEnergy

namespace Lemniscate
open Matrix Finset Complex
open scoped ComplexConjugate

def shortLowRowIndex (i : Fin 7) : Fin 15 := ⟨i.val+4,by omega⟩

noncomputable def shortLowSmallBasis : Matrix (Fin 7) (Fin 7) ℝ :=
  fun i k => shortLowBasis (shortLowRowIndex i) k

noncomputable def shortLowSmallWeight (i : Fin 7) : ℝ :=
  max 1 ((shortHeadFrequency (shortLowRowIndex i):ℝ)^2)

noncomputable def shortLowSmallMatrix : Matrix (Fin 7) (Fin 7) ℝ :=
  diagonal (fun i => 1/shortLowSmallWeight i) * shortLowSmallBasis *
    (shortLowShear * shortLowRotation)

noncomputable def shortLowSmallInverse : Matrix (Fin 7) (Fin 7) ℝ :=
  shortLowRotation * ((1:Matrix (Fin 7) (Fin 7) ℝ)-shortLowShearPerturbation) *
    shortLowSmallBasisᵀ * diagonal shortLowSmallWeight

theorem short_low_small_weight_pos (i : Fin 7) : 0 < shortLowSmallWeight i :=
  lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)

theorem short_low_embedding_restrict (i k : Fin 7) :
    shortLowEmbedding (shortLowRowIndex i) k = shortLowSmallMatrix i k := by
  change (∑ a : Fin 7, shortLowWeightedBasis (shortLowRowIndex i) a *
    (shortLowShear*shortLowRotation) a k) =
    ∑ a : Fin 7, (diagonal (fun j => 1/shortLowSmallWeight j)*shortLowSmallBasis) i a *
      (shortLowShear*shortLowRotation) a k
  apply sum_congr rfl
  intro a _
  rw [Matrix.diagonal_mul]
  simp only [shortLowWeightedBasis,shortLowSmallBasis,shortLowSmallWeight]
  ring

theorem short_low_basis_outside (i : Fin 15) (k : Fin 7)
    (hi : i.val < 4 ∨ 10 < i.val) : shortLowBasis i k = 0 := by
  have h0 : shortHeadFrequency i ≠ 0 := by dsimp only [shortHeadFrequency]; omega
  have h2 : ¬(shortHeadFrequency i=2 ∨ shortHeadFrequency i= -2) := by
    dsimp only [shortHeadFrequency]; omega
  have h4 : ¬(shortHeadFrequency i=4 ∨ shortHeadFrequency i= -4) := by
    dsimp only [shortHeadFrequency]; omega
  have h6 : ¬(shortHeadFrequency i=6 ∨ shortHeadFrequency i= -6) := by
    dsimp only [shortHeadFrequency]; omega
  fin_cases k <;> simp [shortLowBasis,h0,not_or.mp h2,not_or.mp h4,not_or.mp h6]

theorem short_low_embedding_outside (i : Fin 15) (k : Fin 7)
    (hi : i.val < 4 ∨ 10 < i.val) : shortLowEmbedding i k = 0 := by
  unfold shortLowEmbedding
  rw [Matrix.mul_apply]
  apply sum_eq_zero
  intro a _
  rw [shortLowWeightedBasis,short_low_basis_outside i a hi,zero_div,zero_mul]

set_option maxHeartbeats 800000 in
theorem short_low_small_basis_orthogonal :
    shortLowSmallBasis * shortLowSmallBasisᵀ = (1:Matrix (Fin 7) (Fin 7) ℝ) := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [shortLowSmallBasis,shortLowRowIndex,shortLowBasis,shortHeadFrequency,
      Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Matrix.one_apply] <;>
    field_simp <;> nlinarith

noncomputable def shortLowRotationArray : Matrix (Fin 7) (Fin 7) ℝ :=
  let t := 1/Real.sqrt 2
  ![![1,0,0,0,0,0,0],![0,t,0,t,0,0,0],![0,0,1,0,0,0,0],
    ![0,t,0,-t,0,0,0],![0,0,0,0,1,0,0],![0,0,0,0,0,1,0],![0,0,0,0,0,0,1]]

noncomputable def shortLowShearPerturbationArray : Matrix (Fin 7) (Fin 7) ℝ :=
  ![![0,0,-(1/7:ℝ),0,0,0,0],![0,0,0,0,0,0,0],![0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0],![0,0,0,0,0,0,0],![0,0,0,0,0,0,0],![0,0,0,0,0,0,0]]

theorem short_low_rotation_array : shortLowRotation = shortLowRotationArray := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [shortLowRotation,shortLowRotationArray,Fin.ext_iff] <;> ring

theorem short_low_shear_perturbation_array : shortLowShearPerturbation = shortLowShearPerturbationArray := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [shortLowShearPerturbation,shortLowShearPerturbationArray,Fin.ext_iff]

set_option maxHeartbeats 800000 in
theorem short_low_rotation_involution :
    shortLowRotation * shortLowRotation = (1:Matrix (Fin 7) (Fin 7) ℝ) := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  ext i k
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases k <;>
    norm_num [short_low_rotation_array,shortLowRotationArray,Fin.sum_univ_succ,
      Matrix.one_apply,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.ext_iff] <;>
    field_simp <;> nlinarith

theorem short_low_shear_inverse :
    shortLowShear * ((1:Matrix (Fin 7) (Fin 7) ℝ)-shortLowShearPerturbation) = 1 := by
  have hn : shortLowShearPerturbation*shortLowShearPerturbation = 0 := by
    ext i k
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases k <;>
      norm_num [short_low_shear_perturbation_array,shortLowShearPerturbationArray,
        Fin.sum_univ_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.ext_iff]
  unfold shortLowShear
  rw [add_mul,mul_sub,mul_sub,Matrix.one_mul,Matrix.mul_one,hn]
  simp only [Matrix.one_mul]
  abel

theorem short_low_small_inverse_right : shortLowSmallMatrix * shortLowSmallInverse = 1 := by
  have hd : diagonal (fun i => 1/shortLowSmallWeight i) * diagonal shortLowSmallWeight =
      (1:Matrix (Fin 7) (Fin 7) ℝ) := by
    rw [diagonal_mul_diagonal]
    ext i k
    simp only [Matrix.diagonal_apply,Matrix.one_apply]
    split_ifs with hik
    · subst k; exact one_div_mul_cancel (ne_of_gt (short_low_small_weight_pos i))
    · rfl
  unfold shortLowSmallMatrix shortLowSmallInverse
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc shortLowRotation,short_low_rotation_involution,Matrix.one_mul]
  rw [← Matrix.mul_assoc shortLowShear,short_low_shear_inverse,Matrix.one_mul]
  rw [← Matrix.mul_assoc shortLowSmallBasis,short_low_small_basis_orthogonal,Matrix.one_mul]
  exact hd

theorem short_low_row_index_injective : Function.Injective shortLowRowIndex := by
  intro i k hik
  apply Fin.ext
  have hh := congrArg Fin.val hik
  dsimp only [shortLowRowIndex] at hh
  omega

theorem short_low_row_index_range (i : Fin 15) :
    (∃ k, shortLowRowIndex k = i) ↔ 4 ≤ i.val ∧ i.val ≤ 10 := by
  constructor
  · rintro ⟨k,rfl⟩
    dsimp only [shortLowRowIndex]
    constructor <;> omega
  · intro hi
    refine ⟨⟨i.val-4,by omega⟩,?_⟩
    apply Fin.ext
    dsimp only [shortLowRowIndex]
    omega

theorem short_low_embedding_surjective (q : Fin 15 → ℂ)
    (hq : ∀ i, i.val < 4 ∨ 10 < i.val → q i = 0) :
    ∃ x : Fin 7 → ℂ, ∀ i : Fin 15, (∑ k : Fin 7, (shortLowEmbedding i k:ℂ)*x k) = q i := by
  let A := shortLowSmallMatrix.map Complex.ofRealHom
  let B := shortLowSmallInverse.map Complex.ofRealHom
  have hAB : A*B = (1:Matrix (Fin 7) (Fin 7) ℂ) := by
    rw [← Matrix.map_mul,short_low_small_inverse_right]
    ext i k
    simp only [Matrix.map_apply,Matrix.one_apply]
    split_ifs <;> simp only [map_zero,map_one]
  let x := B *ᵥ (fun i => q (shortLowRowIndex i))
  have hx : A *ᵥ x = fun i => q (shortLowRowIndex i) := by
    rw [show x = B *ᵥ (fun i => q (shortLowRowIndex i)) from rfl,
      Matrix.mulVec_mulVec,hAB,Matrix.one_mulVec]
  refine ⟨x,fun i => ?_⟩
  by_cases hi : 4 ≤ i.val ∧ i.val ≤ 10
  · obtain ⟨a,rfl⟩ := (short_low_row_index_range i).mpr hi
    have hh := congrFun hx a
    simpa only [Matrix.mulVec,dotProduct,A,Matrix.map_apply,short_low_embedding_restrict,
      Complex.ofRealHom_eq_coe] using hh
  · have hout : i.val < 4 ∨ 10 < i.val := by omega
    rw [hq i hout]
    apply sum_eq_zero
    intro k _
    rw [short_low_embedding_outside i k hout,Complex.ofReal_zero,zero_mul]

end Lemniscate
