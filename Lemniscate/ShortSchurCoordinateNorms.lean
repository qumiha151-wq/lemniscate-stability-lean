import Lemniscate.ShortSchurCoordinateMap
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

namespace Lemniscate
open Matrix Finset Complex
open scoped ComplexConjugate

noncomputable def shortLowWeightedSmallMatrix : Matrix (Fin 7) (Fin 7) ℝ :=
  shortLowSmallBasis * (shortLowShear * shortLowRotation)

def shortLowShearGramRat : Matrix (Fin 7) (Fin 7) ℚ :=
  ![![1,0,-(1/7:ℚ),0,0,0,0],![0,1,0,0,0,0,0],![ -(1/7:ℚ),0,50/49,0,0,0,0],
    ![0,0,0,1,0,0,0],![0,0,0,0,1,0,0],![0,0,0,0,0,1,0],![0,0,0,0,0,0,1]]

noncomputable def shortLowShearGram : Matrix (Fin 7) (Fin 7) ℝ :=
  fun i k => (shortLowShearGramRat i k:ℝ)

noncomputable def shortLowShearArray : Matrix (Fin 7) (Fin 7) ℝ :=
  ![![1,0,-(1/7:ℝ),0,0,0,0],![0,1,0,0,0,0,0],![0,0,1,0,0,0,0],
    ![0,0,0,1,0,0,0],![0,0,0,0,1,0,0],![0,0,0,0,0,1,0],![0,0,0,0,0,0,1]]

theorem short_low_shear_array : shortLowShear = shortLowShearArray := by
  ext i k
  change (if i=k then (1:ℝ) else 0) +
    (if i=0 ∧ k=2 then -(1/7:ℝ) else 0) = shortLowShearArray i k
  fin_cases i <;> fin_cases k <;> norm_num [shortLowShearArray,Fin.ext_iff]

set_option maxRecDepth 10000 in
theorem short_low_shear_rotation_commute :
    shortLowShear*shortLowRotation = shortLowRotation*shortLowShear := by
  ext i k
  rw [Matrix.mul_apply,Matrix.mul_apply]
  fin_cases i <;> fin_cases k <;>
    norm_num [short_low_shear_array,shortLowShearArray,
      short_low_rotation_array,shortLowRotationArray,
      Matrix.add_apply,Matrix.one_apply,Fin.sum_univ_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.ext_iff]

theorem short_low_rotation_symmetric : shortLowRotationᵀ = shortLowRotation := by
  ext i k
  change shortLowRotation k i = shortLowRotation i k
  fin_cases i <;> fin_cases k <;>
    norm_num [Matrix.transpose_apply,short_low_rotation_array,shortLowRotationArray,Fin.ext_iff]

set_option maxRecDepth 10000 in
theorem short_low_shear_gram : shortLowShearᵀ * shortLowShear = shortLowShearGram := by
  ext i k
  rw [Matrix.mul_apply]
  change (∑ a : Fin 7,shortLowShear a i*shortLowShear a k) = shortLowShearGram i k
  fin_cases i <;> fin_cases k <;>
    norm_num [short_low_shear_array,shortLowShearArray,
      shortLowShearGram,shortLowShearGramRat,Matrix.transpose_apply,Matrix.add_apply,Matrix.one_apply,
      Fin.sum_univ_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.ext_iff]

theorem short_low_weighted_gram :
    shortLowWeightedSmallMatrixᵀ*shortLowWeightedSmallMatrix = shortLowShearGram := by
  have hb : shortLowSmallBasisᵀ*shortLowSmallBasis = (1:Matrix (Fin 7) (Fin 7) ℝ) :=
    mul_eq_one_comm.mp short_low_small_basis_orthogonal
  unfold shortLowWeightedSmallMatrix
  rw [short_low_shear_rotation_commute,Matrix.transpose_mul,Matrix.transpose_mul,
    short_low_rotation_symmetric]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc shortLowSmallBasisᵀ,hb,Matrix.one_mul]
  rw [← Matrix.mul_assoc shortLowRotation,short_low_rotation_involution,Matrix.one_mul]
  exact short_low_shear_gram

theorem short_low_shear_gram_row (i : Fin 7) :
    shortLowShearGram i i + (∑ k : Fin 7, if k=i then 0 else |shortLowShearGram i k|) ≤ (7/6:ℝ) := by
  have hrat : ∀ a : Fin 7, shortLowShearGramRat a a +
      (∑ k : Fin 7, if k=a then 0 else |shortLowShearGramRat a k|) ≤ (7/6:ℚ) := by
    decide +kernel
  have hh := (Rat.cast_le (K := ℝ)).mpr (hrat i)
  have heq : shortLowShearGram i i + (∑ k : Fin 7, if k=i then 0 else |shortLowShearGram i k|) =
      ((shortLowShearGramRat i i + (∑ k : Fin 7, if k=i then 0 else |shortLowShearGramRat i k|):ℚ):ℝ) := by
    simp only [Rat.cast_add,Rat.cast_sum,shortLowShearGram]
    congr 1
    apply sum_congr rfl
    intro k _
    by_cases h : k=i <;> simp only [h,ite_true,ite_false,Rat.cast_zero,Rat.cast_abs]
  rw [heq]
  simpa only [Rat.cast_div,Rat.cast_ofNat] using hh

theorem short_low_shear_gram_symmetric (i k : Fin 7) :
    shortLowShearGram i k = shortLowShearGram k i := by
  fin_cases i <;> fin_cases k <;> norm_num [shortLowShearGram,shortLowShearGramRat]

theorem short_real_matrix_norm_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (x : κ → ℂ) :
    (∑ i : ι, ‖∑ k : κ, (M i k:ℂ)*x k‖^2) =
      (∑ k : κ, ∑ l : κ, conj (x k)*((Mᵀ*M) k l:ℂ)*x l).re := by
  let A := M.map Complex.ofRealHom
  have hc : (fun i => conj ((A *ᵥ x) i)) = A *ᵥ (fun k => conj (x k)) := by
    funext i
    simp only [Matrix.mulVec,dotProduct,A,Matrix.map_apply,map_sum,map_mul,Complex.conj_ofReal,
      Complex.ofRealHom_eq_coe]
  have hG : Aᵀ*A = (Mᵀ*M).map Complex.ofRealHom := by
    rw [Matrix.map_mul]
    rfl
  have hdot : (fun i => conj ((A *ᵥ x) i)) ⬝ᵥ (A *ᵥ x) =
      (fun k => conj (x k)) ⬝ᵥ ((Aᵀ*A) *ᵥ x) := by
    rw [hc,Matrix.dotProduct_mulVec,Matrix.vecMul_mulVec,← Matrix.dotProduct_mulVec]
  have hleft : ((fun i => conj ((A *ᵥ x) i)) ⬝ᵥ (A *ᵥ x)).re =
      ∑ i : ι, ‖∑ k : κ, (M i k:ℂ)*x k‖^2 := by
    change Complex.reCLM (∑ i : ι, conj ((A *ᵥ x) i)*(A *ᵥ x) i) = _
    simp only [map_sum,Complex.conj_mul',Complex.reCLM_apply,← Complex.ofReal_pow,Complex.ofReal_re]
    simp only [Matrix.mulVec,dotProduct,A,Matrix.map_apply,Complex.ofRealHom_eq_coe]
  rw [← hleft,hdot,hG]
  simp only [Matrix.mulVec,dotProduct,Matrix.map_apply,mul_sum,Complex.ofRealHom_eq_coe,mul_assoc]

theorem short_low_weighted_small_norm (x : Fin 7 → ℂ) :
    (∑ i : Fin 7, ‖∑ k : Fin 7, (shortLowWeightedSmallMatrix i k:ℂ)*x k‖^2) ≤
      (7/6:ℝ)*(∑ k : Fin 7, ‖x k‖^2) := by
  rw [short_real_matrix_norm_square,short_low_weighted_gram]
  have hh := CoarseArithmetic.short_real_symmetric_row_form univ shortLowShearGram (fun _ => 1) x (-(7/6))
    (by intro _ _; norm_num) short_low_shear_gram_symmetric (by
      intro i _
      simpa only [div_self (by norm_num : (1:ℝ)≠0),mul_one,neg_neg] using short_low_shear_gram_row i)
  simpa only [neg_neg] using hh

theorem short_low_weighted_small_entry (i k : Fin 7) :
    shortLowWeightedSmallMatrix i k = shortLowSmallWeight i*shortLowEmbedding (shortLowRowIndex i) k := by
  rw [short_low_embedding_restrict]
  unfold shortLowWeightedSmallMatrix shortLowSmallMatrix
  rw [Matrix.mul_apply,Matrix.mul_apply]
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  rw [Matrix.diagonal_mul]
  field_simp [ne_of_gt (short_low_small_weight_pos i)]

theorem short_low_weighted_embedding_norm (x : Fin 7 → ℂ) :
    (∑ i : Fin 15, ‖((max (1:ℝ) ((shortHeadFrequency i:ℝ)^2):ℝ):ℂ)*
      (∑ k : Fin 7, (shortLowEmbedding i k:ℂ)*x k)‖^2) ≤
      (7/6:ℝ)*(∑ k : Fin 7, ‖x k‖^2) := by
  let f (i : Fin 15) : ℝ := ‖((max (1:ℝ) ((shortHeadFrequency i:ℝ)^2):ℝ):ℂ)*
      (∑ k : Fin 7, (shortLowEmbedding i k:ℂ)*x k)‖^2
  have hsum : (∑ i : Fin 15, f i) = ∑ i : Fin 7, f (shortLowRowIndex i) := by
    have hsub : univ.image shortLowRowIndex ⊆ (univ:Finset (Fin 15)) := subset_univ _
    have hs := Finset.sum_subset (f := f) hsub (by
      intro i _ hi
      have hout : i.val < 4 ∨ 10 < i.val := by
        have hnot : ¬∃ k,shortLowRowIndex k=i := by simpa only [mem_image,mem_univ,true_and] using hi
        have hh : ¬(4 ≤ i.val ∧ i.val ≤ 10) := fun h => hnot ((short_low_row_index_range i).mpr h)
        omega
      have hz : (∑ k : Fin 7, (shortLowEmbedding i k:ℂ)*x k) = 0 := by
        apply sum_eq_zero
        intro k _
        rw [short_low_embedding_outside i k hout,Complex.ofReal_zero,zero_mul]
      simp only [f,hz,mul_zero,norm_zero,zero_pow (by decide : 2≠0)])
    rw [← hs,Finset.sum_image (fun i _ k _ hik => short_low_row_index_injective hik)]
  change (∑ i : Fin 15, f i) ≤ _
  rw [hsum]
  have heq (i : Fin 7) : f (shortLowRowIndex i) =
      ‖∑ k : Fin 7, (shortLowWeightedSmallMatrix i k:ℂ)*x k‖^2 := by
    dsimp only [f]
    rw [mul_sum]
    apply congrArg (fun z : ℂ => ‖z‖^2)
    apply sum_congr rfl
    intro k _
    rw [short_low_weighted_small_entry,Complex.ofReal_mul]
    simp only [shortLowSmallWeight,mul_assoc]
  simp only [heq]
  exact short_low_weighted_small_norm x

end Lemniscate
