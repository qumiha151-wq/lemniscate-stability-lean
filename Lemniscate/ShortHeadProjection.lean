import Lemniscate.ShortHeadCoefficientIdentification

namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

theorem short_head_pair_add_right {N : ℕ} (v x y : Fin N → ℂ) :
    shortHeadPair v (x+y)=shortHeadPair v x+shortHeadPair v y := by
  simp only [shortHeadPair,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem short_head_pair_smul_right {N : ℕ} (v x : Fin N → ℂ) (c : ℂ) :
    shortHeadPair v (c • x)=c*shortHeadPair v x := by
  simp only [shortHeadPair,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem short_complex_matrix_add {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    shortComplexMatrix (A+B)=shortComplexMatrix A+shortComplexMatrix B := by
  ext i j
  simp [shortComplexMatrix]

theorem short_complex_matrix_smul {m n : ℕ}
    (c : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    shortComplexMatrix (c • A)=(c:ℂ) • shortComplexMatrix A := by
  ext i j
  simp [shortComplexMatrix]

theorem short_complex_matrix_one {N : ℕ} :
    shortComplexMatrix (1 : Matrix (Fin N) (Fin N) ℝ)=1 := by
  ext i j
  simp only [shortComplexMatrix,Matrix.one_apply]
  split_ifs <;> norm_num

noncomputable def shortHeadProjectionMatrix {N : ℕ} (a : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ := fun i j => a i*conj (a j)

theorem short_head_projection_mulVec {N : ℕ} (a v : Fin N → ℂ) :
    shortHeadProjectionMatrix a*ᵥv=shortHeadPair a v • a := by
  funext i
  simp only [shortHeadProjectionMatrix,mulVec,dotProduct,shortHeadPair,Pi.smul_apply,
    smul_eq_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem short_head_projection_sq {N : ℕ} (a : Fin N → ℂ)
    (ha : shortHeadPair a a=1) :
    shortHeadProjectionMatrix a*shortHeadProjectionMatrix a=shortHeadProjectionMatrix a := by
  ext i j
  change (∑ k, a i*conj (a k)*(a k*conj (a j)))=a i*conj (a j)
  calc
    _ = a i*shortHeadPair a a*conj (a j) := by
      simp only [shortHeadPair,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [ha,mul_one]

theorem short_center_matrix_complex : shortComplexMatrix shortCenterProjection=
    shortHeadProjectionMatrix (fun i => (shortAnchorHead i:ℂ)) := by
  ext i j
  simp [shortComplexMatrix,shortCenterProjection,shortOuter,shortHeadProjectionMatrix]

theorem short_stable_matrix_complex : shortComplexMatrix shortStableProjection=
    1-shortComplexMatrix shortCenterProjection := by
  ext i j
  simp [shortComplexMatrix,shortStableProjection,Matrix.one_apply]
  split_ifs <;> norm_num

variable (T : ℝ) [Fact (0<T)]

theorem circle_short_fixed_projection_head (v : Fin 15 → ℂ) :
    circleFixedProjectionH4 T (circleShortHead T v)=
      circleShortHead T (shortComplexMatrix shortCenterProjection*ᵥv) := by
  rw [circleFixedProjectionH4,← circle_householder_anchor_h4_coe T,circle_short_anchor_head,
    circle_short_head_inner,short_center_matrix_complex,short_head_projection_mulVec]
  change shortHeadPair (fun i => (shortAnchorHead i:ℂ)) v •
      circleShortHead T (fun i => (shortAnchorHead i:ℂ)) =
    circleShortHead T (shortHeadPair (fun i => (shortAnchorHead i:ℂ)) v •
      (fun i => (shortAnchorHead i:ℂ)))
  rw [map_smul]

theorem circle_short_stable_projection_head (v : Fin 15 → ℂ) :
    circleShortHead T v-circleFixedProjectionH4 T (circleShortHead T v)=
      circleShortHead T (shortComplexMatrix shortStableProjection*ᵥv) := by
  rw [circle_short_fixed_projection_head,short_stable_matrix_complex,sub_mulVec,one_mulVec,
    map_sub]

theorem short_center_complex_sq :
    shortComplexMatrix shortCenterProjection*shortComplexMatrix shortCenterProjection=
      shortComplexMatrix shortCenterProjection := by
  rw [short_center_matrix_complex]
  apply short_head_projection_sq
  haveI : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
  have h := circle_householder_anchor_unit 1
  rw [← circle_householder_anchor_h4_coe 1,circle_short_anchor_head,
    circle_short_head_inner] at h
  exact h

theorem short_stable_complex_sq :
    shortComplexMatrix shortStableProjection*shortComplexMatrix shortStableProjection=
      shortComplexMatrix shortStableProjection := by
  rw [short_stable_matrix_complex]
  simp only [sub_mul,mul_sub,one_mul,mul_one,short_center_complex_sq]
  abel

end Lemniscate
