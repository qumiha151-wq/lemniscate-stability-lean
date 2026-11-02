import Lemniscate.PeriodicFiniteBlochPolynomial

/-! Real matrices for the finite changes of variables, with exact complex
cast identities. These enable the rational interval calculation. -/
namespace Lemniscate
open Complex Matrix
open scoped ComplexConjugate

noncomputable def realHeadMatrixCast :
    Matrix (Fin 31) (Fin 31) ℝ →+* Matrix (Fin 31) (Fin 31) ℂ :=
  Complex.ofRealHom.mapMatrix

theorem real_head_matrix_cast_apply (M : Matrix (Fin 31) (Fin 31) ℝ) (i j : Fin 31) :
    realHeadMatrixCast M i j = (M i j:ℂ) := rfl

theorem real_head_matrix_cast_smul (x : ℝ) (M : Matrix (Fin 31) (Fin 31) ℝ) :
    realHeadMatrixCast (x • M) = (x:ℂ) • realHeadMatrixCast M := by
  funext i j
  change ((x*M i j:ℝ):ℂ) = (x:ℂ)*(M i j:ℂ)
  exact Complex.ofReal_mul _ _

theorem real_head_matrix_cast_transpose (M : Matrix (Fin 31) (Fin 31) ℝ) :
    realHeadMatrixCast Mᵀ = (realHeadMatrixCast M)ᴴ := by
  funext i j
  change (M j i:ℂ) = conj (M j i:ℂ)
  rw [Complex.conj_ofReal]

noncomputable def realHeadHouseholder (e a : Fin 31 → ℝ) : Matrix (Fin 31) (Fin 31) ℝ :=
  fun i j => (if i = j then 1 else 0)-
    (1+∑ r, e r*a r)⁻¹*(e i+a i)*(e j+a j)

noncomputable def realHeadNeutral (e p : Fin 31 → ℝ) : Matrix (Fin 31) (Fin 31) ℝ :=
  fun i j => (if i = j then 1 else 0)+e i*(p j-e j)

noncomputable def realHeadNeutralInv (e p : Fin 31 → ℝ) : Matrix (Fin 31) (Fin 31) ℝ :=
  fun i j => (if i = j then 1 else 0)-e i*(p j-e j)

theorem real_head_householder_cast (e a : Fin 31 → ℝ) :
    realHeadMatrixCast (realHeadHouseholder e a) =
      headHouseholderMatrix (fun i => (e i:ℂ)) (fun i => (a i:ℂ)) := by
  funext i j
  simp only [real_head_matrix_cast_apply, realHeadHouseholder, headHouseholderMatrix,
    headPair, map_add, Complex.conj_ofReal]
  split_ifs <;> push_cast <;> rfl

theorem real_head_neutral_cast (e p : Fin 31 → ℝ) :
    realHeadMatrixCast (realHeadNeutral e p) =
      headNeutralMatrix (fun i => (e i:ℂ)) (fun i => (p i:ℂ)) := by
  funext i j
  simp only [real_head_matrix_cast_apply, realHeadNeutral, headNeutralMatrix,
    map_sub, Complex.conj_ofReal]
  split_ifs <;> push_cast <;> rfl

theorem real_head_neutral_inv_cast (e p : Fin 31 → ℝ) :
    realHeadMatrixCast (realHeadNeutralInv e p) =
      headNeutralInvMatrix (fun i => (e i:ℂ)) (fun i => (p i:ℂ)) := by
  funext i j
  simp only [real_head_matrix_cast_apply, realHeadNeutralInv, headNeutralInvMatrix,
    map_sub, Complex.conj_ofReal]
  split_ifs <;> push_cast <;> rfl

noncomputable def realHeadHermitianPart (M : Matrix (Fin 31) (Fin 31) ℝ) :
    Matrix (Fin 31) (Fin 31) ℝ := (1/2:ℝ) • (M+Mᵀ)

theorem real_head_hermitian_part_cast (M : Matrix (Fin 31) (Fin 31) ℝ) :
    realHeadMatrixCast (realHeadHermitianPart M) = headHermitianPart (realHeadMatrixCast M) := by
  rw [realHeadHermitianPart, real_head_matrix_cast_smul, map_add,
    real_head_matrix_cast_transpose]
  norm_num [headHermitianPart]

noncomputable def realFiniteHouseholder : Matrix (Fin 31) (Fin 31) ℝ :=
  realHeadHouseholder finiteRotationHead finiteAnchorHead

noncomputable def realFiniteNeutral : Matrix (Fin 31) (Fin 31) ℝ :=
  realHeadNeutral finiteRotationHead finiteAdjointHead

noncomputable def realFiniteNeutralInv : Matrix (Fin 31) (Fin 31) ℝ :=
  realHeadNeutralInv finiteRotationHead finiteAdjointHead

noncomputable def realFiniteAnchorProjection : Matrix (Fin 31) (Fin 31) ℝ :=
  fun i j => finiteAnchorHead i*finiteAnchorHead j

noncomputable def realFiniteStableProjection : Matrix (Fin 31) (Fin 31) ℝ :=
  1-realFiniteAnchorProjection

theorem real_finite_householder_cast :
    realHeadMatrixCast realFiniteHouseholder = finiteHouseholderHeadMatrix :=
  real_head_householder_cast _ _

theorem real_finite_anchor_projection_cast :
    realHeadMatrixCast realFiniteAnchorProjection = finiteAnchorProjection := by
  funext i j
  simp only [real_head_matrix_cast_apply, realFiniteAnchorProjection,
    finiteAnchorProjection, headProjectionMatrix, Complex.conj_ofReal, Complex.ofReal_mul]

theorem real_finite_stable_projection_cast :
    realHeadMatrixCast realFiniteStableProjection = finiteStableProjection := by
  rw [realFiniteStableProjection, map_sub, map_one, real_finite_anchor_projection_cast]
  rfl

noncomputable def realQuarticMatrixBernstein (C : Fin 5 → Matrix (Fin 31) (Fin 31) ℝ)
    (k : Fin 5) : Matrix (Fin 31) (Fin 31) ℝ :=
  ![C 0, C 0+(1/8:ℝ) • C 1,
    C 0+(1/4:ℝ) • C 1+(1/24:ℝ) • C 2,
    C 0+(3/8:ℝ) • C 1+(1/8:ℝ) • C 2+(1/32:ℝ) • C 3,
    C 0+(1/2:ℝ) • C 1+(1/4:ℝ) • C 2+(1/8:ℝ) • C 3+(1/16:ℝ) • C 4] k

theorem real_quartic_matrix_bernstein_cast (C : Fin 5 → Matrix (Fin 31) (Fin 31) ℝ)
    (k : Fin 5) : realHeadMatrixCast (realQuarticMatrixBernstein C k) =
      quarticMatrixBernstein (fun j => realHeadMatrixCast (C j)) k := by
  fin_cases k <;> norm_num [realQuarticMatrixBernstein, quarticMatrixBernstein,
    map_add, real_head_matrix_cast_smul]

end Lemniscate
