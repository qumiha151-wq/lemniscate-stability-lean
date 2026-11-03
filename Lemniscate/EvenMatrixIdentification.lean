import Lemniscate.RealFiniteBlochSymmetry
import Lemniscate.EvenBernstein0
import Lemniscate.EvenBernstein1
import Lemniscate.EvenBernstein2
import Lemniscate.EvenBernstein3
import Lemniscate.EvenBernstein4

/-! Identification of the interval-certified expressions with the actual
real Bernstein matrices of the finite reduced Bloch form. -/
namespace Lemniscate
open Matrix CoarseArithmetic

theorem even_stage_h0_real : evenStageH0Real = realFiniteSymmetricHead lemniscateFrequencySquared nome 0 := by
  rfl

private theorem real_positive_head_assoc (j : Fin 5) (hj : j ≠ 0) :
    realHeadHermitianPart ((realFiniteHouseholder*realFiniteNeutral*
      evenBlochCoefficientMatrix lemniscateFrequencySquared nome j)*
      (realFiniteNeutralInv*realFiniteHouseholder)) =
      realFiniteSymmetricHead lemniscateFrequencySquared nome j := by
  simp only [realFiniteSymmetricHead, realFiniteBaseHead, if_neg hj, mul_assoc]

theorem even_stage_h1_real : evenStageH1Real = realFiniteSymmetricHead lemniscateFrequencySquared nome 1 :=
  real_positive_head_assoc 1 (by decide)
theorem even_stage_h2_real : evenStageH2Real = realFiniteSymmetricHead lemniscateFrequencySquared nome 2 :=
  real_positive_head_assoc 2 (by decide)
theorem even_stage_h3_real : evenStageH3Real = realFiniteSymmetricHead lemniscateFrequencySquared nome 3 :=
  real_positive_head_assoc 3 (by decide)

theorem even_stage_c0_real : evenStageC0Real = realFiniteBlochCoefficient lemniscateFrequencySquared nome 0 := by
  norm_num [evenStageC0Real, evenStageMain0Real, evenStageCross0Real,
    evenStageZ2P0Real, evenStageZ1PReal, evenStageV1P0Real, evenStageV0PReal,
    evenStageZ2Real, evenStageZ1Real, evenStageV1Real, evenStageV0Real,
    even_stage_h0_real, even_stage_h1_real, even_stage_h2_real,
    realFiniteBlochCoefficient, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> rfl

theorem even_stage_c1_real : evenStageC1Real = realFiniteBlochCoefficient lemniscateFrequencySquared nome 1 := by
  norm_num [evenStageC1Real, evenStageCross1Real,
    evenStageZ2PReal, evenStageV2P0Real, evenStageV1PReal,
    evenStageZ2Real, evenStageV2Real, evenStageV1Real,
    even_stage_h1_real, even_stage_h2_real,
    realFiniteBlochCoefficient, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> rfl

theorem even_stage_c2_real : evenStageC2Real = realFiniteBlochCoefficient lemniscateFrequencySquared nome 2 := by
  norm_num [evenStageC2Real, evenStageMain2Real, evenStageTop0Real, evenStageGram0Real,
    evenStageCross2Real, evenStageZ3PReal, evenStageV3P0Real, evenStageV2PReal,
    evenStageZ3Real, evenStageV3Real, evenStageV2Real,
    even_stage_h2_real, even_stage_h3_real,
    realFiniteBlochCoefficient, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> rfl

theorem even_stage_c3_real : evenStageV3PReal = realFiniteBlochCoefficient lemniscateFrequencySquared nome 3 := by
  norm_num [evenStageV3PReal, evenStageV3Real, even_stage_h3_real,
    realFiniteBlochCoefficient, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> rfl

theorem even_stage_c4_real : evenStageC4Real = realFiniteBlochCoefficient lemniscateFrequencySquared nome 4 := by
  norm_num [evenStageC4Real, evenStageGram1Real,
    realFiniteBlochCoefficient, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> rfl

theorem even_bernstein_0_real : evenBernstein0Real = realFiniteBlochBernstein lemniscateFrequencySquared nome 0 := by
  norm_num [evenBernstein0Real, even_stage_c0_real, realFiniteBlochBernstein,
    realQuarticMatrixBernstein, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> rfl
theorem even_bernstein_1_real : evenBernstein1Real = realFiniteBlochBernstein lemniscateFrequencySquared nome 1 := by
  norm_num [evenBernstein1Real, even_stage_c0_real, even_stage_c1_real,
    realFiniteBlochBernstein, realQuarticMatrixBernstein, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> rfl
theorem even_bernstein_2_real : evenBernstein2Real = realFiniteBlochBernstein lemniscateFrequencySquared nome 2 := by
  norm_num [evenBernstein2Real, even_stage_c0_real, even_stage_c1_real, even_stage_c2_real,
    realFiniteBlochBernstein, realQuarticMatrixBernstein, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> rfl
theorem even_bernstein_3_real : evenBernstein3Real = realFiniteBlochBernstein lemniscateFrequencySquared nome 3 := by
  norm_num [evenBernstein3Real, even_stage_c0_real, even_stage_c1_real, even_stage_c2_real,
    even_stage_c3_real, realFiniteBlochBernstein, realQuarticMatrixBernstein,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> rfl
theorem even_bernstein_4_real : evenBernstein4Real = realFiniteBlochBernstein lemniscateFrequencySquared nome 4 := by
  norm_num [evenBernstein4Real, even_stage_c0_real, even_stage_c1_real, even_stage_c2_real,
    even_stage_c3_real, even_stage_c4_real, realFiniteBlochBernstein, realQuarticMatrixBernstein,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> rfl

theorem actual_even_bernstein_interval (k : Fin 5) :
    MatrixContains (evenBernsteinInterval k) (realFiniteBlochBernstein lemniscateFrequencySquared nome k) := by
  fin_cases k
  · change MatrixContains (evenBernsteinInterval (0:Fin 5))
      (realFiniteBlochBernstein lemniscateFrequencySquared nome 0)
    rw [← even_bernstein_0_real]
    exact even_bernstein_0_sound
  · change MatrixContains (evenBernsteinInterval (1:Fin 5))
      (realFiniteBlochBernstein lemniscateFrequencySquared nome 1)
    rw [← even_bernstein_1_real]
    exact even_bernstein_1_sound
  · change MatrixContains (evenBernsteinInterval (2:Fin 5))
      (realFiniteBlochBernstein lemniscateFrequencySquared nome 2)
    rw [← even_bernstein_2_real]
    exact even_bernstein_2_sound
  · change MatrixContains (evenBernsteinInterval (3:Fin 5))
      (realFiniteBlochBernstein lemniscateFrequencySquared nome 3)
    rw [← even_bernstein_3_real]
    exact even_bernstein_3_sound
  · change MatrixContains (evenBernsteinInterval (4:Fin 5))
      (realFiniteBlochBernstein lemniscateFrequencySquared nome 4)
    rw [← even_bernstein_4_real]
    exact even_bernstein_4_sound

end Lemniscate
