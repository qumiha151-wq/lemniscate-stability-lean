import Lemniscate.SineH2Dissipation
import Lemniscate.SineCoupling

/-! The complete coefficient-defined sine block form and its constrained
dissipation. The tail block and coupling estimates are proved, not hypotheses.
Identification with the periodic differential form and geometric rotation
vector remains a separate obligation. -/
namespace Lemniscate.CoarseArithmetic
open Complex
open scoped ComplexConjugate ENNReal

noncomputable def sineH2BlockForm (u : ℂ) (v : SineTailSpace) : ℝ :=
  sineMatrixEntry thetaParameter nome 1 1*‖u‖^2+
    2*(conj u*inner ℂ sineCouplingVector v).re+sineTailH2Form v

theorem sine_tail_space_norm_sq (v : SineTailSpace) :
    ‖v‖^2 = ∑' j : ℕ, ‖v j‖^2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) v
  simpa [Real.rpow_two] using h

theorem sine_tail_space_form_dissipative (v : SineTailSpace)
    (hv : HasSineTailH2Coefficients v) :
    sineTailH2Form v ≤ -100*‖v‖^2 := by
  rw [sine_tail_space_norm_sq]
  exact sine_tail_h2_form_dissipative v hv

theorem sine_h2_block_energy_bound (u : ℂ) (v : SineTailSpace)
    (hv : HasSineTailH2Coefficients v) :
    sineH2BlockForm u v ≤ -100*‖v‖^2+2*63*‖u‖*‖v‖ := by
  have hd : sineMatrixEntry thetaParameter nome 1 1*‖u‖^2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sine_first_diagonal_bound.le.trans (by norm_num)) (sq_nonneg _)
  have ht := sine_tail_space_form_dissipative v hv
  have hc : (conj u*inner ℂ sineCouplingVector v).re ≤ 63*‖u‖*‖v‖ := by
    calc
      _ ≤ ‖conj u*inner ℂ sineCouplingVector v‖ := Complex.re_le_norm _
      _ = ‖u‖*‖inner ℂ sineCouplingVector v‖ := by rw [norm_mul, norm_conj]
      _ ≤ ‖u‖*(63*‖v‖) :=
        mul_le_mul_of_nonneg_left (sine_coupling_pairing_bound v) (norm_nonneg _)
      _ = _ := by ring
  unfold sineH2BlockForm
  linarith

theorem sine_h2_constrained_dissipative (u : ℂ) (v : SineTailSpace)
    (hv : HasSineTailH2Coefficients v)
    (horth : u+inner ℂ sineTailVector v = 0) :
    sineH2BlockForm u v ≤ -75*(‖u‖^2+‖v‖^2) :=
  sine_constraint_energy_bound u v (sineH2BlockForm u v) horth
    (sine_h2_block_energy_bound u v hv)

end Lemniscate.CoarseArithmetic
