import Lemniscate.SineConstrainedForm

/-! Finite first-mode/tail block forms converge to the complete H2 coefficient
form. The coupling series is obtained from the actual l2 inner product. -/
namespace Lemniscate.CoarseArithmetic
open Complex Filter
open scoped ComplexConjugate Topology

noncomputable def sineCouplingPartial (I : Finset ℕ) (v : ℕ → ℂ) : ℂ :=
  ∑ j ∈ I, (sineMatrixEntry thetaParameter nome 1 (j+2):ℂ)*v j

noncomputable def sineFiniteBlockPairing (I : Finset ℕ) (u : ℂ) (v : ℕ → ℂ) : ℂ :=
  conj u*(sineMatrixEntry thetaParameter nome 1 1:ℂ)*u +
    (∑ j ∈ I, conj u*(sineMatrixEntry thetaParameter nome 1 (j+2):ℂ)*v j) +
    (∑ i ∈ I, conj (v i)*(sineMatrixEntry thetaParameter nome (i+2) 1:ℂ)*u) +
    ∑ i ∈ I, ∑ j ∈ I, sineTailEnergyTerm v (i,j)

theorem sine_finite_block_pairing_re (I : Finset ℕ) (u : ℂ) (v : ℕ → ℂ) :
    (sineFiniteBlockPairing I u v).re =
      sineMatrixEntry thetaParameter nome 1 1*‖u‖^2 +
        2*(conj u*sineCouplingPartial I v).re +
        (∑ i ∈ I, ∑ j ∈ I, sineTailEnergyTerm v (i,j)).re := by
  have hrow : (∑ j ∈ I, conj u*(sineMatrixEntry thetaParameter nome 1 (j+2):ℂ)*v j) =
      conj u*sineCouplingPartial I v := by
    rw [sineCouplingPartial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hcol : (∑ i ∈ I, conj (v i)*(sineMatrixEntry thetaParameter nome (i+2) 1:ℂ)*u) =
      conj (conj u*sineCouplingPartial I v) := by
    simp only [sineCouplingPartial, map_mul, map_sum, Complex.conj_conj,
      Complex.conj_ofReal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [sine_matrix_symmetric thetaParameter nome (j+2) 1]
    ring
  have hnorm : conj u*u = ((‖u‖^2:ℝ):ℂ) := by
    rw [Complex.conj_mul', ← Complex.ofReal_pow]
  have hd : (conj u*(sineMatrixEntry thetaParameter nome 1 1:ℂ)*u).re =
      sineMatrixEntry thetaParameter nome 1 1*‖u‖^2 := by
    calc
      _ = ((sineMatrixEntry thetaParameter nome 1 1:ℂ)*(conj u*u)).re := by congr 1; ring
      _ = _ := by rw [hnorm, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [sineFiniteBlockPairing, hrow, hcol, Complex.add_re, Complex.conj_re, hd]
  ring

theorem sine_coupling_partial_tendsto (v : SineTailSpace) :
    Tendsto (fun I : Finset ℕ => sineCouplingPartial I v) atTop
      (𝓝 (inner ℂ sineCouplingVector v)) := by
  change HasSum (fun j : ℕ => (sineMatrixEntry thetaParameter nome 1 (j+2):ℂ)*v j)
    (inner ℂ sineCouplingVector v)
  have h := lp.hasSum_inner (𝕜 := ℂ) sineCouplingVector v
  simpa only [sineCouplingPartial, sineCouplingVector, RCLike.inner_apply',
    Complex.conj_ofReal] using h

theorem sine_finite_block_form_tendsto (u : ℂ) (v : SineTailSpace)
    (hv : HasSineTailH2Coefficients v) :
    Tendsto (fun I : Finset ℕ => (sineFiniteBlockPairing I u v).re)
      atTop (𝓝 (sineH2BlockForm u v)) := by
  have hc := (Complex.continuous_re.tendsto _).comp
    ((sine_coupling_partial_tendsto v).const_mul (conj u))
  have ht := (Complex.continuous_re.tendsto _).comp (sine_tail_energy_tendsto v hv)
  simpa only [sine_finite_block_pairing_re, sineH2BlockForm, sineTailH2Form,
    Function.comp_def] using
    ((hc.const_mul 2).const_add (sineMatrixEntry thetaParameter nome 1 1*‖u‖^2)).add ht

end Lemniscate.CoarseArithmetic
