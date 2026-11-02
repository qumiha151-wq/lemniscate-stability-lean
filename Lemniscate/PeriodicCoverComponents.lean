import Lemniscate.PeriodicCoverFourier

/-! Every nonzero function has a nonzero centered Bloch component. Only
this consequence of completeness is needed for the lower spectral bound. -/
namespace Lemniscate
open Complex MeasureTheory

private theorem centered_cover_index (M : ℕ) (hM : 0 < M) (n : ℤ) :
    ∃ j k : ℤ, 2*|j| ≤ (M:ℤ) ∧ circleCoverIndex M j k = n := by
  have hMz : (0:ℤ) < M := by exact_mod_cast hM
  have hr0 := Int.emod_nonneg n (ne_of_gt hMz)
  have hrM := Int.emod_lt_of_pos n hMz
  have hdiv := Int.mul_ediv_add_emod n (M:ℤ)
  by_cases h : 2*(n%(M:ℤ)) ≤ (M:ℤ)
  · refine ⟨n%(M:ℤ),n/(M:ℤ),?_,hdiv⟩
    rwa [abs_of_nonneg hr0]
  · refine ⟨n%(M:ℤ)-(M:ℤ),n/(M:ℤ)+1,?_,?_⟩
    · rw [abs_of_neg (by omega)]
      omega
    · unfold circleCoverIndex
      calc
        _ = (M:ℤ)*(n/(M:ℤ))+n%(M:ℤ) := by ring
        _ = n := hdiv

theorem circle_cover_parameter_bound (M : ℕ) (hM : 0 < M) (j : ℤ)
    (hj : 2*|j| ≤ (M:ℤ)) : |(j:ℝ)/(M:ℝ)| ≤ 1/2 := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hr : 2*|(j:ℝ)| ≤ (M:ℝ) := by exact_mod_cast hj
  rw [abs_div,abs_of_pos hMr,div_le_iff₀ hMr]
  linarith only [hr]

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

theorem circle_cover_nonzero_component (M : ℕ) (hM : 0 < M)
    (f : CircleL2 S) (hf : f ≠ 0) :
    ∃ j : ℤ, 2*|j| ≤ (M:ℤ) ∧ circleCoverComponent T S M hM j f ≠ 0 := by
  have hc : ∃ n : ℤ, fourierCoeff f n ≠ 0 := by
    by_contra! h
    apply hf
    apply circle_fourier_ext S
    intro n
    rw [h n,circle_fourierCoeff_zero]
  obtain ⟨n,hn⟩ := hc
  obtain ⟨j,k,hj,hindex⟩ := centered_cover_index M hM n
  refine ⟨j,hj,?_⟩
  intro hz
  have h := congrArg (fun v : CircleL2 T => fourierCoeff v k) hz
  rw [circle_cover_component_fourier,circle_fourierCoeff_zero,hindex] at h
  exact hn h

end Lemniscate
