import Lemniscate.PeriodicFourierProducts

/-! Fourier coefficients of an absolutely convergent centered even-mode series. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

def evenFourierPair (n : ℕ) : C(AddCircle T, ℂ) :=
  fourier (2*((n+1:ℕ):ℤ)) + fourier (-2*((n+1:ℕ):ℤ)) -
    (2:ℂ) • (1 : C(AddCircle T, ℂ))

theorem even_fourier_pair_norm (n : ℕ) : ‖evenFourierPair T n‖ ≤ 4 := by
  unfold evenFourierPair
  calc
    _ ≤ ‖(fourier (2*((n+1:ℕ):ℤ)) : C(AddCircle T, ℂ)) +
        fourier (-2*((n+1:ℕ):ℤ))‖ + ‖(2:ℂ) • (1 : C(AddCircle T, ℂ))‖ :=
      norm_sub_le _ _
    _ ≤ ‖(fourier (2*((n+1:ℕ):ℤ)) : C(AddCircle T, ℂ))‖ +
        ‖(fourier (-2*((n+1:ℕ):ℤ)) : C(AddCircle T, ℂ))‖ +
        ‖(2:ℂ) • (1 : C(AddCircle T, ℂ))‖ :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ = 4 := by rw [fourier_norm,fourier_norm,norm_smul,norm_one]; norm_num

private theorem even_fourier_pair_coefficient (n : ℕ) (m : ℤ) :
    fourierCoeff (evenFourierPair T n) m =
      (if m = 2*((n+1:ℕ):ℤ) then 1 else 0) +
      (if m = -2*((n+1:ℕ):ℤ) then 1 else 0) -
      2*(if m = 0 then 1 else 0) := by
  simp only [evenFourierPair,circle_continuous_fourier_sub,
    circle_continuous_fourier_add,circle_continuous_fourier_smul,
    circle_continuous_fourier_mode,circle_continuous_fourier_one]

private theorem even_fourier_series_coefficient_hasSum
    (c : ℕ → ℂ) (f : C(AddCircle T, ℂ))
    (hf : HasSum (fun n : ℕ => c n • evenFourierPair T n) (f-1)) (m : ℤ) :
    HasSum (fun n : ℕ => c n * fourierCoeff (evenFourierPair T n) m)
      (fourierCoeff f m - (if m = 0 then 1 else 0)) := by
  simpa only [circle_fourier_clm_apply,circle_continuous_fourier_smul,
    circle_continuous_fourier_sub,circle_continuous_fourier_one] using
    (circleFourierCLM T m).hasSum hf

theorem even_fourier_series_mean
    (c : ℕ → ℂ) (hc : Summable (fun n : ℕ => ‖c n‖))
    (f : C(AddCircle T, ℂ))
    (hf : HasSum (fun n : ℕ => c n • evenFourierPair T n) (f-1)) :
    fourierCoeff f 0 = 1-2*(∑' n : ℕ, c n) := by
  have h := even_fourier_series_coefficient_hasSum T c f hf 0
  have h0 : HasSum (fun n : ℕ => (-2:ℂ)*c n) (fourierCoeff f 0-1) := by
    convert! h using 1
    funext n
    rw [even_fourier_pair_coefficient]
    have hp : (0:ℤ) ≠ 2*((n+1:ℕ):ℤ) := by omega
    have hn : (0:ℤ) ≠ -2*((n+1:ℕ):ℤ) := by omega
    simp only [if_neg hp,if_neg hn,ite_true]
    ring
  have he := h0.unique (hc.of_norm.hasSum.mul_left (-2:ℂ))
  linear_combination he

theorem even_fourier_series_positive
    (c : ℕ → ℂ) (f : C(AddCircle T, ℂ))
    (hf : HasSum (fun n : ℕ => c n • evenFourierPair T n) (f-1)) (j : ℕ) :
    fourierCoeff f (2*((j+1:ℕ):ℤ)) = c j := by
  have hz : (2:ℤ)*((j+1:ℕ):ℤ) ≠ 0 := by omega
  have hn (n : ℕ) : (2:ℤ)*((j+1:ℕ):ℤ) ≠ -2*((n+1:ℕ):ℤ) := by omega
  have h := even_fourier_series_coefficient_hasSum T c f hf (2*((j+1:ℕ):ℤ))
  simp only [if_neg hz,sub_zero] at h
  have hsingle : HasSum (fun n : ℕ => if n = j then c j else 0)
      (fourierCoeff f (2*((j+1:ℕ):ℤ))) := by
    convert! h using 1
    funext n
    rw [even_fourier_pair_coefficient]
    by_cases he : n = j
    · subst n
      simp only [ite_true,if_neg (hn j),if_neg hz]
      ring
    · have hp : (2:ℤ)*((j+1:ℕ):ℤ) ≠ 2*((n+1:ℕ):ℤ) := by omega
      simp only [if_neg he,if_neg hp,if_neg (hn n),if_neg hz,
        mul_zero,add_zero,sub_zero]
  exact hsingle.unique (hasSum_ite_eq j (c j))

theorem even_fourier_series_symmetric
    (c : ℕ → ℂ) (f : C(AddCircle T, ℂ))
    (hf : HasSum (fun n : ℕ => c n • evenFourierPair T n) (f-1)) (m : ℤ) :
    fourierCoeff f (-m) = fourierCoeff f m := by
  have hneg := even_fourier_series_coefficient_hasSum T c f hf (-m)
  have hpos := even_fourier_series_coefficient_hasSum T c f hf m
  have hsame : HasSum (fun n : ℕ => c n * fourierCoeff (evenFourierPair T n) (-m))
      (fourierCoeff f m - (if m = 0 then 1 else 0)) := by
    convert! hpos using 1
    funext n
    congr 1
    rw [even_fourier_pair_coefficient,even_fourier_pair_coefficient]
    have hp : -m = 2*((n+1:ℕ):ℤ) ↔ m = -2*((n+1:ℕ):ℤ) := by omega
    have hn : -m = -2*((n+1:ℕ):ℤ) ↔ m = 2*((n+1:ℕ):ℤ) := by omega
    simp only [hp,hn,neg_eq_zero]
    ring
  have he := hneg.unique hsame
  simp only [neg_eq_zero] at he
  linear_combination he

theorem even_fourier_series_odd
    (c : ℕ → ℂ) (f : C(AddCircle T, ℂ))
    (hf : HasSum (fun n : ℕ => c n • evenFourierPair T n) (f-1))
    (m : ℤ) (hm : Odd m) : fourierCoeff f m = 0 := by
  have hz : m ≠ 0 := by obtain ⟨k,hk⟩ := hm; omega
  have hp (n : ℕ) : m ≠ 2*((n+1:ℕ):ℤ) := by obtain ⟨k,hk⟩ := hm; omega
  have hn (n : ℕ) : m ≠ -2*((n+1:ℕ):ℤ) := by obtain ⟨k,hk⟩ := hm; omega
  have h := even_fourier_series_coefficient_hasSum T c f hf m
  simp only [if_neg hz,sub_zero] at h
  have hzero : HasSum (fun _ : ℕ => (0:ℂ)) (fourierCoeff f m) := by
    convert! h using 1
    funext n
    rw [even_fourier_pair_coefficient]
    simp only [if_neg (hp n),if_neg (hn n),if_neg hz,mul_zero,add_zero,sub_zero]
  exact hzero.unique hasSum_zero

end Lemniscate
