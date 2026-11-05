import Lemniscate.ShortSchurCoefficients
import Lemniscate.ShortSchurKernel

/-! The finite external Fourier columns are genuine untruncated entries.
Both this calculation and the analytic tail use half-frequency indices. -/
namespace Lemniscate

def shortOutsideHalfFrequency (j : Fin 14) : ℤ :=
  if j.val < 7 then (j.val : ℤ)-14 else (j.val : ℤ)+1

def shortHighHalfFrequency (j : Fin 22) : ℤ :=
  if j.val < 11 then (j.val : ℤ)-14 else (j.val : ℤ)-7

theorem short_high_half_frequency_bounds (j : Fin 22) :
    (-14 ≤ shortHighHalfFrequency j ∧ shortHighHalfFrequency j ≤ -4) ∨
      (4 ≤ shortHighHalfFrequency j ∧ shortHighHalfFrequency j ≤ 14) := by
  unfold shortHighHalfFrequency
  split_ifs <;> omega

def shortHighLookup (j : Fin 22) : Fin 15 ⊕ Fin 14 :=
  let n := shortHighHalfFrequency j
  if hn : -7 ≤ n ∧ n ≤ 7 then .inl ⟨(n+7).toNat, by omega⟩
  else if hs : n < 0 then .inr ⟨(n+14).toNat, by
    have hb := short_high_half_frequency_bounds j
    omega⟩
  else .inr ⟨(n-1).toNat, by
    have hb := short_high_half_frequency_bounds j
    omega⟩

theorem short_high_lookup_spec (j : Fin 22) :
    match shortHighLookup j with
    | .inl i => shortHeadIndex (shortHighHalfFrequency j) = some i
    | .inr k => shortHeadIndex (shortHighHalfFrequency j) = none ∧
        shortOutsideHalfFrequency k = shortHighHalfFrequency j := by
  unfold shortHighLookup
  dsimp only
  split_ifs with hn hs
  · simp only [shortHeadIndex, dif_pos hn]
  · constructor
    · simp only [shortHeadIndex, dif_neg hn]
    · have hb := short_high_half_frequency_bounds j
      dsimp only [shortOutsideHalfFrequency]
      split_ifs <;> omega
  · constructor
    · simp only [shortHeadIndex, dif_neg hn]
    · have hb := short_high_half_frequency_bounds j
      dsimp only [shortOutsideHalfFrequency]
      split_ifs <;> omega

end Lemniscate

namespace Lemniscate.CoarseArithmetic
open Matrix

noncomputable def shortOutsideForward (k : Fin 5) : Matrix (Fin 15) (Fin 14) ℝ :=
  fun i j => shortBlochEntry lemniscateFrequencySquared shortActualCoefficient k
    (shortHeadFrequency i) (2*shortOutsideHalfFrequency j)

noncomputable def shortOutsideBackward (k : Fin 5) : Matrix (Fin 15) (Fin 14) ℝ :=
  fun i j => shortBlochEntry lemniscateFrequencySquared shortActualCoefficient k
    (2*shortOutsideHalfFrequency j) (shortHeadFrequency i)

def shortOutsideForwardInput (k : Fin 5) (i : Fin 15) (j : Fin 14) : Interval :=
  shortBlochEntryInput k (shortHeadFrequency i) (2*shortOutsideHalfFrequency j)

def shortOutsideBackwardInput (k : Fin 5) (i : Fin 15) (j : Fin 14) : Interval :=
  shortBlochEntryInput k (2*shortOutsideHalfFrequency j) (shortHeadFrequency i)

theorem short_outside_forward_input_sound (k : Fin 5) :
    MatrixContains (shortOutsideForwardInput k) (shortOutsideForward k) :=
  fun _ _ => short_bloch_entry_input_sound k _ _

theorem short_outside_backward_input_sound (k : Fin 5) :
    MatrixContains (shortOutsideBackwardInput k) (shortOutsideBackward k) :=
  fun _ _ => short_bloch_entry_input_sound k _ _

noncomputable def shortRawOutsideBernstein (j : Fin 5) : Matrix (Fin 14) (Fin 14) ℝ :=
  fun n m => shortRawBernsteinEntry lemniscateFrequencySquared shortActualCoefficient j
    (shortOutsideHalfFrequency n) (shortOutsideHalfFrequency m)

def shortRawOutsideBernsteinInput (j : Fin 5) (n m : Fin 14) : Interval :=
  let N := 2*shortOutsideHalfFrequency n
  let M := 2*shortOutsideHalfFrequency m
  add (point (if N=M then (1/2:ℚ) else 0))
    ⟨∑ k : Fin 5, (scale (scale (add (shortBlochEntryInput k N M)
        (shortBlochEntryInput k M N)) (1/2)) (shortBernsteinWeight j k)).lo,
     ∑ k : Fin 5, (scale (scale (add (shortBlochEntryInput k N M)
        (shortBlochEntryInput k M N)) (1/2)) (shortBernsteinWeight j k)).hi⟩

theorem short_raw_outside_bernstein_input_sound (j : Fin 5) :
    MatrixContains (shortRawOutsideBernsteinInput j) (shortRawOutsideBernstein j) := by
  intro n m
  have hsum := sum_interval_sound _ _ (fun k : Fin 5 => scale_sound _ _ (shortBernsteinWeight j k)
    (scale_sound _ _ (1/2) (add_sound _ _ _ _
      (short_bloch_entry_input_sound k (2*shortOutsideHalfFrequency n) (2*shortOutsideHalfFrequency m))
      (short_bloch_entry_input_sound k (2*shortOutsideHalfFrequency m) (2*shortOutsideHalfFrequency n)))))
  have hdelta : Contains (point (if 2*shortOutsideHalfFrequency n=2*shortOutsideHalfFrequency m
      then (1/2:ℚ) else 0)) (if shortOutsideHalfFrequency n=shortOutsideHalfFrequency m
      then (1/2:ℝ) else 0) := by
    by_cases hnm : shortOutsideHalfFrequency n=shortOutsideHalfFrequency m
    · simp only [hnm, ite_true]
      simpa using point_sound (1/2)
    · have hnm' : 2*shortOutsideHalfFrequency n≠2*shortOutsideHalfFrequency m := by omega
      simp only [if_neg hnm, if_neg hnm']
      simpa using point_sound 0
  have hresult := add_sound _ _ _ _ hdelta hsum
  have heq : shortRawOutsideBernstein j n m =
      (if shortOutsideHalfFrequency n=shortOutsideHalfFrequency m then (1/2:ℝ) else 0) +
      (∑ k : Fin 5, ((shortBlochEntry lemniscateFrequencySquared shortActualCoefficient k
          (2*shortOutsideHalfFrequency n) (2*shortOutsideHalfFrequency m) +
        shortBlochEntry lemniscateFrequencySquared shortActualCoefficient k
          (2*shortOutsideHalfFrequency m) (2*shortOutsideHalfFrequency n))*((1/2:ℚ):ℝ))*
          (shortBernsteinWeight j k : ℝ)) := by
    unfold shortRawOutsideBernstein shortRawBernsteinEntry
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  rw [heq]
  exact hresult

end Lemniscate.CoarseArithmetic
