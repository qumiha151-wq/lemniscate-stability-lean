import Lemniscate.CoefficientMajorant

/-! Uniform entry bounds for both signs in the positive-frequency cosine/sine
formula. These are bounds on the concrete convergent coefficient formulas;
their identification with the differential operator is a separate obligation. -/
namespace Lemniscate.CoarseArithmetic

theorem two_coefficient_majorant (r d s ε n m B : ℝ)
    (hr : 0 ≤ r) (hn : 0 ≤ n) (hm : 0 ≤ m)
    (hd : |d| ≤ B) (hs : |s| ≤ B) (hε : |ε| ≤ 1) :
    |r*(d*(45*n*m-(15/4:ℝ)*(n-m)^2)+
      ε*s*(-45*n*m-(15/4:ℝ)*(n+m)^2))| ≤
    45*r*B*(2*n*m+(n^2+m^2)/6) := by
  have hB : 0 ≤ B := (abs_nonneg d).trans hd
  have hminus : |45*n*m-(15/4:ℝ)*(n-m)^2| ≤
      45*n*m+(15/4:ℝ)*(n-m)^2 := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg hn hm]
    · nlinarith [sq_nonneg (n-m)]
  have hplus : |-45*n*m-(15/4:ℝ)*(n+m)^2| =
      45*n*m+(15/4:ℝ)*(n+m)^2 := by
    rw [show -45*n*m-(15/4:ℝ)*(n+m)^2 = -(45*n*m+(15/4:ℝ)*(n+m)^2) by ring,
      abs_neg, abs_of_nonneg (by positivity)]
  have hfirst : |d*(45*n*m-(15/4:ℝ)*(n-m)^2)| ≤
      B*(45*n*m+(15/4:ℝ)*(n-m)^2) := by
    rw [abs_mul]
    exact mul_le_mul hd hminus (abs_nonneg _) hB
  have hsecond : |ε*s*(-45*n*m-(15/4:ℝ)*(n+m)^2)| ≤
      B*(45*n*m+(15/4:ℝ)*(n+m)^2) := by
    rw [abs_mul, abs_mul, hplus]
    have hp : |ε| * |s| ≤ B := by
      simpa only [one_mul] using mul_le_mul hε hs (abs_nonneg s) (by norm_num : (0:ℝ) ≤ 1)
    exact mul_le_mul_of_nonneg_right hp (by positivity)
  calc
    _ = r*|d*(45*n*m-(15/4:ℝ)*(n-m)^2)+
        ε*s*(-45*n*m-(15/4:ℝ)*(n+m)^2)| := by rw [abs_mul, abs_of_nonneg hr]
    _ ≤ r*(B*(45*n*m+(15/4:ℝ)*(n-m)^2)+
        B*(45*n*m+(15/4:ℝ)*(n+m)^2)) :=
      mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hfirst hsecond)) hr
    _ = _ := by ring

noncomputable def positiveFrequencyEntry (r q ε : ℝ) (j k : ℕ) : ℝ :=
  let n : ℝ := 2*(j:ℝ)
  let m : ℝ := 2*(k:ℝ)
  r*(fourierCoefficient r q (j-k+(k-j))*(45*n*m-(15/4:ℝ)*(n-m)^2)+
    ε*fourierCoefficient r q (j+k)*(-45*n*m-(15/4:ℝ)*(n+m)^2))

theorem positive_frequency_upper_tail (ε : ℝ) (j k : ℕ)
    (hε : |ε| ≤ 1) (hjk : j < k) :
    |positiveFrequencyEntry thetaParameter nome ε j k| ≤
      (C:ℝ)*(2*(j:ℝ)+((k-j:ℕ):ℝ))^2*((k-j:ℕ):ℝ)*(qb:ℝ)^(k-j) := by
  let l := k-j
  let B : ℝ := (H:ℝ)*((l:ℝ)*(qb:ℝ)^l)
  have hl : 0 < l := Nat.sub_pos_of_lt hjk
  have hdiff : j-k+(k-j) = l := by dsimp [l]; omega
  have hsum : l ≤ j+k := by dsimp [l]; omega
  have hd : |fourierCoefficient thetaParameter nome (j-k+(k-j))| ≤ B := by
    rw [hdiff]
    exact common_index_coefficient_majorant l l hl le_rfl
  have hs : |fourierCoefficient thetaParameter nome (j+k)| ≤ B :=
    common_index_coefficient_majorant l (j+k) hl hsum
  have hr : 0 ≤ thetaParameter :=
    (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).1
  have hB : 0 ≤ B := (abs_nonneg _).trans hd
  have hb := two_coefficient_majorant thetaParameter
    (fourierCoefficient thetaParameter nome (j-k+(k-j)))
    (fourierCoefficient thetaParameter nome (j+k)) ε (2*(j:ℝ)) (2*(k:ℝ)) B
    hr (by positivity) (by positivity) hd hs hε
  have hk : (k:ℝ) = (j:ℝ)+(l:ℝ) := by
    dsimp [l]
    rw [Nat.cast_sub hjk.le]
    ring
  have hpoly : 45*(2*(2*(j:ℝ))*(2*(k:ℝ))+((2*(j:ℝ))^2+(2*(k:ℝ))^2)/6) ≤
      105*(2*(j:ℝ)+(l:ℝ))^2 := by
    rw [hk]
    nlinarith [sq_nonneg (l:ℝ)]
  calc
    _ ≤ 45*thetaParameter*B*
        (2*(2*(j:ℝ))*(2*(k:ℝ))+((2*(j:ℝ))^2+(2*(k:ℝ))^2)/6) := hb
    _ = thetaParameter*B*(45*
        (2*(2*(j:ℝ))*(2*(k:ℝ))+((2*(j:ℝ))^2+(2*(k:ℝ))^2)/6)) := by ring
    _ ≤ thetaParameter*B*(105*(2*(j:ℝ)+(l:ℝ))^2) :=
      mul_le_mul_of_nonneg_left hpoly (mul_nonneg hr hB)
    _ ≤ (rhi:ℝ)*B*(105*(2*(j:ℝ)+(l:ℝ))^2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).2 hB) (by positivity)
    _ = _ := by simp only [B, l, C, Rat.cast_mul, Rat.cast_ofNat]; ring

theorem cosine_upper_tail (j k : ℕ) (hj : 0 < j) (hjk : j < k) :
    |cosineMatrixEntry thetaParameter nome j k| ≤
      (C:ℝ)*(2*(j:ℝ)+((k-j:ℕ):ℝ))^2*((k-j:ℕ):ℝ)*(qb:ℝ)^(k-j) := by
  have hk : k ≠ 0 := Nat.ne_of_gt (hj.trans hjk)
  have heq : cosineMatrixEntry thetaParameter nome j k =
      positiveFrequencyEntry thetaParameter nome 1 j k := by
    simp [cosineMatrixEntry, positiveFrequencyEntry, Nat.ne_of_gt hj, hk, Nat.ne_of_lt hjk]
  rw [heq]
  exact positive_frequency_upper_tail 1 j k (by norm_num) hjk

end Lemniscate.CoarseArithmetic
