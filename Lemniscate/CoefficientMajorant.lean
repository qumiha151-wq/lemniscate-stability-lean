import Lemniscate.ConcreteCoefficients

/-! The uniform exponential coefficient bound used in matrix tail estimates,
including the monotonicity comparison between sum and difference indices. -/
namespace Lemniscate.CoarseArithmetic

theorem nat_mul_geometric_step (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (n : ℕ) (hn : 1 ≤ n) :
    ((n+1:ℕ):ℝ)*q^(n+1) ≤ (n:ℝ)*q^n := by
  have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_left hq
    (by positivity : 0 ≤ (n:ℝ)+1)
  have hfactor : ((n:ℝ)+1)*q ≤ (n:ℝ) := by nlinarith
  calc
    _ = (((n:ℝ)+1)*q)*q^n := by simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (pow_nonneg hq0 n)

theorem nat_mul_geometric_antitone (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (l m : ℕ) (hl : 1 ≤ l) (hlm : l ≤ m) :
    (m:ℝ)*q^m ≤ (l:ℝ)*q^l := by
  induction m, hlm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    exact (nat_mul_geometric_step q hq0 hq m (hl.trans hm)).trans ih

theorem coefficient_qb_majorant (r q : ℝ) (j : ℕ)
    (hr : Contains ⟨rlo,rhi⟩ r) (hq : Contains ⟨qlo,qhi⟩ q) (hj : 0 < j) :
    0 ≤ fourierCoefficient r q j ∧
    fourierCoefficient r q j ≤ (H:ℝ)*((j:ℝ)*(qb:ℝ)^j) := by
  have hr0 : 0 ≤ r := (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans hr.1
  have hq0 : 0 ≤ q := (by norm_num [qlo] : (0:ℝ) ≤ (qlo:ℝ)).trans hq.1
  have hq1 : q < 1 := hq.2.trans_lt (by norm_num [qhi])
  have hqb : q ≤ (qb:ℝ) := hq.2.trans (by norm_num [qhi, qb])
  have hmono := evenCoefficient_mono r (rhi:ℝ) q (qb:ℝ) j hr0 hr.2 hq0 hqb
    (by norm_num [qb]) hj
  have hbound := evenCoefficient_majorant (rhi:ℝ) (qb:ℝ) j
    (by norm_num [rhi]) (by norm_num [qb]) (by norm_num [qb])
  simp only [fourierCoefficient, if_neg (Nat.ne_of_gt hj)]
  refine ⟨evenCoefficient_nonneg r q j hr0 hq0 hq1, ?_⟩
  simpa only [H, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_sub, Rat.cast_one, Rat.cast_pow] using hmono.trans hbound

theorem theta_nome_coefficient_majorant (j : ℕ) (hj : 0 < j) :
    0 ≤ fourierCoefficient thetaParameter nome j ∧
    fourierCoefficient thetaParameter nome j ≤ (H:ℝ)*((j:ℝ)*(qb:ℝ)^j) :=
  coefficient_qb_majorant _ _ j actual_nome_theta_r_bounds coarse_nome_bounds hj

theorem common_index_coefficient_majorant (l m : ℕ) (hl : 0 < l) (hlm : l ≤ m) :
    |fourierCoefficient thetaParameter nome m| ≤ (H:ℝ)*((l:ℝ)*(qb:ℝ)^l) := by
  have hm := theta_nome_coefficient_majorant m (hl.trans_le hlm)
  rw [abs_of_nonneg hm.1]
  apply hm.2.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num [H, rhi, qb])
  exact nat_mul_geometric_antitone (qb:ℝ) (by norm_num [qb]) (by norm_num [qb])
    l m hl hlm

end Lemniscate.CoarseArithmetic
