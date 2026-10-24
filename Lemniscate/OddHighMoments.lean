import Lemniscate.OddSignedWeights
import Lemniscate.CosineHighRows
import Lemniscate.GeometricMomentTails

/-! Exact geometric sums and the uniform opposite-branch constant used in the
odd high-row estimate. The decay bound is proved for every j >= 6. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

def oddCrossMoment : ℚ :=
  4*moment 0 (qb*a)+8*moment 1 (qb*a)+5*moment 2 (qb*a)+moment 3 (qb*a)

theorem odd_upper_majorant_hasSum (v : ℝ) :
    HasSum (fun k : ℕ => (45*(rhi:ℝ)*(H:ℝ))*((k+1:ℕ):ℝ)*((qb*a:ℚ):ℝ)^(k+1)*
      (v^2+2*v*((k+1:ℕ):ℝ)+((k+1:ℕ):ℝ)^2/3))
      ((45*(rhi:ℝ)*(H:ℝ))*(v^2*(moment 1 (qb*a):ℝ)+
        2*v*(moment 2 (qb*a):ℝ)+(moment 3 (qb*a):ℝ)/3)) := by
  have hz : ‖((qb*a:ℚ):ℝ)‖ < 1 := by norm_num [qb, a]
  convert! ((((tail1_sound (qb*a) hz 1).mul_left (v^2)).add
    ((tail2_sound (qb*a) hz 1).mul_left (2*v))).add
    ((tail3_sound (qb*a) hz 1).mul_left (1/3))).mul_left (45*(rhi:ℝ)*(H:ℝ)) using 1
  · ext k
    ring
  · rw [tail_one_values.2.1, tail_one_values.2.2.1, tail_one_values.2.2.2]
    ring

theorem odd_cross_moment_hasSum :
    HasSum (fun k : ℕ => (4+8*(k:ℝ)+5*(k:ℝ)^2+(k:ℝ)^3)*((qb*a:ℚ):ℝ)^k)
      (oddCrossMoment:ℝ) := by
  have hz : ‖((qb*a:ℚ):ℝ)‖ < 1 := by norm_num [qb, a]
  convert! ((((moment_sound 0 (by omega) (qb*a) hz).mul_left 4).add
    ((moment_sound 1 (by omega) (qb*a) hz).mul_left 8)).add
    ((moment_sound 2 (by omega) (qb*a) hz).mul_left 5)).add
    (moment_sound 3 (by omega) (qb*a) hz) using 1
  · ext k
    ring
  · simp only [oddCrossMoment, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]

theorem odd_cross_polynomial_bound (v k : ℝ) (hv : 1 ≤ v) (hk : 0 ≤ k) :
    (v+k)*(2*v+k)^2 ≤ v^3*(4+8*k+5*k^2+k^3) := by
  have hv0 : 0 ≤ v := by linarith
  have hv2 : v ≤ v^2 := by nlinarith [mul_nonneg hv0 (by linarith : 0 ≤ v-1)]
  have hv3 : v^2 ≤ v^3 := by nlinarith [mul_nonneg (sq_nonneg v) (by linarith : 0 ≤ v-1)]
  have h1 := mul_le_mul_of_nonneg_right hv3 hk
  have h2 := mul_le_mul_of_nonneg_right (hv2.trans hv3) (sq_nonneg k)
  have h3 := mul_le_mul_of_nonneg_right (hv.trans (hv2.trans hv3)) (pow_nonneg hk 3)
  nlinarith

theorem odd_frequency_geometric_decay (j : ℕ) (hj : 6 ≤ j) :
    (2*(j:ℝ)+3/2)*((qb/a:ℚ):ℝ)^j ≤ (27/2)*((qb/a:ℚ):ℝ)^6 := by
  have hz : 0 ≤ ((qb/a:ℚ):ℝ) := by norm_num [qb, a]
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    calc
      _ = ((2*(j:ℝ)+7/2)*((qb/a:ℚ):ℝ))*((qb/a:ℚ):ℝ)^j := by
        rw [pow_succ]
        push_cast
        ring
      _ ≤ (2*(j:ℝ)+3/2)*((qb/a:ℚ):ℝ)^j := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hz j)
        have hjr : (6:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
        norm_num [qb, a]
        linarith
      _ ≤ _ := ih

set_option maxRecDepth 100000 in
theorem odd_cross_constant_certificate :
    (45*rhi*H)*(37/16:ℚ)*qb*(27/2)*(qb/a)^6*oddCrossMoment < 8 := by
  decide +kernel

theorem odd_cross_moment_nonneg : (0:ℝ) ≤ (oddCrossMoment:ℝ) := by
  norm_num [oddCrossMoment, moment, qb, a]

theorem odd_cross_coefficient_bound (j : ℕ) (hj : 6 ≤ j) (v : ℝ)
    (hv : v ≤ 2*(j:ℝ)+3/2) :
    (45*(rhi:ℝ)*(H:ℝ))*(37/16)*(qb:ℝ)*((qb/a:ℚ):ℝ)^j*v*(oddCrossMoment:ℝ) < 8 := by
  have hz : 0 ≤ ((qb/a:ℚ):ℝ) := by norm_num [qb, a]
  have hb := (mul_le_mul_of_nonneg_right hv (pow_nonneg hz j)).trans
    (odd_frequency_geometric_decay j hj)
  have hfactor : 0 ≤ (45*(rhi:ℝ)*(H:ℝ))*(37/16)*(qb:ℝ)*(oddCrossMoment:ℝ) := by
    have hH : 0 ≤ (H:ℝ) := by norm_num [H, rhi, qb]
    have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
    have hr : 0 ≤ (rhi:ℝ) := by norm_num [rhi]
    exact mul_nonneg (by positivity) odd_cross_moment_nonneg
  have hh := mul_le_mul_of_nonneg_left hb hfactor
  have hc : (45*(rhi:ℝ)*(H:ℝ))*(37/16)*(qb:ℝ)*(27/2)*((qb/a:ℚ):ℝ)^6*
      (oddCrossMoment:ℝ) < 8 := by
    have hc0 := (Rat.cast_lt (K := ℝ)).mpr odd_cross_constant_certificate
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hc0
  nlinarith

end Lemniscate.OddArithmetic
