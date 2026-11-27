import LengthGrowth.ActualFlow.MulticoverIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open MeasureTheory
namespace LengthGrowth.Multicover.Trigonometric

def period : ℝ := 2 * Real.pi

theorem period_pos : 0 < period := by unfold period; positivity

def mode (n : ℕ) : Fn := ⟨fun s => Real.cos ((n : ℝ) * s), by fun_prop⟩

def trigWave (n : ℕ) : Fn :=
  ⟨fun s => 2 * Real.cos (n * s) + Real.cos (3 * (n * s)) / 32, by fun_prop⟩

/-- The second derivative with respect to the fast phase. -/
def trigSecond (n : ℕ) : Fn :=
  ⟨fun s => -2 * Real.cos (n * s) - 9 * Real.cos (3 * (n * s)) / 32, by fun_prop⟩

def trigForce (n : ℕ) : Fn := trigSecond n + (1/2 : ℝ) • (trigWave n)^3

theorem trigWave_poly (n : ℕ) (s : ℝ) :
    trigWave n s = 61/32 * mode n s + 1/8 * (mode n s)^3 := by
  change 2 * Real.cos _ + Real.cos (3 * _) / 32 = 61/32 * Real.cos _ + 1/8 * (Real.cos _)^3
  rw [Real.cos_three_mul]
  ring

theorem trigSecond_poly (n : ℕ) (s : ℝ) :
    trigSecond n s = -(37/32) * mode n s - 9/8 * (mode n s)^3 := by
  change -2 * Real.cos _ - 9 * Real.cos (3 * _) / 32 = -(37/32) * Real.cos _ - 9/8 * (Real.cos _)^3
  rw [Real.cos_three_mul]
  ring

theorem mode_mass_step {n : ℕ} (hn : 0 < n) (j : ℕ) :
    mass period ((mode n)^(j+2)) = (j+1 : ℝ)/(j+2) * mass period ((mode n)^j) := by
  have nz : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have endpoint : Real.sin ((n : ℝ) * period) = 0 := by
    simpa [period] using Real.sin_nat_mul_two_pi_sub 0 n
  have scale (k : ℕ) : mass period ((mode n)^k) =
      (n : ℝ)⁻¹ * ∫ y in 0..(n : ℝ)*period, Real.cos y ^ k := by
    change (∫ s in 0..period, Real.cos ((n : ℝ)*s)^k) = _
    simpa [smul_eq_mul] using intervalIntegral.integral_comp_mul_left
      (fun y => Real.cos y ^ k) nz (a:=0) (b:=period)
  rw [scale, scale, integral_cos_pow j]
  simp only [endpoint, Real.sin_zero, mul_zero, sub_zero, zero_div, zero_add]
  ring

/-- Even moments of one nonconstant cosine mode, including its integer repetitions. -/
private theorem modeMoment2 {n : ℕ} (hn : 0 < n) :
    mass period ((mode n)^2) = (1/2 : ℝ) * period := by
  have h := mode_mass_step hn 0
  norm_num [mass_one] at h ⊢
  linarith only [h]

private theorem modeMoment4 {n : ℕ} (hn : 0 < n) :
    mass period ((mode n)^4) = (3/8 : ℝ) * period := by
  have h := mode_mass_step hn 2
  norm_num [modeMoment2 hn] at h ⊢
  linarith only [h]

private theorem modeMoment6 {n : ℕ} (hn : 0 < n) :
    mass period ((mode n)^6) = (5/16 : ℝ) * period := by
  have h := mode_mass_step hn 4
  norm_num [modeMoment4 hn] at h ⊢
  linarith only [h]

private theorem modeMoment8 {n : ℕ} (hn : 0 < n) :
    mass period ((mode n)^8) = (35/128 : ℝ) * period := by
  have h := mode_mass_step hn 6
  norm_num [modeMoment6 hn] at h ⊢
  linarith only [h]

private theorem modeMoment10 {n : ℕ} (hn : 0 < n) :
    mass period ((mode n)^10) = (63/256 : ℝ) * period := by
  have h := mode_mass_step hn 8
  norm_num [modeMoment8 hn] at h ⊢
  linarith only [h]

private theorem modeMoment12 {n : ℕ} (hn : 0 < n) :
    mass period ((mode n)^12) = (231/1024 : ℝ) * period := by
  have h := mode_mass_step hn 10
  norm_num [modeMoment10 hn] at h ⊢
  linarith only [h]

private theorem modeMoment14 {n : ℕ} (hn : 0 < n) :
    mass period ((mode n)^14) = (429/2048 : ℝ) * period := by
  have h := mode_mass_step hn 12
  norm_num [modeMoment12 hn] at h ⊢
  linarith only [h]

private theorem modeMoment16 {n : ℕ} (hn : 0 < n) :
    mass period ((mode n)^16) = (6435/32768 : ℝ) * period := by
  have h := mode_mass_step hn 14
  norm_num [modeMoment14 hn] at h ⊢
  linarith only [h]

private theorem modeMoment18 {n : ℕ} (hn : 0 < n) :
    mass period ((mode n)^18) = (12155/65536 : ℝ) * period := by
  have h := mode_mass_step hn 16
  norm_num [modeMoment16 hn] at h ⊢
  linarith only [h]

theorem wave_square {n : ℕ} (hn : 0 < n) :
    mass period ((trigWave n)^2) = (4097/2048 : ℝ) * period := by
  have identity : (trigWave n)^2 =
      (3721/1024 : ℝ) • ((mode n)^2) +
      (61/128 : ℝ) • ((mode n)^4) +
      (1/64 : ℝ) • ((mode n)^6) := by
    ext s
    simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply,
      smul_eq_mul, trigWave_poly]
    ring
  rw [identity]
  simp only [map_add, map_smul, smul_eq_mul, modeMoment2 hn, modeMoment4 hn, modeMoment6 hn]
  ring

theorem wave_force {n : ℕ} (hn : 0 < n) :
    mass period (trigWave n * trigForce n) = (17801219/16777216 : ℝ) * period := by
  have identity : trigWave n * trigForce n =
      (-2257/1024 : ℝ) • ((mode n)^2) +
      (9045329/2097152 : ℝ) • ((mode n)^4) +
      (208549/131072 : ℝ) • ((mode n)^6) +
      (11163/65536 : ℝ) • ((mode n)^8) +
      (61/8192 : ℝ) • ((mode n)^10) +
      (1/8192 : ℝ) • ((mode n)^12) := by
    ext s
    simp only [trigForce, ContinuousMap.pow_apply, ContinuousMap.smul_apply,
      ContinuousMap.add_apply, ContinuousMap.mul_apply, smul_eq_mul, trigWave_poly, trigSecond_poly]
    ring
  rw [identity]
  simp only [map_add, map_smul, smul_eq_mul, modeMoment2 hn, modeMoment4 hn, modeMoment6 hn, modeMoment8 hn, modeMoment10 hn, modeMoment12 hn]
  ring

theorem force_square {n : ℕ} (hn : 0 < n) :
    mass period ((trigForce n)^2) = (60523245573/68719476736 : ℝ) * period := by
  have identity : (trigForce n)^2 =
      (1369/1024 : ℝ) • ((mode n)^2) +
      (-5670361/1048576 : ℝ) • ((mode n)^4) +
      (16719382105/4294967296 : ℝ) • ((mode n)^6) +
      (1655295207/536870912 : ℝ) • ((mode n)^8) +
      (180096959/268435456 : ℝ) • ((mode n)^10) +
      (1098041/16777216 : ℝ) • ((mode n)^12) +
      (55815/16777216 : ℝ) • ((mode n)^14) +
      (183/2097152 : ℝ) • ((mode n)^16) +
      (1/1048576 : ℝ) • ((mode n)^18) := by
    ext s
    simp only [trigForce, ContinuousMap.pow_apply, ContinuousMap.smul_apply,
      ContinuousMap.add_apply, smul_eq_mul, trigWave_poly, trigSecond_poly]
    ring
  rw [identity]
  simp only [map_add, map_smul, smul_eq_mul, modeMoment2 hn, modeMoment4 hn, modeMoment6 hn, modeMoment8 hn, modeMoment10 hn, modeMoment12 hn, modeMoment14 hn, modeMoment16 hn, modeMoment18 hn]
  ring

theorem positive_average_rate {n : ℕ} (hn : 0 < n) :
    period^2 / 6 < mass period ((trigWave n)^2) * mass period (trigWave n * trigForce n) / 2 -
      period * mass period ((trigForce n)^2) := by
  rw [wave_square hn, wave_force hn, force_square hn]
  nlinarith only [sq_pos_of_pos period_pos]

end LengthGrowth.Multicover.Trigonometric
#print axioms LengthGrowth.Multicover.Trigonometric.positive_average_rate

