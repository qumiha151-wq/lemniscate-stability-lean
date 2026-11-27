import LengthGrowth.ActualFlow.TrigonometricPerturbation

noncomputable section
open MeasureTheory Set Function
namespace LengthGrowth.Multicover.Trigonometric

def slowAmplitude (Q a : ℝ) := Real.sqrt (Q^2 - a^2*(1024/4097))

theorem slowAmplitude_continuous (Q : ℝ) : Continuous (slowAmplitude Q) := by
  unfold slowAmplitude
  fun_prop

/-- A single frequency works throughout the continuous family with the prescribed excess. -/
theorem frequency_for_level {m Q : ℝ} (large : 2000000*(1+|m|) ≤ Q) :
    ∃ n : ℕ, 2000 ≤ n ∧ |m| < (n:ℝ) ∧ ∀ a ∈ Icc (0:ℝ) 3,
      1000000*(1+|m|) ≤ slowAmplitude Q a ∧ |(n:ℝ)-slowAmplitude Q a| ≤ 1 ∧
      a^2/2 + (slowAmplitude Q a)^2*(4097/2048) = Q^2*(4097/2048) := by
  let n := ⌊Q+1/2⌋₊
  have qmin : 2000000 ≤ Q := by linarith only [large, abs_nonneg m]
  have lo : Q+1/2 < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have hi : (n:ℝ) ≤ Q+1/2 := Nat.floor_le (by linarith)
  have nmin : (2000:ℝ) ≤ n := by linarith
  refine ⟨n, by exact_mod_cast nmin, by linarith only [large, lo,abs_nonneg m], fun a ha => ?_⟩
  have a2 : a^2 ≤ 9 := by nlinarith only [sq_nonneg (a-3),mul_nonneg ha.1 (sub_nonneg.mpr ha.2),ha.2]
  have q2 : 2000000^2 ≤ Q^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr qmin) (by linarith only [qmin] : 0 ≤ Q+2000000)]
  have rad : 0 ≤ Q^2-a^2*(1024/4097) := by linarith only [q2,a2]
  have ae : (slowAmplitude Q a)^2 = Q^2-a^2*(1024/4097) := Real.sq_sqrt rad
  have ap : 0 ≤ slowAmplitude Q a := Real.sqrt_nonneg _
  have lower : Q-1/2 ≤ slowAmplitude Q a := by
    by_contra! bad
    have h := mul_pos (sub_pos.mpr bad) (show 0 < Q-1/2 + slowAmplitude Q a by linarith)
    nlinarith only [h, ae, a2, qmin]
  have upper : slowAmplitude Q a ≤ Q := by
    by_contra! bad
    have h := mul_pos (sub_pos.mpr bad) (show 0 < slowAmplitude Q a + Q by linarith)
    nlinarith only [h, ae, sq_nonneg a]
  refine ⟨by linarith only [lower,large,abs_nonneg m], abs_le.mpr ⟨by linarith,by linarith⟩, ?_⟩
  linarith only [ae]

def signedMode (z : ℤ) : Fn := ⟨fun s => Real.cos ((z:ℝ)*s), by fun_prop⟩

theorem average_signedMode {z : ℤ} (hz : z ≠ 0) : average (signedMode z) = 0 := by
  have nz : (z:ℝ) ≠ 0 := by exact_mod_cast hz
  have edge : Real.sin ((z:ℝ)*period) = 0 := by simpa [period] using Real.sin_int_mul_two_pi_sub 0 z
  have slope (s:ℝ) : HasDerivAt (fun t => Real.sin ((z:ℝ)*t)/(z:ℝ)) (signedMode z s) s := by
    apply (((hasDerivAt_id s).const_mul (z:ℝ)).sin.div_const _).congr_deriv
    change Real.cos _ * ((z:ℝ)*1) / (z:ℝ) = Real.cos _
    field_simp
    rfl
  rw [average_eq]
  change (∫s in 0..period, signedMode z s)/period = _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => slope s) ((signedMode z).continuous.intervalIntegrable ..)]
  simp [edge]

theorem average_signed_modes {y z : ℤ} (hm : y-z ≠ 0) (hp : y+z ≠ 0) :
    average (signedMode y * signedMode z) = 0 := by
  have eq : signedMode y * signedMode z = (1/2:ℝ) • (signedMode (y-z)+signedMode (y+z)) := by
    ext s
    change Real.cos _ * Real.cos _ = 1/2 * (Real.cos _ + Real.cos _)
    push_cast
    rw [sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  rw [eq,map_smul,map_add,average_signedMode hm,average_signedMode hp]
  simp

theorem wave_modes (n : ℕ) : trigWave n =
    (2:ℝ) • signedMode n + (1/32 : ℝ) • signedMode (3*(n:ℤ)) := by
  ext s
  change 2*Real.cos _ + Real.cos _/32 = 2*Real.cos _ + (1/32)*Real.cos _
  push_cast
  ring_nf

theorem prescribed_energy {n : ℕ} (hn : 2 ≤ n) (m a A : ℝ) :
    let k := m • (1 : Fn) + a • signedMode 1 + A • trigWave n
    average k = m ∧ average (k^2) = m^2 + a^2/2 + A^2*(4097/2048) := by
  have npos : 0 < n := by omega
  have z0 := average_signedMode (by norm_num : (1:ℤ) ≠ 0)
  have z1 : average (trigWave n) = 0 := by
    rw [wave_modes,map_add,map_smul,map_smul,average_signedMode (by omega),average_signedMode (by omega)]
    simp
  have cross : average (signedMode 1 * trigWave n) = 0 := by
    have eq : signedMode 1 * trigWave n = (2:ℝ) • (signedMode 1 * signedMode n) +
        (1/32:ℝ) • (signedMode 1 * signedMode (3*(n:ℤ))) := by
      rw [wave_modes]
      ext s
      simp [smul_eq_mul]
      ring
    rw [eq,map_add,map_smul,map_smul,average_signed_modes (by omega) (by omega),
      average_signed_modes (by omega) (by omega)]
    simp
  have cos2 : average ((signedMode 1)^2) = 1/2 := by
    have h := mode_mass_step (n:=1) (by norm_num) 0
    norm_num [mass_one] at h
    have eq : signedMode 1 = mode 1 := by ext s; simp [signedMode,mode]
    rw [eq, average_eq, h]
    field_simp [period_pos.ne']
  have w2 : average ((trigWave n)^2) = 4097/2048 := by
    rw [average_eq, wave_square npos,mul_div_cancel_right₀ _ period_pos.ne']
  dsimp only
  constructor
  · simp [z0,z1,average_one]
  · have expand : (m • (1 : Fn) + a • signedMode 1 + A • trigWave n)^2 =
        (m^2) • (1 : Fn) + (a^2) • ((signedMode 1)^2) + (A^2) • ((trigWave n)^2) +
        (2*m*a) • signedMode 1 + (2*m*A) • trigWave n + (2*a*A) • (signedMode 1 * trigWave n) := by
      ext s
      simp only [ContinuousMap.pow_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, ContinuousMap.mul_apply, smul_eq_mul]
      ring
    rw [expand]
    simp only [map_add,map_smul,smul_eq_mul,average_one,cos2,w2,z0,z1,cross]
    ring

end LengthGrowth.Multicover.Trigonometric
#print axioms LengthGrowth.Multicover.Trigonometric.prescribed_energy


