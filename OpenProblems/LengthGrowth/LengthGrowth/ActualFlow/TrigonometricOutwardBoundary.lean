import LengthGrowth.ActualFlow.TrigonometricImmersion
import LengthGrowth.ActualFlow.TrigonometricClosureZero

noncomputable section
open MeasureTheory Function Set
namespace LengthGrowth.Multicover.Trigonometric
open LengthGrowth.ActualFlow LengthGrowth.Multicover.Outward

private theorem mass_from_average (g : Fn) : mass period g = period*average g := by
  rw [average_eq]
  field_simp [period_pos.ne']

private theorem select_amplitude {n : ℕ} {m : ℤ} {Q : ℝ} (hn : 2000 ≤ n)
    (small : |(m:ℝ)| < n) (near : ∀ a ∈ Icc (0:ℝ) 3, |(n:ℝ)-slowAmplitude Q a| ≤ 1) :
    ∃ a ∈ Icc (0:ℝ) 3, (∫ s in 0..period, angleTangent (liftAngle n m a (slowAmplitude Q a)) s) = 0 := by
  by_cases hz : m = 0
  · subst m
    obtain ⟨a, ha, re, im⟩ := TrigonometricClosure.zero_turn_closes hn (slowAmplitude Q)
      (slowAmplitude_continuous Q).continuousOn (fun a ha => by rw [abs_sub_comm]; exact near a ha)
    refine ⟨a,ha,?_⟩
    let v := angleTangent (liftAngle n 0 a (slowAmplitude Q a))
    have ci := (angleTangent_smooth (lift_smooth n 0 a (slowAmplitude Q a))).continuous.intervalIntegrable 0 period (μ:=volume)
    simp only [Int.cast_zero]
    apply Complex.ext
    · change Complex.reCLM (∫ s in 0..period, v s) = 0
      rw [←Complex.reCLM.intervalIntegral_comp_comm ci]
      simpa only [v,angleTangent, Complex.reCLM_apply, mul_comm Complex.I, Complex.exp_ofReal_mul_I_re,
        liftAngle,zero_mul,zero_add,primitiveWave,TrigonometricClosure.phase,period] using re
    · change Complex.imCLM (∫ s in 0..period, v s) = 0
      rw [←Complex.imCLM.intervalIntegral_comp_comm ci]
      simpa only [v,angleTangent, Complex.imCLM_apply, mul_comm Complex.I, Complex.exp_ofReal_mul_I_im,
        liftAngle,zero_mul,zero_add,primitiveWave,TrigonometricClosure.phase,period] using im
  · exact ⟨0, ⟨le_rfl,by norm_num⟩, nonzero_closure (by omega) hz small _⟩

private theorem physical_level {n : ℕ} {m : ℤ} {a A Q : ℝ} (hn : 2 ≤ n) (ha : |a| ≤ 3)
    (large : 1000000*(1+|(m:ℝ)|) ≤ A) (near : |(n:ℝ)-A| ≤ 1)
    (level : a^2/2 + A^2*(4097/2048) = Q^2*(4097/2048))
    (close : (∫s in 0..period, angleTangent (liftAngle n m a A) s)=0) :
    ∃ g : PeriodicRegularPosition, materialSignedCurvature g.position g.period=2*Real.pi*(m:ℝ) ∧
      2*materialEnergy g.position g.period*g.length-(2*Real.pi*(m:ℝ))^2 =
        period^2*(4097/2048)*Q^2 ∧
      0 < materialEnergy g.position g.period*materialLengthRate g.position g.period -
        g.length*materialDissipation g.position g.period := by
  let k := curvatureField n (m:ℝ) a A
  let w := scaledCurvature n (m:ℝ) a A
  let h := scaledForce n (m:ℝ) a A
  let F := spatialForce k
  have Ap : 0 < A := by linarith only [large,abs_nonneg (m:ℝ)]
  have np : 0 < n := by omega
  obtain ⟨g,_,gl,gt,ge,gr,gd⟩ := realize_angle period period_pos (liftAngle n m a A) (fun s => k s)
    (lift_smooth n m a A) (lift_derivative np m a A) (lift_periodic n m a A) close
  obtain ⟨turn, bend⟩ := prescribed_energy hn (m:ℝ) a A
  change average k = m at turn
  change average (k^2) = (m:ℝ)^2 + a^2/2 + A^2*(4097/2048) at bend
  change materialSignedCurvature g.position g.period = mass period k at gt
  change materialEnergy g.position g.period = 1/2 * mass period (k^2) at ge
  change materialLengthRate g.position g.period = ∫s in 0..period, k s*F s at gr
  change materialDissipation g.position g.period = ∫s in 0..period, (F s)^2 at gd
  have ff (s : ℝ) : F s = A^3*h s := force_scaled n Ap.ne' s
  have kk (s : ℝ) : k s = A*w s := congrArg (fun v : Fn => v s) (field_scaled n Ap.ne')
  have rate : (∫s in 0..period, k s*F s) = A^4 * mass period (w*h) := by
    simp_rw [kk,ff,show ∀x y : ℝ, A*x*(A^3*y)=A^4*(x*y) by intros; ring]
    exact intervalIntegral.integral_const_mul _ _
  have diss : (∫s in 0..period, (F s)^2) = A^6 * mass period (h^2) := by
    simp_rw [ff,show ∀x : ℝ, (A^3*x)^2 = A^6*x^2 by intros; ring]
    exact intervalIntegral.integral_const_mul _ _
  have square : mass period (k^2) = A^2*mass period (w^2) := by
    change (∫s in 0..period, (k s)^2) = _
    simp_rw [kk,mul_pow]
    exact intervalIntegral.integral_const_mul _ _
  refine ⟨g,?_,?_,?_⟩
  · rw [gt,mass_from_average,turn]; rfl
  · rw [ge, gl, mass_from_average, bend]
    change 2*(1/2*(period*((m:ℝ)^2+a^2/2+A^2*(4097/2048))))*period -
      (period*(m:ℝ))^2 = _
    linear_combination period^2 * level
  · rw [ge,square,gl,gr,gd,rate,diss,mass_from_average,mass_from_average,mass_from_average]
    have sg := prescribed_scaled_rate np ha large near
    change 0 < average (w^2)*average (w*h)/2-average (h^2) at sg
    have pos : 0 < period^2 * A^6 := mul_pos (pow_pos period_pos _) (pow_pos Ap _)
    convert! mul_pos pos sg using 1
    ring

/-- Every integer turning number and every sufficiently large prescribed defect
has an actual smooth closed regular position pointing strictly out of the sublevel. -/
theorem prescribed_outward_exact_level (m : ℤ) (K : ℝ)
    (high : (2*Real.pi)^2 * (4097/2048) * (2000000*(1+|(m:ℝ)|))^2 ≤ K) :
    ∃ g : PeriodicRegularPosition, materialSignedCurvature g.position g.period=2*Real.pi*(m:ℝ) ∧
      2*materialEnergy g.position g.period*g.length-(2*Real.pi*(m:ℝ))^2=K ∧
      0 < materialEnergy g.position g.period*materialLengthRate g.position g.period -
        g.length*materialDissipation g.position g.period := by
  let B := period^2 * (4097/2048)
  let Q := Real.sqrt (K/B)
  have bp : 0 < B := by dsimp [B]; have := period_pos; positivity
  change B * (2000000*(1+|(m:ℝ)|))^2 ≤ K at high
  have low : (2000000*(1+|(m:ℝ)|))^2 ≤ K/B :=
    (le_div_iff₀ bp).mpr (by simpa only [mul_comm B] using high)
  have q2 : Q^2 = K/B := Real.sq_sqrt ((sq_nonneg _).trans low)
  have qp : 0 ≤ Q := Real.sqrt_nonneg _
  have enough : 2000000*(1+|(m:ℝ)|) ≤ Q := by
    by_contra! bad
    have h := mul_pos (sub_pos.mpr bad) (show 0 < 2000000*(1+|(m:ℝ)|)+Q by linarith only [qp,abs_nonneg (m:ℝ)])
    nlinarith only [h,q2,low]
  obtain ⟨n,hn,small,family⟩ := frequency_for_level enough
  obtain ⟨a,ha,close⟩ := select_amplitude hn small (fun a ha => (family a ha).2.1)
  obtain ⟨large,near,level⟩ := family a ha
  obtain ⟨g,turn,defect,sg⟩ := physical_level (by omega : 2 ≤ n)
    (by rw [abs_of_nonneg ha.1]; exact ha.2) large near level close
  refine ⟨g,turn,?_,sg⟩
  rw [defect]
  change B*Q^2 = K
  rw [q2]
  field_simp [bp.ne']

end LengthGrowth.Multicover.Trigonometric
#print axioms LengthGrowth.Multicover.Trigonometric.prescribed_outward_exact_level

