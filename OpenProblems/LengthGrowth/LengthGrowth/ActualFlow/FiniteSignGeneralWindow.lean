import LengthGrowth.ActualFlow.FiniteSignWindow

/-! Window bounds with arbitrary normalized initial phase. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.FiniteSignGeneralWindow
open LengthGrowth.ActualFlow.FiniteSignWindow

private theorem energy_nonneg (k : ℝ → ℝ) (x : ℝ) : 0 ≤ energy k x := by
  unfold energy
  positivity

private theorem energy_deriv {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (x : ℝ) :
    HasDerivAt (energy k) (2 * deriv k x * force k x) x := by
  have hv := (contDiff_infty_iff_deriv.mp hk).2
  have hd := (((hv.differentiable (by simp) x).hasDerivAt.pow 2).add
    (((hk.differentiable (by simp) x).hasDerivAt.pow 4).div_const 4))
  apply hd.congr_deriv
  unfold force
  ring

/-- Resistance of the oscillator energy amplitude to L¹ forcing. The
positive regularization also handles points where the unregularized
phase velocity could vanish. -/
theorem energy_amplitude_window {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) {P : ℝ} (hP : 0≤P)
    (x : ℝ) (hx : x ∈ Icc 0 P) :
    |Real.sqrt (energy k x)-Real.sqrt (energy k 0)| ≤ ∫ t in 0..P, |force k t| := by
  have hv := (contDiff_infty_iff_deriv.mp hk).2
  have hc := force_continuous hk
  have hE : Continuous (energy k) := continuous_iff_continuousAt.mpr
    (fun z => (energy_deriv hk z).continuousAt)
  have pert (ε : ℝ) (hε : 0<ε) :
      |Real.sqrt (energy k x+ε)-Real.sqrt (energy k 0+ε)| ≤ ∫ t in 0..P, |force k t| := by
    let d := fun z => deriv k z * force k z / Real.sqrt (energy k z+ε)
    have hp (z) : 0 < energy k z+ε := add_pos_of_nonneg_of_pos (energy_nonneg k z) hε
    have hpd (z) : 0 < Real.sqrt (energy k z+ε) := Real.sqrt_pos.mpr (hp z)
    have cd : Continuous d := (hv.continuous.mul hc).div (hE.add continuous_const).sqrt
      (fun z => (hpd z).ne')
    have df (z) : HasDerivAt (fun t => Real.sqrt (energy k t+ε)) (d z) z := by
      apply (((energy_deriv hk z).add_const ε).sqrt (hp z).ne').congr_deriv
      dsimp [d]
      ring
    have hi := LengthGrowth.interval_oscillation_le df cd hx (show (0:ℝ)∈Icc 0 P from ⟨le_rfl,hP⟩)
    simp only [Real.norm_eq_abs] at hi
    apply hi.trans
    apply intervalIntegral.integral_mono_on hP (cd.abs.intervalIntegrable _ _) (hc.abs.intervalIntegrable _ _)
    intro z _
    change |deriv k z*force k z / Real.sqrt (energy k z+ε)| ≤ |force k z|
    rw [abs_div,abs_mul,abs_of_pos (hpd z),div_le_iff₀ (hpd z)]
    have hb : |deriv k z| ≤ Real.sqrt (energy k z+ε) := by
      apply (Real.le_sqrt (abs_nonneg _) (hp z).le).mpr
      rw [sq_abs]
      unfold energy
      nlinarith [show 0≤(k z)^4 by positivity]
    linarith [mul_le_mul_of_nonneg_right hb (abs_nonneg (force k z))]
  have hlim (v : ℝ) : Tendsto (fun ε : ℝ => Real.sqrt (energy k v + ε)) (𝓝[>] 0)
      (𝓝 (Real.sqrt (energy k v))) := by
    simpa only [add_zero,Function.comp_def,id_eq] using (Real.continuous_sqrt.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := energy k v)).add
        (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))))
  have hl := (hlim x).sub (hlim 0)
  have hevent : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0<ε := self_mem_nhdsWithin
  have endbound := le_of_tendsto (continuous_abs.continuousAt.tendsto.comp hl)
    (show ∀ᶠ ε in 𝓝[>] (0:ℝ), |Real.sqrt (energy k x + ε) - Real.sqrt (energy k 0 + ε)| ≤
      ∫ t in 0..P, |force k t| from hevent.mono (fun ε hε => pert ε hε))
  exact endbound

theorem forced_window_bounds {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) {P : ℝ} (hP : 0≤P)
    (hamp : Real.sqrt (energy k 0) = 1) (hf : (∫ x in 0..P, |force k x|) ≤ 1/4) :
    ∀ x∈Icc 0 P, |k x|≤2 ∧ |deriv k x|≤2 := by
  intro x hx
  have h := (abs_le.mp ((energy_amplitude_window hk hP x hx).trans hf)).2
  rw [hamp] at h
  have he : Real.sqrt (energy k x) ≤ 5/4 := by linarith
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) he 2
  rw [Real.sq_sqrt (energy_nonneg k x)] at hsq
  unfold energy at hsq
  constructor
  · by_contra! hn
    have hpow := pow_lt_pow_left₀ hn (by norm_num : (0:ℝ)≤2) (by norm_num : (4:ℕ)≠0)
    have ha : |k x|^4 = k x^4 := by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]
    rw [ha] at hpow
    nlinarith [sq_nonneg (deriv k x)]
  · nlinarith [sq_abs (deriv k x), abs_nonneg (deriv k x),show 0≤k x^4 by positivity]

theorem cubic_integral_gt {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (N : ℕ)
    (hamp : Real.sqrt (energy k 0) = 1)
    (hf : (∫ x in 0..(100*((N:ℝ)+1)), |force k x|) ≤ 1/4) :
    8*((N:ℝ)+1)+1/2 < ∫ x in 0..(100*((N:ℝ)+1)), |k x|^3 := by
  let P := 100*((N:ℝ)+1)
  have hP : 0≤P := by dsimp [P]; positivity
  have hv := (contDiff_infty_iff_deriv.mp hk).2
  have hfcont := force_continuous hk
  let dp := fun x => (deriv k x)^2 + k x*deriv (deriv k) x
  have cdp : Continuous dp := (hv.continuous.pow 2).add
    (hk.continuous.mul (contDiff_infty_iff_deriv.mp hv).2.continuous)
  have hd (x) : HasDerivAt (fun z => k z*deriv k z) (dp x) x := by
    apply (((hk.differentiable (by simp) x).hasDerivAt).mul
      ((hv.differentiable (by simp) x).hasDerivAt)).congr_deriv
    dsimp [dp]
    ring
  have hb := forced_window_bounds hk hP hamp hf
  have pt (x : ℝ) (hx : x∈Icc 0 P) :
      (9/16:ℝ) ≤ (dp x+(3/2)*|k x|^3) + 2*|force k x| := by
    have hw := (abs_le.mp ((energy_amplitude_window hk hP x hx).trans hf)).1
    rw [hamp] at hw
    have hs : (3/4:ℝ) ≤ Real.sqrt (energy k x) := by linarith
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/4) hs 2
    rw [Real.sq_sqrt (energy_nonneg k x)] at hsq
    have hk4 : (k x)^4 ≤ 2*|k x|^3 := by
      have hh := mul_le_mul_of_nonneg_right (hb x hx).1 (pow_nonneg (abs_nonneg (k x)) 3)
      have ha : |k x|^4 = k x^4 := by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]
      simpa only [← pow_succ',ha] using hh
    have hprod := (neg_abs_le (k x*force k x))
    rw [abs_mul] at hprod
    have hprod' := mul_le_mul_of_nonneg_right (hb x hx).1 (abs_nonneg (force k x))
    have hid : energy k x = dp x + 3/4*(k x)^4 - k x*force k x := by
      dsimp [energy,dp,force]; ring
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hP intervalIntegrable_const
    (((cdp.add ((hk.continuous.abs.pow 3).const_mul (3/2))).add
      (hfcont.abs.const_mul 2)).intervalIntegrable _ _) pt
  change (∫ _x in 0..P, (9/16:ℝ)) ≤ ∫ x in 0..P, (dp x +(3/2)*|k x|^3)+2*|force k x| at hi
  rw [intervalIntegral.integral_const,smul_eq_mul,sub_zero,
    intervalIntegral.integral_add (f := fun x => dp x+(3/2)*|k x|^3)
      (g := fun x => 2*|force k x|) ((cdp.add ((hk.continuous.abs.pow 3).const_mul (3/2))).intervalIntegrable _ _)
      ((hfcont.abs.const_mul 2).intervalIntegrable _ _),
    intervalIntegral.integral_add (f := dp) (g := fun x => (3/2)*|k x|^3)
      (cdp.intervalIntegrable _ _) (((hk.continuous.abs.pow 3).const_mul (3/2)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd z) (cdp.intervalIntegrable 0 P)] at hi
  obtain ⟨hy,hv'⟩ := hb P ⟨hP,le_rfl⟩
  have hprod := (le_abs_self (k P*deriv k P)).trans
    ((abs_mul (k P) (deriv k P)).le.trans (mul_le_mul hy hv' (abs_nonneg _) (by norm_num)))
  obtain ⟨hy0,hv0⟩ := hb 0 ⟨le_rfl,hP⟩
  have absprod : |k 0*deriv k 0| ≤ 4 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hy0 hv0 (abs_nonneg _) (by norm_num)]
  have lowerprod := (neg_abs_le (k 0*deriv k 0))
  change _ < ∫ x in 0..P, |k x|^3
  change (∫ x in 0..P, |force k x|) ≤ 1/4 at hf
  dsimp only [P] at hi hf hprod ⊢
  linarith [show 0 ≤ (N:ℝ) by positivity]

#print axioms energy_amplitude_window
#print axioms forced_window_bounds
#print axioms cubic_integral_gt
end LengthGrowth.ActualFlow.FiniteSignGeneralWindow
