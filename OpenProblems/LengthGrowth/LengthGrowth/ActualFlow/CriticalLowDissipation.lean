import LengthGrowth.ActualFlow.CriticalDensityScalar

noncomputable section
open Set Function MeasureTheory FreeElasticScalar
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.CriticalDensity

/-- With the lower virial bound of a closed curve, a low RMS force
requires proportionally more half-RMS reversals. -/
theorem low_dissipation_count {P : ℝ} (hP : 0<P) {k : ℝ→ℝ} (hk : ContDiff ℝ ∞ k)
    (period : Periodic k P) (rms : (∫s in 0..P, k s^2)=P) (N : ℕ)
    (nodes : Count k P N) (low : 16*(∫s in 0..P, FiniteSignWindow.force k s^2)≤P)
    (virial : 1≤P*(∫s in 0..P, FiniteSignWindow.force k s^2)) :
    P^5 ≤ (10^16:ℝ)*((N:ℝ)+1)^6*(∫s in 0..P, FiniteSignWindow.force k s^2) := by
  let m : ℝ := (N:ℝ)+1
  let F:=FiniteSignWindow.force k
  let D:=∫s in 0..P,F s^2
  let J:=∫s in 0..P,|F s|
  have hm : 0<m := by dsimp [m]; positivity
  have hF:Continuous F:=FiniteSignWindow.force_continuous hk
  have D0 : 0≤D:=intervalIntegral.integral_nonneg_of_forall hP.le (fun _=>sq_nonneg _)
  change 16*D≤P at low
  change 1≤P*D at virial
  change P^5 ≤ (10^16:ℝ)*m^6*D
  by_cases short : P≤200*m
  · have sixth:=pow_le_pow_left₀ hP.le short 6
    apply (mul_le_mul_iff_right₀ hP).mp
    nlinarith only [sixth,mul_le_mul_of_nonneg_left virial (show 0≤(10^16:ℝ)*m^6 by positivity),pow_nonneg hm.le 6]
  have cs:=LengthGrowth.interval_integral_mul_sq_le (f:=fun _:ℝ => (1:ℝ)) continuous_const hF.abs hP.le
  simp only [one_mul,one_pow,sq_abs,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at cs
  change J^2 ≤ P*D at cs
  have jlow : J≤P/4 := by
    by_contra! hh
    nlinarith only [mul_self_lt_mul_self (show 0≤P/4 by positivity) hh,cs,mul_le_mul_of_nonneg_left low hP.le]
  have hk' := (contDiff_infty_iff_deriv.mp hk).2
  have hp':=actual_deriv_periodic period (hk.differentiable (by simp))
  have hp'':=actual_deriv_periodic hp' (hk'.differentiable (by simp))
  have hper : Periodic F P := by
    intro s; unfold F FiniteSignWindow.force; rw [hp'',period]
  let e:=FiniteSignWindow.energy k
  have he : Continuous e := (hk'.continuous.pow 2).add ((hk.continuous.pow 4).div_const 4)
  obtain ⟨z,hz,hmax⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hP.le) he.continuousOn
  let a:=fourthRoot (e z)
  let A:=max 1 a
  have ha0:0≤a:=fourthRoot_nonneg _
  have ea : e z=a^4 := (fourthRoot_pow_four (show 0≤e z by
    change 0≤(deriv k z)^2+(k z)^4/4;positivity)).symm
  have hA : 1≤A := le_max_left _ _
  have cap (s : ℝ) (hs : s∈Icc 0 P) : |k s|≤2*A := by
    have mx:=hmax hs
    change (deriv k s)^2+k s^4/4≤e z at mx
    rw [ea] at mx
    have ka : |k s|≤2*a := by
      by_contra! hh
      have h4:=pow_lt_pow_left₀ hh (show 0≤2*a by positivity) (by decide : 4≠0)
      rw [show |k s|^4=k s^4 by rw [show (4:ℕ)=2*2 by decide,pow_mul,pow_mul,sq_abs]] at h4
      nlinarith only [h4,mx,sq_nonneg (deriv k s),pow_nonneg ha0 4]
    linarith only [ka,show a≤A from le_max_right _ _]
  have ode (s:ℝ) : HasDerivAt (deriv k) (F s-k s^3/2) s := by
    simpa [F,FiniteSignWindow.force] using (hk'.differentiable (by simp) s).hasDerivAt
  obtain ⟨n,hn,part⟩:=nodes 0 P hP.le (by linarith)
  have tent:=part.tent_mass hA (fun s => (hk.differentiable (by simp) s).hasDerivAt) ode hF cap
  rw [rms,sub_zero] at tent
  have nm : (n:ℝ)≤m := by dsimp [m];exact_mod_cast hn
  have bound : P/2-J≤16*m*A := by
    change (3/2:ℝ)*P≤2*J+P/2+32*(n:ℝ)*A at tent
    nlinarith only [tent,mul_le_mul_of_nonneg_right nm (show 0≤A by linarith)]

  have mass_amp : P≤64*m*A := by linarith
  have ha : 2≤a := by
    by_contra! hh
    have hA2 : A≤2 := max_le (by norm_num) hh.le
    nlinarith only [mass_amp,mul_le_mul_of_nonneg_left hA2 hm.le,lt_of_not_ge short,hm]
  have apos : 0<a := by linarith
  rw [show A=a from max_eq_right (by linarith)] at mass_amp
  have plen : 200*m/a≤P := (div_le_iff₀ apos).mpr (by nlinarith only [lt_of_not_ge short,mul_le_mul_of_nonneg_left ha hP.le,hP])
  obtain ⟨n',hn',part'⟩:=nodes z (z+200*m/a) (le_add_of_nonneg_right (by positivity)) (by linarith)
  have lower:=charge hk N ha ea hn' part'
  have upper:=periodic_window hF hper 0 z (show 0≤200*m/a by positivity) plen
  simp only [zero_mul,zero_add,sub_zero,sq_abs] at upper
  change a^2/4<∫s in z..(z+200*m/a),|F s| at lower
  change (∫s in z..(z+200*m/a),|F s|)≤Real.sqrt ((200*m/a)*D) at upper
  have sq:=mul_self_lt_mul_self (show 0≤a^2/4 by positivity) (lower.trans_le upper)
  have sr:=Real.sq_sqrt (show 0≤200*m/a*D by positivity)
  have fourth : a^4/16 < 200*m*D/a := by
    rw [← div_mul_eq_mul_div]
    nlinarith only [sq,sr]
  have fifth : a^5≤3200*m*D := by nlinarith only [(lt_div_iff₀ apos).mp fourth]
  have total:=pow_le_pow_left₀ hP.le mass_amp 5
  nlinarith only [total,mul_le_mul_of_nonneg_left fifth (show 0≤(64*m)^5 by positivity),
    mul_nonneg (pow_nonneg hm.le 6) D0]

end LengthGrowth.ActualFlow.CriticalDensity
#print axioms LengthGrowth.ActualFlow.CriticalDensity.low_dissipation_count
