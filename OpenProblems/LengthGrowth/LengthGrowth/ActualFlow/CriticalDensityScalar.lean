import LengthGrowth.ActualFlow.CriticalDensityWindow
import LengthGrowth.ActualFlow.CriticalDensityTent
import LengthGrowth.ActualFlow.CriticalDensityEstimates
import LengthGrowth.ActualFlow.FiniteSignTheorem

noncomputable section
open Set Function MeasureTheory FreeElasticScalar
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.CriticalDensity

/-- The optimal power of the number of half-RMS excursion pieces,
for an actual smooth scalar curvature and its second-order force. -/
theorem scalar_bound {P : ℝ} (hP : 0<P) {k : ℝ→ℝ} (hk : ContDiff ℝ ∞ k)
    (period : Periodic k P) (rms : (∫s in 0..P, k s^2)=P) (N : ℕ)
    (nodes : Count k P N) :
    P/2 ≤ Real.sqrt (P*(∫s in 0..P, FiniteSignWindow.force k s^2)) +
      1024*((N:ℝ)+1)*Real.sqrt ((N:ℝ)+1) := by
  let m : ℝ := (N:ℝ)+1
  let F:=FiniteSignWindow.force k
  let D:=∫s in 0..P,F s^2
  let J:=∫s in 0..P,|F s|
  let R:=∫s in 0..P,(|F s|-1/2)^2
  have hm : 1≤m := by dsimp [m]; linarith [Nat.cast_nonneg (α:=ℝ) N]
  have hm0 : 0<m := by linarith
  have hs : 1≤Real.sqrt m := by
    simpa using Real.sqrt_le_sqrt hm
  have hF:Continuous F:=FiniteSignWindow.force_continuous hk
  have D0 : 0≤D:=intervalIntegral.integral_nonneg_of_forall hP.le (fun _=>sq_nonneg _)
  have hroot:=Real.sq_sqrt (mul_nonneg hP.le D0)
  have root0:=Real.sqrt_nonneg (P*D)
  change P/2 ≤ Real.sqrt (P*D)+1024*m*Real.sqrt m
  have nonneg : 0≤1024*m*Real.sqrt m := by positivity
  by_cases smallP : P≤2048*m*Real.sqrt m
  · linarith
  by_cases high : P/4≤D
  · have hlow : P/2≤Real.sqrt (P*D) := by
      by_contra! hh
      have sq:=mul_self_lt_mul_self root0 hh
      nlinarith only [sq,hroot,mul_le_mul_of_nonneg_left high hP.le]
    linarith
  have Jroot : J≤Real.sqrt (P*D) := by
    have hh:=LengthGrowth.interval_integral_mul_sq_le (f:=fun _:ℝ => (1:ℝ)) continuous_const hF.abs hP.le
    simp only [one_mul,one_pow,sq_abs,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at hh
    change J^2 ≤ P*D at hh
    by_contra! gt
    nlinarith only [hh,hroot,mul_self_lt_mul_self root0 gt]
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
  have Rle : R≤16*m*A := by
    have r:=residual_mass F hF P
    change R=D-J+P/4 at r
    linarith [lt_of_not_ge high]
  have ampl : A≤32*Real.sqrt m := by
    by_cases ha : 2≤a
    · have eqA : A=a := max_eq_right (by linarith)
      rw [eqA] at Rle ⊢
      have pos : 0<a := by linarith
      have plen : 200*m/a≤P := by
        apply (div_le_iff₀ pos).mpr
        have ml:=mul_le_mul_of_nonneg_left hs hm0.le
        nlinarith only [lt_of_not_ge smallP,ml,mul_le_mul_of_nonneg_left ha hP.le,hm]
      obtain ⟨t,ht,p⟩:=nodes z (z+200*m/a) (le_add_of_nonneg_right (by positivity)) (by linarith)
      have lower:=charge hk N ha ea ht p
      have upper:=periodic_window hF hper (1/2) z (show 0≤200*m/a by positivity) plen
      change a^2/4<∫s in z..(z+200*m/a),|F s| at lower
      change (∫s in z..(z+200*m/a),|F s|)≤(1/2)*(200*m/a)+Real.sqrt (200*m/a*R) at upper
      exact amplitude_from_cost ha hm Rle (lower.trans_le upper)
    · exact max_le (by linarith) (by linarith [lt_of_not_ge ha])
  nlinarith only [bound,Jroot,mul_le_mul_of_nonneg_left ampl hm0.le,
    mul_nonneg hm0.le (Real.sqrt_nonneg m)]

end LengthGrowth.ActualFlow.CriticalDensity
#print axioms LengthGrowth.ActualFlow.CriticalDensity.scalar_bound
