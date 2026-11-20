import LengthGrowth.ActualFlow.FiniteSignMaterial
import LengthGrowth.ActualFlow.FiniteSignCharge
import LengthGrowth.ActualFlow.FiniteSignIntegrals
import LengthGrowth.ActualFlow.FiniteSignBudget

noncomputable section
open Set Function MeasureTheory Filter FreeElasticScalar
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace LengthGrowth.ActualFlow

theorem finiteSignScalarEstimate_exists (N : ℕ) : ∃C : ℝ, 0≤C ∧ FiniteSignScalarEstimate N C := by
  let m:ℝ:=N+1
  let P:=100*m
  let Q:=256*P*m
  have hm:1≤m:=by dsimp [m]; linarith [Nat.cast_nonneg (α:=ℝ) N]
  have hm0:0<m:=by linarith
  have hP:0<P:=by dsimp [P];positivity
  have hQ:1≤Q:=by dsimp [Q,P]; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) hm]
  have hQ0:0<Q:=by linarith
  refine ⟨2*m*(P^2+Q^2),by positivity,?_⟩
  intro k hk period nodes
  let B:=∫s in (0:ℝ)..1,k s^2
  let q:=Real.sqrt B
  let F:=FiniteSignWindow.force k
  let d:=∫s in (0:ℝ)..1,F s^2
  let c:=B*q/2
  let J:=∫s in (0:ℝ)..1,|F s|
  let R:=∫s in (0:ℝ)..1,(|F s|-c)^2
  have hB:0≤B:=intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _=>sq_nonneg _)
  have hd:0≤d:=intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _=>sq_nonneg _)
  have hR:0≤R:=intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _=>sq_nonneg _)
  have hq:0≤q:=Real.sqrt_nonneg _
  have q2:q^2=B:=Real.sq_sqrt hB
  have hc:0≤c:=by dsimp [c];positivity
  have hF:Continuous F:=FiniteSignWindow.force_continuous hk
  have hk' := (contDiff_infty_iff_deriv.mp hk).2
  have hp':=actual_deriv_periodic period (hk.differentiable (by simp))
  have hp'':=actual_deriv_periodic hp' (hk'.differentiable (by simp))
  have hper : Periodic F 1 := by
    intro s; unfold F FiniteSignWindow.force; rw [hp'',period]
  let e:=FiniteSignWindow.energy k
  have he : Continuous e := (hk'.continuous.pow 2).add ((hk.continuous.pow 4).div_const 4)
  obtain ⟨z,hz,maximal⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (show (0:ℝ)≤1 by norm_num))
    he.continuousOn
  let a:=fourthRoot (e z)
  have ha0:0≤a := fourthRoot_nonneg _
  have ea : e z=a^4 := (fourthRoot_pow_four (show 0≤e z by
    change 0≤(deriv k z)^2+(k z)^4/4;positivity)).symm
  have dv (s:ℝ) (hs:s∈Icc (0:ℝ) 1) : |deriv k s|≤a^2 := by
    have v:=maximal hs
    change (deriv k s)^2+k s^4/4≤e z at v
    rw [ea] at v
    by_contra! hh
    nlinarith only [mul_self_lt_mul_self (sq_nonneg a) hh,v,sq_abs (deriv k s),pow_nonneg (sq_nonneg (k s)) 2]
  have ode (s:ℝ) : HasDerivAt (deriv k) (F s-k s^3/2) s := by
    simpa [F,FiniteSignWindow.force] using (hk'.differentiable (by simp) s).hasDerivAt
  obtain ⟨n,hn,p⟩:=nodes 0 1 (by norm_num) (by norm_num)
  have hpart:=p.cubic_upper hk.continuous hF ode dv
  have hlow:=FiniteSignIntegrals.cubic_lower hk.continuous
  have hn' : (n:ℝ)≤m := by dsimp [m]; exact_mod_cast hn
  have cJ : c≤J+2*m*a^2 := by
    change B*q≤_ at hlow
    change _≤2*J+4*(n:ℝ)*a^2 at hpart
    dsimp [c];nlinarith only [hlow,hpart,mul_le_mul_of_nonneg_right hn' (sq_nonneg a)]
  have Jd : J≤Real.sqrt d:=FiniteSignIntegrals.integral_abs_unit hF
  change c≤Real.sqrt d+2*m*(P^2+Q^2)*(1+B)
  by_cases small : c≤Real.sqrt d
  · exact small.trans (le_add_of_nonneg_right (by positivity))
  have hcd : d<c^2 := by
    have h:=mul_self_lt_mul_self (Real.sqrt_nonneg d) (lt_of_not_ge small)
    nlinarith only [h,Real.sq_sqrt hd]
  have hR' : R≤4*c*m*a^2 := by
    have eR:=FiniteSignWindow.residual_mass F hF c
    change R=d-2*c*J+c^2 at eR
    nlinarith only [eR,hcd,mul_le_mul_of_nonneg_left cJ hc]
  have amp : a^2≤P^2+Q^2*B := by
    by_cases low : a≤P
    · nlinarith only [mul_self_le_mul_self ha0 low,mul_nonneg (sq_nonneg Q) hB]
    have high:=lt_of_not_ge low
    have ha:=hP.trans high
    have hl:0≤P/a := by positivity
    have hl1:P/a≤1 := (div_le_one ha).mpr high.le
    obtain ⟨n',hn',part⟩:=nodes z (z+P/a) (by linarith) (by linarith)
    have lower:=FiniteSignWindow.charge hk N ha ea hn' part
    have upper:=FiniteSignIntegrals.periodic_window hF hper c z hl hl1
    change a^2/4<∫s in z..(z+P/a),|F s| at lower
    change (∫s in z..(z+P/a),|F s|)≤c*(P/a)+Real.sqrt (P/a*R) at upper
    have ac : a^3<Q*c:=FiniteSignWindow.amplitude_budget ha hP hm hc hR hR' (lower.trans_le upper)
    have aq : a≤Q*q := by
      by_contra! hh
      have gt:=pow_lt_pow_left₀ hh (mul_nonneg hQ0.le hq) (by decide : 3≠0)
      have q3 : q^3=B*q := by rw [pow_succ,q2]
      rw [mul_pow,q3] at gt
      have Q3 : Q≤Q^3 := by
        nlinarith only [hQ,mul_nonneg hQ0.le (sub_nonneg.mpr hQ),mul_nonneg (sq_nonneg Q) (sub_nonneg.mpr hQ)]
      change a^3<Q*(B*q/2) at ac
      nlinarith only [ac,gt,mul_le_mul_of_nonneg_right Q3 (mul_nonneg hB hq),
        mul_nonneg hQ0.le (mul_nonneg hB hq)]
    have sq:=mul_self_le_mul_self ha0 aq
    nlinarith only [sq,show Q^2*q^2=Q^2*B by rw [q2],sq_nonneg P]
  nlinarith only [cJ,Jd,mul_le_mul_of_nonneg_left amp hm0.le,
    mul_nonneg (mul_nonneg hm0.le (sq_nonneg P)) hB,
    mul_nonneg hm0.le (sq_nonneg Q)]

/-- Uniformly bounded signed-curvature alternation on late slices gives a
near-quarter length bound and decay of the total bending energy. -/
theorem ForwardImmersion.log_quarter_and_decay_of_finite_sign (flow : ForwardImmersion)
    (hf : flow.IsNormalFEF) {N : ℕ} {T : ℝ} (hT : 0≤T)
    (nodes : ∀t, (ht:T<t) → let p:=flow.regularPositionAt (hT.trans ht.le)
      BoundedNodalCount (p.scaledArclengthCurvature p.length) N) :
    (∃ B : ℝ, 0<B ∧ ∀t≥T, flow.length t ≤ B*fourthRoot (1+t)*(1+Real.log (1+t))) ∧
      Tendsto flow.energy atTop (𝓝 0) := by
  obtain ⟨C,hC,estimate⟩:=finiteSignScalarEstimate_exists N
  exact flow.log_quarter_and_decay_of_scalar_finite_sign hf hT hC estimate nodes

end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.finiteSignScalarEstimate_exists
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.log_quarter_and_decay_of_finite_sign
