import SolitonClassification.Rotating.IntegerTerminalRows
namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set Metric DyadicReset
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private theorem grid_cover (N : ℕ) (hN : 0<N) (v : ℝ) (h0 : 0≤v) (h1 : v≤N) :
    ∃i : ℕ, i<N ∧ ∃t∈unitCell, v=(i:ℝ)+t := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h : 0<N ∧ v≤N
    · obtain ⟨i,lo,t,ht,e⟩ := ih h.1 h.2
      exact ⟨i,by omega,t,ht,e⟩
    · have low : (N:ℝ)≤v := by
        by_cases hn : N=0
        · simpa only [hn,Nat.cast_zero] using h0
        · exact le_of_not_ge (fun q => h ⟨by omega,q⟩)
      refine ⟨N,by omega,v-N,⟨by linarith,by push_cast at h1; linarith⟩,by ring⟩

private theorem scaled_box {n : ℤ} {T : PolynomialTape n 4000} {q : Fin 6→ℚ}
    {cols : ParameterMatrix} (data : TapeNumbers T q cols) {c : Parameters} (hc : c∈cube)
    {endt η : ℝ} (distT : |endt-4000*step n|≤1/10^30) (hη : η∈unitCell) :
    StateBox (wideFlow (η*endt,shootingInitial phase c)) := by
  let a := shootingInitial phase c
  have cnt : (0:ℕ)<4000 := by decide
  obtain ⟨i,hi,t,ht,he⟩ := grid_cover 4000 cnt (4000*η) (by nlinarith [hη.1])
    (by norm_num; linarith [hη.2])
  have transfer := fixed_time_shooting_bounds T data.stepSmall data.origin a
    (in_arm_ball data hc) i hi t ht
  have p := transfer.2.2.1
  have st : ((i:ℝ)+t)*step n=η*(4000*step n) := by rw [←he]; ring
  rw [st] at p
  have dt : |η*endt-η*(4000*step n)|≤1/10^30 := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hη.1]
    exact (mul_le_mul hη.2 distT (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have time := lipschitzWith_iff_norm_sub_le.mp (wide_time_lip a) (η*endt) (η*(4000*step n))
  rw [Real.norm_eq_abs] at time
  norm_num only [NNReal.coe_ofNat] at time
  have dis : ‖wideFlow (η*endt,a)-path (T.data i) d t‖≤1 :=
    (norm_sub_le_norm_sub_add_norm_sub _ (wideFlow (η*(4000*step n),a)) _).trans (by linarith)
  intro j hj
  have inner := (lift_inner (T.small i hi) ht).1 j hj
  change |path (T.data i) d t j|≤9 at inner
  have diff := (coordinate_bound (wideFlow (η*endt,a)-path (T.data i) d t) j).trans dis
  change |wideFlow (η*endt,a) j-path (T.data i) d t j|≤1 at diff
  have tri := abs_add_le (wideFlow (η*endt,a) j-path (T.data i) d t j) (path (T.data i) d t j)
  rw [sub_add_cancel] at tri
  change |wideFlow (η*endt,a) j|≤10
  linarith

theorem half_step : center 2=4000*step Middle.hn := by
  have h : centerQ 2=4000*((Middle.hn:ℚ)/(Middle.hd:ℚ)) := by decide +kernel
  simpa only [center,step,Rat.cast_mul,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat] using
    congrArg (fun r:ℚ => (r:ℝ)) h
theorem minus_half_step : -(center 2)=4000*step (-Middle.hn) := by
  rw [half_step]
  simp only [step,Int.cast_neg]
  ring

/-- Only the two signed finite tapes and their identifiable boundary rows are
inputs. Thus all analytic, geometric and irrational-target implications for
one complete winding are accounted for before the remaining rows are replayed. -/
theorem closed_immersion_of_certified_tapes
    (P : PolynomialTape Middle.hn 4000) (M : PolynomialTape (-Middle.hn) 4000)
    (p0 : P.node 0=initialNode) (m0 : M.node 0=initialNode)
    (pn : ∀j : ℕ,(P.data 3999 j).sum=(plusNode[j]?).getD 0)
    (mn : ∀j : ℕ,(M.data 3999 j).sum=(minusNode[j]?).getD 0) :
    ∃c∈cube, ∃I : WindingOneImmersion (c 4) (2*c 2),
      60<2*c 2 ∧ 2*c 2<62 ∧ 1/10<c 4 ∧ c 4<11/100 ∧ 7<I.k 0 ∧
      (∃s, I.k s<0) ∧ c 4*(I.x 0*deriv I.x 0+I.y 0*deriv I.y 0)≠0 := by
  have pos := plus_numbers P p0 pn
  have neg := minus_numbers M m0 mn
  have err (c : Parameters) (hc : c∈cube) : |c 2-center 2|≤1/10^30 :=
    (norm_le_pi_norm (c-center) 2).trans (show ‖c-center‖≤1/(10:ℝ)^30 from hc)
  have opposite (c : Parameters) (hc : c∈cube) : |-(c 2)-(-(center 2))|≤1/10^30 := by
    rw [show -(c 2)-(-(center 2))= -(c 2-center 2) by ring,abs_neg]
    exact err c hc
  have pArm := arm_from_tape P pos (forwardEndpointInput phase) (fun _ => rfl)
    half_step err
  have mArm := arm_from_tape M neg (backwardEndpointInput phase) (fun _ => rfl)
    minus_half_step opposite
  apply immersion_of_shooting_bounds wideFlow selectedDerivative pArm mArm
      (fun c _ => wideFlow_zero (shootingInitial phase c))
  intro c hc s hs
  have T0 : 0<c 2 := by
    have he := (abs_le.mp (err c hc)).1
    have hq : (30:ℚ)<centerQ 2 := by decide +kernel
    have hreal : (30:ℝ)<center 2 := by
      simpa only [center,Rat.cast_ofNat] using (Rat.cast_lt (K:=ℝ)).mpr hq
    linarith
  have box : StateBox (wideFlow (s,shootingInitial phase c)) := by
    by_cases h : 0≤s
    · have hη : s/c 2∈unitCell :=
        ⟨div_nonneg h T0.le,(div_le_one T0).mpr hs.2⟩
      have e := scaled_box pos hc (endt:=c 2) (η:=s/c 2) (by rw [←half_step]; exact err c hc) hη
      simpa only [div_mul_cancel₀ _ T0.ne'] using e
    · have hη : (-s)/c 2∈unitCell :=
        ⟨div_nonneg (by linarith) T0.le,(div_le_one T0).mpr (by linarith [hs.1])⟩
      have e := scaled_box neg hc (endt:= -(c 2)) (η:=(-s)/c 2)
        (by rw [←minus_half_step]; exact opposite c hc) hη
      simpa only [mul_neg,div_mul_cancel₀ _ T0.ne',neg_neg] using e
  simpa only [wideField,wideClip_id box] using wideFlow_time (shootingInitial phase c) s

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.closed_immersion_of_certified_tapes
