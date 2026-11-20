import SolitonClassification.CentreShotAlignment

noncomputable section
open Set
namespace ClosedSimilarity.OuterStress

/-- Common bounds for the two corrector remainders and the unscaled correction
    polynomial, valid below any prescribed finite amplitude. -/
theorem bounded_correctors (M : ℝ) (_hM : 0≤M) :
    ∃ C ≥ 0, ∀ A U w a b : ℝ, |A|≤M → |U|≤M → |w|≤M → |a|≤M → |b|≤M →
      |impactRemainder A U w a b|≤C ∧ |amplitudeRemainder A U w a b|≤C ∧
      |FrozenStress.psi U w a b|≤C ∧ |Q U w a b|≤C := by
  let f (x : Fin 5 → ℝ) := |impactRemainder (x 0) (x 1) (x 2) (x 3) (x 4)|+
    |amplitudeRemainder (x 0) (x 1) (x 2) (x 3) (x 4)|+|FrozenStress.psi (x 1) (x 2) (x 3) (x 4)|+
    |Q (x 1) (x 2) (x 3) (x 4)|
  have hf : Continuous f := by unfold f impactRemainder amplitudeRemainder FrozenStress.remJ FrozenStress.psi Q; fun_prop
  let box : Set (Fin 5→ℝ) := Icc (fun _ => -M) (fun _ => M)
  have compact : IsCompact box := isCompact_Icc
  obtain ⟨C,hC⟩ := compact.bddAbove_image hf.continuousOn
  refine ⟨max C 0,le_max_right ..,?_⟩
  intro A U w a b hA hU hw ha hb
  let x : Fin 5→ℝ := ![A,U,w,a,b]
  have hx (i : Fin 5) : |x i|≤M := by fin_cases i <;> assumption
  have inside : x ∈ box := ⟨fun i => (abs_le.mp (hx i)).1,fun i => (abs_le.mp (hx i)).2⟩
  have bound := (hC (mem_image_of_mem f inside)).trans (le_max_left C 0)
  change |impactRemainder A U w a b|+|amplitudeRemainder A U w a b|+|FrozenStress.psi U w a b|+
    |Q U w a b| ≤ _ at bound
  exact ⟨by linarith [abs_nonneg (amplitudeRemainder A U w a b),abs_nonneg (FrozenStress.psi U w a b),abs_nonneg (Q U w a b)],
      by linarith [abs_nonneg (impactRemainder A U w a b),abs_nonneg (FrozenStress.psi U w a b),abs_nonneg (Q U w a b)],
      by linarith [abs_nonneg (impactRemainder A U w a b),abs_nonneg (amplitudeRemainder A U w a b),abs_nonneg (Q U w a b)],
      by linarith [abs_nonneg (impactRemainder A U w a b),abs_nonneg (amplitudeRemainder A U w a b),abs_nonneg (FrozenStress.psi U w a b)]⟩

namespace Data

/-- A genuine entry slice with uniformly positive longitudinal displacement
    and O(δ) transverse displacement for every high-slope physical centre shot. -/
theorem centre_entry :
    ∃ C ≥ 0, ∀ {δ : ℝ} (z : Data δ), 0<δ → δ≤1/32 →
      z.K 0=0 → z.V 0=1 → z.p 0=0 → z.q 0=0 →
      1/288 ≤ z.along (1/2) ∧ |z.across (1/2)|≤C*δ ∧
      |impact δ z.root z.shape z.slope z.along z.across (1/2)|≤C*δ ∧
      1/2≤z.amplitude (1/2) ∧ z.amplitude (1/2)≤3/2 := by
  obtain ⟨D,hD,poly⟩ := bounded_correctors 2 (by norm_num)
  refine ⟨12*D+4,by positivity,?_⟩
  intro δ z hd small hk hv hp hq
  let T := (1/2:ℝ)
  let seg := Icc (0:ℝ) T
  have h0 : (0:ℝ) ∈ seg := ⟨le_rfl,by norm_num [T]⟩
  have hT : T ∈ seg := ⟨by norm_num [T],le_rfl⟩
  have pq (x : ℝ) (hx : x∈seg) := (z.centre_bounds hd hk hv hp hq hx.1).1
  have low (x : ℝ) (hx : x∈seg) : 1/2≤z.amplitude x := by
    have a := (z.centre_bounds hd hk hv hp hq hx.1).2
    have xx := pow_le_pow_left₀ hx.1 hx.2 2
    dsimp [T] at xx; nlinarith
  have pp (x : ℝ) (hx : x∈seg) : 0<z.amplitude x := by linarith [low x hx]
  have az : z.amplitude 0=1 := by norm_num [amplitude,hk,hv]
  have upper (x : ℝ) (hx : x∈seg) : z.amplitude x≤3/2 := by
    have hbound (t : ℝ) (ht : t∈seg) : ‖deriv z.amplitude t‖ ≤ 1 := by
      have ap := pp t ht
      have V : |z.V t|≤z.amplitude t := le_of_sq_le_sq
        (by rw [sq_abs]; nlinarith [z.amplitude_sq t,sq_nonneg (z.K t^2/2)]) ap.le
      have P : |z.p t|≤1 := le_of_sq_le_sq
        (by rw [sq_abs]; nlinarith [pq t ht,sq_nonneg (z.q t), pow_le_pow_left₀ ht.1 ht.2 2,
          show T^2≤1 by norm_num [T]]) zero_le_one
      rw [(z.amplitude_hasDerivAt t ap hd).deriv,Real.norm_eq_abs,abs_div,abs_of_pos ap,abs_mul,
        abs_neg,div_le_one ap]
      simpa using mul_le_mul P V (abs_nonneg _) zero_le_one
    have H := (convex_Icc (0:ℝ) T).norm_image_sub_le_of_norm_deriv_le
      (fun y hy => (z.amplitude_hasDerivAt y (pp y hy) hd).differentiableAt) hbound h0 hx
    simp only [Real.norm_eq_abs,sub_zero,one_mul,abs_of_nonneg hx.1,az] at H
    have cap : x≤(1/2:ℝ) := hx.2
    linarith [(abs_le.mp H).2]
  let J := impact δ z.root z.shape z.slope z.along z.across
  have data (x : ℝ) (hx : x∈seg) :
      |impactRemainder (z.root x^2) (z.shape x) (z.slope x) (z.along x) (z.across x)| ≤ D ∧
      |FrozenStress.psi (z.shape x) (z.slope x) (z.along x) (z.across x)|≤D ∧ |z.shape x|≤2 := by
    have f := z.radius_sq x (pp x hx)
    have b := pq x hx
    have xx := pow_le_pow_left₀ hx.1 hx.2 2
    dsimp [T] at xx
    have o := (z.normalized_rates x (pp x hx) hd).oscillator
    have U : |z.shape x|≤2 := le_of_sq_le_sq
      (by rw [sq_abs]; nlinarith [sq_nonneg (z.slope x),sq_nonneg ((z.shape x)^2/2-1)]) (by norm_num)
    have bounds := poly (z.root x^2) (z.shape x) (z.slope x) (z.along x) (z.across x)
      (by rw [abs_of_nonneg (sq_nonneg _),show z.root x^2=z.amplitude x from Real.sq_sqrt (pp x hx).le]; linarith [upper x hx])
      U (le_of_sq_le_sq (by rw [sq_abs]; nlinarith [sq_nonneg ((z.shape x)^2/2)]) (by norm_num))
      (le_of_sq_le_sq (by rw [sq_abs]; nlinarith [sq_nonneg (z.across x)]) (by norm_num))
      (le_of_sq_le_sq (by rw [sq_abs]; nlinarith [sq_nonneg (z.along x)]) (by norm_num))
    exact ⟨bounds.1,bounds.2.2.1,U⟩
  have drift : |J T|≤4*D*δ := by
    have bd (x : ℝ) (hx : x∈seg) : ‖deriv J x‖≤4*D*δ := by
      have rates := z.normalized_rates x (pp x hx) hd
      have rr : z.root x^2=z.amplitude x := Real.sq_sqrt (pp x hx).le
      have r4 : 1/4 ≤ z.root x^4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) (low x hx) 2, congrArg (·^2) rr]
      rw [(impact_rate rates).deriv,Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos hd,abs_of_pos (pow_pos rates.pos _)]
      apply (div_le_iff₀ (pow_pos rates.pos _)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left (data x hx).1 hd.le,
        mul_le_mul_of_nonneg_left r4 (mul_nonneg hD hd.le)]
    have H := (convex_Icc (0:ℝ) T).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (impact_rate (z.normalized_rates x (pp x hx) hd)).differentiableAt) bd h0 hT
    have j0 : J 0=0 := by simp [J,impact,FrozenStress.psi,across,transverse,shape,along,radial,hk,hv,hp,hq]
    change |J T-J 0|≤4*D*δ*|T-0| at H
    rw [j0,sub_zero,sub_zero,abs_of_nonneg hT.1] at H
    change |J T|≤4*D*δ*(1/2) at H
    nlinarith only [H,mul_nonneg hD hd.le]
  have r2 : z.root T^2=z.amplitude T := Real.sq_sqrt (pp T hT).le
  have rlo : 1/2≤z.root T := le_of_sq_le_sq (by nlinarith [low T hT]) (Real.sqrt_nonneg _)
  have hpsi : |FrozenStress.psi (z.shape T) (z.slope T) (z.along T) (z.across T) / z.root T^2|≤2*D := by
    rw [abs_div,abs_of_nonneg (sq_nonneg (z.root T))]
    apply (div_le_iff₀ (by linarith [low T hT])).mpr
    rw [r2]
    nlinarith only [(data T hT).2.1,mul_le_mul_of_nonneg_left (low T hT) hD]
  have corr := abs_sub_le (FrozenStress.psi (z.shape T) (z.slope T) (z.along T) (z.across T)/z.root T^2)
    0 (z.shape T)
  simp only [sub_zero,zero_sub,abs_neg] at corr
  have v := abs_add_le (J T)
    (δ*(FrozenStress.psi (z.shape T) (z.slope T) (z.along T) (z.across T)/z.root T^2-z.shape T))
  have id : J T+δ*(FrozenStress.psi (z.shape T) (z.slope T) (z.along T) (z.across T)/z.root T^2-z.shape T) =
      z.root T*z.across T := by dsimp [J,impact]; ring
  rw [id,abs_mul,abs_of_nonneg (show 0≤z.root T from Real.sqrt_nonneg _),abs_mul,abs_of_pos hd] at v
  refine ⟨z.centre_alignment hd small hk hv hp hq,?_,?_,low T hT,upper T hT⟩
  · change |z.across T|≤(12*D+4)*δ
    nlinarith only [v,drift,mul_le_mul_of_nonneg_left (corr.trans (add_le_add hpsi (data T hT).2.2)) hd.le,
      mul_le_mul_of_nonneg_right rlo (abs_nonneg (z.across T))]
  · change |J T|≤(12*D+4)*δ
    nlinarith only [drift,mul_nonneg hD hd.le,hd]

end Data
end ClosedSimilarity.OuterStress

namespace ClosedSimilarity.GlobalSupport
open OuterStress

theorem physical_centre_entry :
    ∃ C≥0, ∀ b : ℝ, (hb : 32≤b) →
      let z := centreData b (by linarith)
      1/288 ≤ z.along (1/2) ∧ |z.across (1/2)|≤C*b⁻¹ ∧
      |impact b⁻¹ z.root z.shape z.slope z.along z.across (1/2)|≤C*b⁻¹ ∧
      1/2≤z.amplitude (1/2) ∧ z.amplitude (1/2)≤3/2 := by
  obtain ⟨C,hC,all⟩ := OuterStress.Data.centre_entry
  refine ⟨C,hC,?_⟩
  intro b hb
  have p : 0<b := by linarith
  have small : b⁻¹≤1/32 := by rw [←one_div]; exact one_div_le_one_div_of_le (by norm_num) hb
  apply all (centreData b p) (inv_pos.mpr p) small
  all_goals simp [centreData,ofSupport,solution_zero,p.ne']

end ClosedSimilarity.GlobalSupport
#print axioms ClosedSimilarity.OuterStress.Data.centre_entry
#print axioms ClosedSimilarity.GlobalSupport.physical_centre_entry
