import SolitonClassification.CentreCriticalLayer
import SolitonClassification.OuterStressDirection

noncomputable section
open Set
namespace ClosedSimilarity.OuterStress.Data

/-- Uniform off-axis control on the whole initial slow-time interval. -/
theorem centre_initial_across :
    ∃ C ≥ 0, ∀ {δ : ℝ} (z : Data δ), 0<δ →
      z.K 0=0 → z.V 0=1 → z.p 0=0 → z.q 0=0 →
      ∀ u ∈ Icc (0:ℝ) (1/2), |z.across u| ≤ C*δ := by
  obtain ⟨D,hD,poly⟩ := bounded_correctors 2 (by norm_num)
  refine ⟨12*D+4,by positivity,?_⟩
  intro δ z hd hk hv hp hq u hu
  let T := (1/2:ℝ)
  let seg := Icc (0:ℝ) T
  have h0 : (0:ℝ) ∈ seg := ⟨le_rfl,by norm_num [T]⟩
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
  have drift : |J u|≤4*D*δ := by
    have bd (x : ℝ) (hx : x∈seg) : ‖deriv J x‖≤4*D*δ := by
      have rates := z.normalized_rates x (pp x hx) hd
      have rr : z.root x^2=z.amplitude x := Real.sq_sqrt (pp x hx).le
      have r4 : 1/4 ≤ z.root x^4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) (low x hx) 2, congrArg (·^2) rr]
      rw [(impact_rate rates).deriv,Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos hd,abs_of_pos (pow_pos rates.pos _)]
      apply (div_le_iff₀ (pow_pos rates.pos _)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left (data x hx).1 hd.le,
        mul_le_mul_of_nonneg_left r4 (mul_nonneg hD hd.le)]
    have H := (convex_Icc (0:ℝ) T).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (impact_rate (z.normalized_rates x (pp x hx) hd)).differentiableAt) bd h0 hu
    have j0 : J 0=0 := by simp [J,impact,FrozenStress.psi,across,transverse,shape,along,radial,hk,hv,hp,hq]
    change |J u-J 0|≤4*D*δ*|u-0| at H
    rw [j0,sub_zero,sub_zero,abs_of_nonneg hu.1] at H
    change |J u|≤4*D*δ*u at H
    exact H.trans (mul_le_of_le_one_right (by positivity) (by linarith [hu.2] : u≤1))
  have r2 : z.root u^2=z.amplitude u := Real.sq_sqrt (pp u hu).le
  have rlo : 1/2≤z.root u := le_of_sq_le_sq (by nlinarith [low u hu]) (Real.sqrt_nonneg _)
  have hpsi : |FrozenStress.psi (z.shape u) (z.slope u) (z.along u) (z.across u) / z.root u^2|≤2*D := by
    rw [abs_div,abs_of_nonneg (sq_nonneg (z.root u))]
    apply (div_le_iff₀ (by linarith [low u hu])).mpr
    rw [r2]
    nlinarith only [(data u hu).2.1,mul_le_mul_of_nonneg_left (low u hu) hD]
  have corr := abs_sub_le (FrozenStress.psi (z.shape u) (z.slope u) (z.along u) (z.across u)/z.root u^2)
    0 (z.shape u)
  simp only [sub_zero,zero_sub,abs_neg] at corr
  have v := abs_add_le (J u)
    (δ*(FrozenStress.psi (z.shape u) (z.slope u) (z.along u) (z.across u)/z.root u^2-z.shape u))
  have id : J u+δ*(FrozenStress.psi (z.shape u) (z.slope u) (z.along u) (z.across u)/z.root u^2-z.shape u) =
      z.root u*z.across u := by dsimp [J,impact]; ring
  rw [id,abs_mul,abs_of_nonneg (show 0≤z.root u from Real.sqrt_nonneg _),abs_mul,abs_of_pos hd] at v
  nlinarith only [v,drift,mul_le_mul_of_nonneg_left (corr.trans (add_le_add hpsi (data u hu).2.2)) hd.le,
    mul_le_mul_of_nonneg_right rlo (abs_nonneg (z.across u))]

end ClosedSimilarity.OuterStress.Data
#print axioms ClosedSimilarity.OuterStress.Data.centre_initial_across
