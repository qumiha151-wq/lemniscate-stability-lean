import SolitonClassification.CentreShotWinding

noncomputable section
open Set
namespace ClosedSimilarity.OuterStress.Data

/-- A fixed slow-time displacement along the stress direction for every true
    high-slope centre shot. The bounded oscillator primitive U w supplies a
    lower mean for U²/2 without any prior averaging hypothesis. -/
theorem centre_alignment {δ : ℝ} (z : Data δ) (hd : 0<δ) (small : δ≤1/32)
    (hk : z.K 0=0) (hv : z.V 0=1) (hp : z.p 0=0) (hq : z.q 0=0) :
    1/288 ≤ z.along (1/2) := by
  let seg := Icc (0:ℝ) (1/2)
  have zero : (0:ℝ) ∈ seg := ⟨le_rfl,by norm_num⟩
  have last : (1/2:ℝ) ∈ seg := ⟨by norm_num,le_rfl⟩
  have short (x : ℝ) (hx : x∈seg) :
      1/2 ≤ z.amplitude x ∧ z.p x^2+z.q x^2≤(1/2:ℝ)^2 := by
    obtain ⟨pq,amp⟩ := z.centre_bounds hd hk hv hp hq hx.1
    have xx := pow_le_pow_left₀ hx.1 hx.2 2
    exact ⟨by nlinarith,pq.trans xx⟩
  have ap (x : ℝ) (hx : x∈seg) : 0<z.amplitude x := by linarith [(short x hx).1]
  have bd (x : ℝ) (hx : x∈seg) : ‖deriv z.amplitude x‖ ≤ 1 := by
    have a := ap x hx
    have A : |z.V x|≤z.amplitude x := le_of_sq_le_sq
      (by rw [sq_abs]; nlinarith [z.amplitude_sq x,sq_nonneg (z.K x^2/2)]) a.le
    have p : |z.p x|≤1 := le_of_sq_le_sq
      (by rw [sq_abs]; nlinarith [(short x hx).2,sq_nonneg (z.q x)]) zero_le_one
    rw [(z.amplitude_hasDerivAt x a hd).deriv,Real.norm_eq_abs,abs_div,abs_of_pos a,
      abs_mul,abs_neg,div_le_one a]
    exact (mul_le_mul p A (abs_nonneg _) zero_le_one).trans (by simp)
  have amp0 : z.amplitude 0=1 := by norm_num [amplitude,hk,hv]
  have upper (x : ℝ) (hx : x∈seg) : z.amplitude x≤2 := by
    have h := (convex_Icc (0:ℝ) (1/2)).norm_image_sub_le_of_norm_deriv_le
      (fun y hy => (z.amplitude_hasDerivAt y (ap y hy) hd).differentiableAt) bd zero hx
    simp only [Real.norm_eq_abs,sub_zero,one_mul,abs_of_nonneg hx.1,amp0] at h
    linarith [(abs_le.mp h).2,hx.2]
  let F := fun x => 18*z.along x+δ*(z.shape x*z.slope x)-x/4
  have der (x : ℝ) (hx : x∈seg) : ∃ d≥0, HasDerivAt F d x := by
    let u := z.shape x^2/2
    let p := z.slope x*z.along x + u*z.across x
    let r := z.root x
    let v := r/δ + z.shape x*p/(2*r^2)
    have rates := z.normalized_rates x (ap x hx) hd
    have pos : 0<r := rates.pos
    have rsq : r^2=z.amplitude x := Real.sq_sqrt (ap x hx).le
    have rlo : 1/2≤r := le_of_sq_le_sq (by nlinarith [(short x hx).1]) pos.le
    have rhi : r≤2 := le_of_sq_le_sq (by nlinarith [upper x hx]) (by norm_num)
    have osc : u^2+z.slope x^2=1 := rates.oscillator
    have u0 : 0≤u := by dsimp [u]; positivity
    have u1 : u≤1 := le_of_sq_le_sq (by nlinarith [sq_nonneg (z.slope x)]) zero_le_one
    have U : |z.shape x| ≤ 2 := le_of_sq_le_sq
      (by rw [sq_abs]; dsimp [u] at u1; linarith) (by norm_num)
    have frame := z.radius_sq x (ap x hx)
    have H := (short x hx).2
    have b : |z.across x|≤1/2 := le_of_sq_le_sq
      (by rw [sq_abs]; nlinarith [sq_nonneg (z.along x)]) (by norm_num)
    have psmall : |p|≤1/2 := by
      apply le_of_sq_le_sq _ (by norm_num)
      rw [sq_abs]
      have exact_square : p^2+(u*z.along x-z.slope x*z.across x)^2 =
          z.along x^2+z.across x^2 := by
        dsimp [p]
        linear_combination (z.along x^2+z.across x^2)*osc
      nlinarith [sq_nonneg (u*z.along x-z.slope x*z.across x)]
    have err : |z.shape x*p/(2*r^2)|≤1 := by
      rw [abs_div,abs_of_pos (by positivity : 0<2*r^2),abs_mul,div_le_one (by positivity)]
      nlinarith only [mul_le_mul U psmall (abs_nonneg _) (by norm_num),rsq,(short x hx).1]
    have vd : δ*v = r+δ*(z.shape x*p/(2*r^2)) := by dsimp [v]; field_simp
    have vmin : 1/4≤δ*v := by
      nlinarith only [vd,rlo,small,mul_le_mul_of_nonneg_left (abs_le.mp err).1 hd.le]
    have vmax : δ*v≤3 := by
      nlinarith only [vd,rhi,small,mul_le_mul_of_nonneg_left (abs_le.mp err).2 hd.le]
    let a := u-p*u*z.across x/r^2
    have amin : u/2≤a := by
      have pb := (le_abs_self (p*z.across x)).trans ((abs_mul p _).symm ▸
        mul_le_mul psmall b (abs_nonneg _) (by norm_num))
      have lhs : p*z.across x ≤ r^2/2 := by nlinarith only [pb,rsq,(short x hx).1]
      have D := mul_le_mul_of_nonneg_right lhs u0
      have div : p*u*z.across x/r^2 ≤ u/2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
      dsimp [a]; linarith
    have prod : HasDerivAt (fun t => z.shape t*z.slope t) ((1-3*u^2)*v) x := by
      convert! rates.dU.mul rates.dw using 1
      change (1-3*u^2)*v = z.slope x*v*z.slope x+z.shape x*(-z.shape x^3/2*v)
      dsimp [u] at *
      linear_combination -v*osc
    have fd : HasDerivAt F (18*a+δ*((1-3*u^2)*v)-1/4) x := by
      exact (((rates.da.const_mul 18).add (prod.const_mul δ)).sub ((hasDerivAt_id x).div_const 4))
    refine ⟨_,?_,fd⟩
    have uu : u^2≤u := by nlinarith [mul_nonneg u0 (sub_nonneg.mpr u1)]
    nlinarith only [amin,vmin,uu,mul_le_mul_of_nonneg_left vmax (sq_nonneg u)]
  have mono : MonotoneOn F seg := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun x hx => (der x hx).choose_spec.2.continuousAt.continuousWithinAt)
      (fun x hx => (der x (interior_subset hx)).choose_spec.2.differentiableAt.differentiableWithinAt)
    intro x hx
    obtain ⟨d,hd',h⟩ := der x (interior_subset hx)
    rw [h.deriv]; exact hd'
  have comp := mono zero last (by norm_num)
  have initial : F 0 = 0 := by simp [F,along,radial,shape,hk,hv,hp,hq]
  rw [initial] at comp
  have osc := (z.normalized_rates (1/2) (ap _ last) hd).oscillator
  have U : |z.shape (1/2)|≤2 := le_of_sq_le_sq
    (by rw [sq_abs]; nlinarith [sq_nonneg (z.slope (1/2)),sq_nonneg ((z.shape (1/2))^2/2-1)]) (by norm_num)
  have w : |z.slope (1/2)|≤1 := le_of_sq_le_sq
    (by rw [sq_abs]; nlinarith [sq_nonneg ((z.shape (1/2))^2/2)]) zero_le_one
  have uv : z.shape (1/2)*z.slope (1/2)≤2 := (le_abs_self _).trans (by
    rw [abs_mul]; simpa using mul_le_mul U w (abs_nonneg _) (by norm_num))
  dsimp [F] at comp
  nlinarith only [mul_le_mul_of_nonneg_left uv hd.le,comp,small]

end ClosedSimilarity.OuterStress.Data
#print axioms ClosedSimilarity.OuterStress.Data.centre_alignment
