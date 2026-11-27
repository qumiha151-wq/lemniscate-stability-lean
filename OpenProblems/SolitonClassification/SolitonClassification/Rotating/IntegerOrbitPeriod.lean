import SolitonClassification.Rotating.PrimitiveSupportPeriod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set MeasureTheory Function
namespace SolitonClassification.Rotating.IntegerOrbitPeriod
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An elementary period bound for an autonomous orbit. The field needs
a Lipschitz bound only on the image of that orbit. -/
theorem four_le_lipschitz_period {f g : ℝ → E} {P K : ℝ} (pp : 0<P) (kn : 0≤K)
    (per : Periodic f P) (cg : Continuous g) (df : ∀s,HasDerivAt f (g s) s)
    (lip : ∀s t, ‖g s-g t‖≤K*‖f s-f t‖) (moves : ∃ s,g s≠0) : 4≤K*P := by
  have gp : Periodic g P := by
    intro s
    have bd := lip (s+P) s
    rw [per s,sub_self,norm_zero,mul_zero,norm_le_zero_iff,sub_eq_zero] at bd
    exact bd
  obtain ⟨v,hv,mx⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr pp.le) cg.norm.continuousOn
  let M := ‖g v‖
  have cap (s : ℝ) : ‖g s‖≤M := by
    obtain ⟨t,ht,eq⟩ := gp.exists_mem_Ico₀ pp s
    rw [eq]; exact mx (Ico_subset_Icc_self ht)
  obtain ⟨s,sm⟩ := moves
  have mp : 0<M := (norm_pos_iff.mpr sm).trans_le (cap s)
  have vel (s t : ℝ) : ‖f s-f t‖≤M*|s-t| := by
    exact (convex_univ (𝕜:=ℝ) (E:=ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => (df x).differentiableAt) (fun x _ => (df x).deriv ▸ cap x)
      (mem_univ t) (mem_univ s)
  let h := P/2
  have hp : 0≤h := by dsimp [h]; linarith
  let D := fun t => (g v-g (v+t))+(g v-g (v-t))
  have cd : Continuous D :=
    (continuous_const.sub (cg.comp (continuous_const.add continuous_id))).add
      (continuous_const.sub (cg.comp (continuous_const.sub continuous_id)))
  let H := fun t : ℝ => (2*t) • g v - (f (v+t)-f (v-t))
  have dH (t : ℝ) : HasDerivAt H (D t) t := by
    have plus : HasDerivAt (fun x => f (v+x)) (g (v+t)) t := by
      simpa [Function.comp_def] using (df (v+t)).scomp t ((hasDerivAt_id t).const_add v)
    have minus : HasDerivAt (fun x => f (v-x)) (-(g (v-t))) t := by
      simpa [Function.comp_def] using (df (v-t)).scomp t ((hasDerivAt_id t).const_sub v)
    apply ((((hasDerivAt_id t).const_mul 2).smul_const (g v)).sub (plus.sub minus)).congr_deriv
    dsimp only [D]; simp only [mul_one]; module
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=h)
    (fun t _ => dH t) (cd.intervalIntegrable ..)
  have cycle : f (v+h)=f (v-h) := by
    rw [show v+h=(v-h)+P by dsimp [h]; ring,per (v-h)]
  have val : (∫ t in (0:ℝ)..h,D t)=P • g v := by
    rw [integral]
    dsimp only [H]
    rw [cycle,sub_self,sub_zero,add_zero,sub_zero,sub_self,mul_zero,zero_smul,sub_zero,sub_zero]
    rw [show 2*h=P by dsimp [h]; ring]
  have point (t : ℝ) (ht : t∈Icc 0 h) : ‖D t‖≤(2*K*M)*t := by
    have pl := (lip v (v+t)).trans (mul_le_mul_of_nonneg_left (vel v (v+t)) kn)
    have mi := (lip v (v-t)).trans (mul_le_mul_of_nonneg_left (vel v (v-t)) kn)
    rw [show v-(v+t)= -t by ring,abs_neg,abs_of_nonneg ht.1] at pl
    rw [show v-(v-t)=t by ring,abs_of_nonneg ht.1] at mi
    exact (norm_add_le _ _).trans (by linarith only [pl,mi])
  have ub := intervalIntegral.integral_mono_on hp (cd.norm.intervalIntegrable (μ:=volume) 0 h)
    (g:=fun t=> (2*K*M)*t) ((continuous_id.const_mul _).intervalIntegrable ..) point
  have whole := (intervalIntegral.norm_integral_le_integral_norm (f:=D) hp).trans ub
  rw [val,norm_smul,Real.norm_eq_abs,abs_of_pos pp,intervalIntegral.integral_const_mul] at whole
  have intId : (∫t in (0:ℝ)..h,t)=h^2/2 := by
    have d (t : ℝ) : HasDerivAt (fun x : ℝ => x^2/2) t t := by
      apply (((hasDerivAt_id t).pow 2).div_const 2).congr_deriv; dsimp; ring
    have ft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=h)
      (fun t _ => d t) (continuous_id.intervalIntegrable ..)
    simpa only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_div,sub_zero] using ft
  rw [intId] at whole
  change P*M≤2*K*M*(h^2/2) at whole
  have mm : 4*(P*M)≤K*P*(P*M) := by dsimp only [h] at whole; nlinarith only [whole]
  exact le_of_mul_le_mul_right mm (mul_pos pp mp)


abbrev Support := Fin 4 → ℝ
def supportVelocity (b : ℝ) (x : Support) : Support :=
  fun i => field (![x 0,x 1,x 2,x 3,b,0] : State) (i.castLE (by decide))

/-- Explicit Lipschitz constant for the actual support ODE in the outer
box used by both halves of the winding-one certificate. -/
theorem support_velocity_lipschitz {b : ℝ} (hb : |b|≤1/5) {x y : Support}
    (hx : ∀ i, |x i|≤9) (hy : ∀ i, |y i|≤9) :
    ‖supportVelocity b x-supportVelocity b y‖≤18*‖x-y‖ := by
  let D := ‖x-y‖
  have dn : 0≤D := norm_nonneg _
  have diff (i : Fin 4) : |x i-y i|≤D := norm_le_pi_norm (x-y) i
  have product (i j : Fin 4) : |x i*x j-y i*y j|≤18*D := calc
    _ = |(x i-y i)*x j+y i*(x j-y j)| := by congr 1; ring
    _ ≤ |(x i-y i)*x j|+|y i*(x j-y j)| := abs_add_le _ _
    _ ≤ D*9+9*D := by rw [abs_mul,abs_mul]; gcongr <;> first | apply diff | apply hx | apply hy
    _ = _ := by ring
  have cube : |x 0^3-y 0^3|≤243*D := calc
    _ = |(x 0-y 0)*(x 0^2+x 0*y 0+y 0^2)| := by congr 1; ring
    _ ≤ D*(|x 0|^2+|x 0| *|y 0|+|y 0|^2) := by
      rw [abs_mul]; gcongr
      · apply diff
      · calc
          _ ≤ |x 0^2+x 0*y 0|+|y 0^2| := abs_add_le _ _
          _ ≤ |x 0^2|+|x 0*y 0|+|y 0^2| := by gcongr; exact abs_add_le _ _
          _ = _ := by rw [abs_pow,abs_pow,abs_mul]
    _ ≤ D*((9:ℝ)^2+9*9+9^2) := by gcongr <;> first | apply hx | apply hy
    _ = _ := by ring
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i; fin_cases i
  · change |8*x 1-8*y 1|≤18*D
    rw [← mul_sub,abs_mul]; norm_num
    linarith only [diff 1,dn]
  · change |(-x 0^3/16-x 2/8-b*x 3/8)-(-y 0^3/16-y 2/8-b*y 3/8)|≤18*D
    calc
      _ = |-(x 0^3-y 0^3)/16-(x 2-y 2)/8-b*(x 3-y 3)/8| := by congr 1; ring
      _ ≤ |-(x 0^3-y 0^3)/16-(x 2-y 2)/8|+|b*(x 3-y 3)/8| := abs_sub _ _
      _ ≤ (|-(x 0^3-y 0^3)/16|+|(x 2-y 2)/8|)+|b*(x 3-y 3)/8| := by gcongr; exact abs_sub _ _
      _ ≤ 243*D/16+D/8+((1:ℝ)/5)*D/8 := by
        simp only [abs_div,abs_neg,abs_mul,show |(16:ℝ)|=16 by norm_num,show |(8:ℝ)|=8 by norm_num]
        gcongr <;> first | exact cube | apply diff
      _ ≤ _ := by linarith only [dn]
  · change |-x 0*x 3- -y 0*y 3|≤18*D
    rw [show -x 0*x 3- -y 0*y 3= -(x 0*x 3-y 0*y 3) by ring,abs_neg]
    exact product 0 3
  · change |1+x 0*x 2-(1+y 0*y 2)|≤18*D
    rw [add_sub_add_left_eq_sub]
    exact product 0 2

/-- For this genuine four-coordinate flow a geometric period below 64
can have only prime divisors from the finite range used in the certificate. -/
theorem primitive_of_winding_prime_checks {z : ℝ → Support} {P b : ℝ} (pp : 0<P) (ps : P<64)
    (per : Periodic z P) (hb : |b|≤1/5) (cap : ∀s i,|z s i|≤9)
    (der : ∀s,HasDerivAt z (supportVelocity b (z s)) s) (moves : ∃ s,supportVelocity b (z s)≠0)
    (checks : ∀ p : ℕ, p.Prime → p≤300 → z (P/p)≠z 0) :
    IsLeast {s : ℝ | Periodic z s ∧ 0<s} P := by
  let g := fun s => supportVelocity b (z s)
  have cz : Continuous z := continuous_iff_continuousAt.mpr fun s => (der s).continuousAt
  have cv : Continuous (supportVelocity b) := by
    apply continuous_pi; intro i; fin_cases i <;> simp [supportVelocity,field] <;> fun_prop
  have bound {s : ℝ} (sp : 0<s) (hper : Periodic z s) : 4≤18*s :=
    four_le_lipschitz_period sp (by norm_num) hper (cv.comp cz) der
      (fun v w => support_velocity_lipschitz hb (cap v) (cap w)) moves
  let S := PrimitiveSupportPeriod.periods z
  have hP : P ∈ S := per
  have dis : Disjoint (S : Set ℝ) (Ioo 0 (1/5)) := by
    apply Set.disjoint_left.mpr
    intro s hs ht
    linarith only [bound ht.1 (show Periodic z s from hs),ht.2]
  have nb : S≠⊥ := by
    intro eq; rw [eq] at hP; exact pp.ne' (by simpa using hP)
  obtain ⟨d,hd⟩ := AddSubgroup.exists_isLeast_pos nb (by norm_num : (0:ℝ)<1/5) dis
  have dp : 0<d := hd.1.2
  have pd : Periodic z d := hd.1.1
  have least := bound dp pd
  rw [AddSubgroup.cyclic_of_min hd,AddSubgroup.mem_closure_singleton] at hP
  obtain ⟨n,hn⟩ := hP
  rw [zsmul_eq_mul] at hn
  have npos : 0<(n:ℝ) := by
    by_contra! bad
    linarith only [mul_nonpos_of_nonpos_of_nonneg bad dp.le,hn,pp]
  have nz : 0≤n := by exact_mod_cast npos.le
  lift n to ℕ using nz
  norm_cast at hn npos
  have ncap : n≤300 := by
    have nr : (n:ℝ)<300 := by
      nlinarith only [mul_le_mul_of_nonneg_left least (show (0:ℝ)≤n by positivity),hn,ps]
    exact_mod_cast nr.le
  have one : n=1 := by
    by_contra bad
    obtain ⟨p,prime,k,hk⟩ := Nat.exists_prime_and_dvd bad
    have pn := Nat.le_of_dvd npos (show p ∣ n from ⟨k,hk⟩)
    have tm : P/p=(k:ℝ)*d := by
      rw [← hn,hk,Nat.cast_mul]; field_simp [(show (p:ℝ)≠0 by exact_mod_cast prime.ne_zero)]
    exact checks p prime (pn.trans ncap) (by rw [tm]; simpa using (pd.nat_mul k) 0)
  have eq : d=P := by simpa [one] using hn
  exact ⟨⟨per,pp⟩,fun _ hs => eq ▸ hd.2 hs⟩


def speeds : Support := ![40,47,81,82]

theorem support_velocity_speed {b : ℝ} (hb : |b|≤1/5) {x : Support}
    (hx : ∀i,|x i|≤9) (hu : |x 1|≤5) (i : Fin 4) :
    |supportVelocity b x i|≤speeds i := by
  fin_cases i
  · change |8*x 1|≤40
    rw [abs_mul]; norm_num; linarith
  · change |-x 0^3/16-x 2/8-b*x 3/8|≤47
    calc
      _ ≤ |-x 0^3/16-x 2/8|+|b*x 3/8| := abs_sub _ _
      _ ≤ (|-x 0^3/16|+|x 2/8|)+|b*x 3/8| := by gcongr; exact abs_sub _ _
      _ = |x 0|^3/16+|x 2|/8+|b| *|x 3|/8 := by simp [abs_div,abs_mul,abs_pow]
      _ ≤ (9:ℝ)^3/16+9/8+(1/5)*9/8 := by gcongr <;> apply hx
      _ ≤ _ := by norm_num
  · change |-x 0*x 3|≤81
    rw [abs_mul,abs_neg]; exact (mul_le_mul (hx 0) (hx 3) (abs_nonneg _) (by norm_num)).trans (by norm_num)
  · change |1+x 0*x 2|≤82
    calc
      _ ≤ |(1:ℝ)|+|x 0*x 2| := abs_add_le _ _
      _ ≤ 1+9*9 := by rw [abs_one,abs_mul]; gcongr <;> apply hx
      _ ≤ _ := by norm_num

/-- Only coordinate comparisons at the rounded reference nodes are needed.
All propagation from the nodal comparisons to true nonreturns and a least
positive period uses the actual ODE. -/
theorem primitive_of_winding_grid {z : ℝ → Support} {P b δ : ℝ} (pp : 0<P) (ps : P<64)
    (per : Periodic z P) (hb : |b|≤1/5) (cap : ∀s i,|z s i|≤9) (ucap : ∀s,|z s 1|≤5)
    (der : ∀s,HasDerivAt z (supportVelocity b (z s)) s) (moves : ∃ s,supportVelocity b (z s)≠0)
    (ref : ℕ → Support) (initial : Support) (time : ℕ → ℝ)
    (start : ∀i, |z 0 i-initial i|≤δ)
    (sample : ∀p : ℕ,p.Prime → p≤300 → ∀i,|z (time p) i-ref p i|≤δ)
    (gap : ∀p : ℕ,p.Prime → p≤300 → ∃i, 2*δ+speeds i*|P/p-time p| < |ref p i-initial i|) :
    IsLeast {s : ℝ | Periodic z s ∧ 0<s} P := by
  apply primitive_of_winding_prime_checks pp ps per hb cap der moves
  intro p prim pc eq
  obtain ⟨i,large⟩ := gap p prim pc
  have dv (s) : HasDerivAt (fun t=>z t i) (supportVelocity b (z s) i) s :=
    (hasDerivAt_pi.mp (der s)) i
  have speed : |z (P/p) i-z (time p) i|≤speeds i*|P/p-time p| :=
    (convex_univ (𝕜:=ℝ) (E:=ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun s _ => (dv s).differentiableAt) (fun s _ => (dv s).deriv ▸ support_velocity_speed hb (cap s) (ucap s) i)
      (mem_univ (time p)) (mem_univ (P/p))
  have lim : |ref p i-initial i|≤2*δ+speeds i*|P/p-time p| := calc
    _ ≤ |ref p i-z (time p) i|+|z (time p) i-initial i| := abs_sub_le _ _ _
    _ ≤ |ref p i-z (time p) i|+(|z (time p) i-z 0 i|+|z 0 i-initial i|) := by gcongr; exact abs_sub_le _ _ _
    _ ≤ _ := by
      have sa : |ref p i-z (time p) i|≤δ := by rw [abs_sub_comm]; exact sample p prim pc i
      have nm : |z (time p) i-z 0 i|≤speeds i*|P/p-time p| := by rw [abs_sub_comm,← eq]; exact speed
      linarith only [sa,nm,start i]
  exact (not_le_of_gt large) lim

end SolitonClassification.Rotating.IntegerOrbitPeriod
#print axioms SolitonClassification.Rotating.IntegerOrbitPeriod.four_le_lipschitz_period
#print axioms SolitonClassification.Rotating.IntegerOrbitPeriod.primitive_of_winding_prime_checks
#print axioms SolitonClassification.Rotating.IntegerOrbitPeriod.primitive_of_winding_grid
