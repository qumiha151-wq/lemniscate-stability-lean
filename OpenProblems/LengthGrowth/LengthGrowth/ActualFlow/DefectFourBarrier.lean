import LengthGrowth.ActualFlow.DefectFourBins

namespace LengthGrowth.DefectFour
open Set
noncomputable section
set_option maxHeartbeats 1200000

private theorem cover (t : ℝ) (ht : 0≤t) (high : t≤501/1000) :
    ∃i : Fin 64, (leftQ i.val : ℝ)≤t ∧ t≤(rightQ i.val : ℝ) := by
  have aux (n : ℕ) (hn : 0<n) (h : t≤(leftQ n : ℝ)) :
      ∃k : ℕ, k<n ∧ (leftQ k : ℝ)≤t ∧ t≤(rightQ k : ℝ) := by
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases low : (leftQ n : ℝ)≤t
      · exact ⟨n,Nat.lt_succ_self _,low,by simpa [rightQ,leftQ] using h⟩
      · have pos : n≠0 := by rintro rfl; simp [leftQ,ht] at low
        obtain ⟨k,hk,l,u⟩ := ih (by omega) (le_of_not_ge low)
        exact ⟨k,by omega,l,u⟩
  obtain ⟨k,hk,l,u⟩ := aux 64 (by decide) (by norm_num [leftQ]; linarith)
  exact ⟨⟨k,hk⟩,l,u⟩

private theorem bin_estimate {l u v H t x g b p q Y : ℝ}
    (lt0 : 0≤l) (ltu : l≤t) (tu : t≤u) (ul : u≤501/1000)
    (x0 : 0≤x) (x1 : x≤4/5) (b0 : 0≤b) (bg : b≤g) (gv : g≤x*v)
    (v0 : 0≤v) (h0 : 0≤H) (sh : v^2-(7/44)*l^2≤H^2)
    (proj : p^2≤(t*b)^2-(7/44)*x^2*t^4) (_p0 : 0≤p)
    (qcap : q≤min 2 (10*u^2-8*l^4))
    (raw : let A := (3/2)*p+g*b/2
      A≤1 → Y≤ -4*(1-A)^2+q+16*t^3*b-(489/100)*(t*b)^2)
    (acap : (6/5)*u*H+((4/5)*v)^2/2≤27/100)
    (numerical : -4*(1-((6/5)*u*H+((4/5)*v)^2/2))^2+min 2 (10*u^2-8*l^4)+
      16*u^3*((4/5)*v)-(489/100)*(l*((4/5)*v))^2≤ -(1/40)) : Y≤ -(1/40) := by
  let A := (3/2)*p+g*b/2
  let B := (4/5)*v
  let D := (6/5)*u*H+B^2/2
  have t0 := lt0.trans ltu
  have u0 := t0.trans tu
  have gg := b0.trans bg
  have bB : b≤B := (bg.trans gv).trans (mul_le_mul_of_nonneg_right x1 v0)
  have gB : g≤B := gv.trans (mul_le_mul_of_nonneg_right x1 v0)
  have sqb := mul_self_le_mul_self b0 (bg.trans gv)
  have lt2 := pow_le_pow_left₀ lt0 ltu 2
  have rad : b^2-(7/44)*x^2*t^2 ≤ x^2*H^2 := by
    nlinarith only [sqb,mul_le_mul_of_nonneg_left sh (sq_nonneg x),
      mul_le_mul_of_nonneg_left lt2 (show 0≤(7/44:ℝ)*x^2 by positivity)]
  have ptx : p≤t*x*H := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith only [proj,mul_le_mul_of_nonneg_left rad (sq_nonneg t)]
  have pp : p≤u*(4/5)*H := ptx.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul tu x1 x0 u0) h0)
  have d0 : 0≤B^2-b^2 := by nlinarith only [mul_self_le_mul_self b0 bB]
  have delta : (B^2-b^2)/4≤D-A := by
    dsimp only [D,A]
    nlinarith only [pp,mul_le_mul_of_nonneg_right gB b0,sq_nonneg (B-b)]
  have aD : A≤D := by linarith only [delta,d0]
  have cap : D≤27/100 := acap
  have aa : A≤1 := by linarith only [aD,cap]
  have sqgain : (7/5)*(B^2-b^2)≤4*((1-A)^2-(1-D)^2) := by
    have m := mul_le_mul_of_nonneg_left delta (show 0≤4*(2-A-D) by linarith)
    have n := mul_le_mul_of_nonneg_right (show (7/5:ℝ)≤2-A-D by linarith) d0
    nlinarith only [m,n]
  have trig : 16*t^3*b≤16*u^3*B := by
    have h := mul_le_mul (pow_le_pow_left₀ t0 tu 3) bB b0 (pow_nonneg u0 _)
    linarith only [h]
  have loss : (489/100)*(l*B)^2-(489/100)*(t*b)^2≤(7/5)*(B^2-b^2) := by
    have t2 : t^2≤(501/1000:ℝ)^2 := pow_le_pow_left₀ t0 (tu.trans ul) 2
    have rate : (489/100)*t^2≤7/5 := by linarith only [t2]
    nlinarith only [mul_le_mul_of_nonneg_right rate d0,
      mul_le_mul_of_nonneg_right lt2 (sq_nonneg B)]
  have hY := raw aa
  change Y≤ -4*(1-A)^2+q+16*t^3*b-(489/100)*(t*b)^2 at hY
  change -4*(1-D)^2+_+16*u^3*B-(489/100)*(l*B)^2≤ -(1/40) at numerical
  linarith only [hY,sqgain,trig,loss,qcap,numerical]

/-- Uniform continuous-variable coercivity on the entire normalized parameter
region. p measures the mean-free quadratic term in the curvature. -/
theorem spectral_barrier {t x g b p q Y : ℝ} (t0 : 0≤t) (t1 : t≤501/1000)
    (x0 : 0≤x) (x1 : x≤4/5) (b0 : 0≤b) (bg : b≤g) (p0 : 0≤p)
    (fq : g≤x*(227/500+(17/500)*t)) (fx : g*t≤x*(81/500+(17/500)*t^2))
    (proj : p^2≤(t*b)^2-(7/44)*x^2*t^4)
    (q2 : q≤2) (qz : q≤10*t^2-8*t^4)
    (raw : let A := (3/2)*p+g*b/2
      A≤1 → Y≤ -4*(1-A)^2+q+16*t^3*b-(489/100)*(t*b)^2) :
    Y≤ -(1/40) := by
  obtain ⟨i,lo,hi⟩ := cover t t0 t1
  obtain ⟨v0,h0,branch,sh,_,cap,num⟩ := verified_bins i
  let l : ℝ := leftQ i
  let u : ℝ := rightQ i
  let v : ℝ := upperV i
  let H : ℝ := upperH i
  have l0 : 0≤l := by dsimp [l,leftQ]; positivity
  have ul : u≤501/1000 := by
    have n := i.isLt
    have nr : (i.val:ℝ)≤63 := by exact_mod_cast (show i.val≤63 by omega)
    dsimp [u,rightQ]; push_cast; linarith
  have gv : g≤x*v := by
    rcases branch with h|⟨lp,h⟩
    · have r : (227/500:ℝ)+(17/500)*u≤v := by dsimp only [u,v]; simpa only [Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_neg,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,Rat.cast_min] using (Rat.cast_le (K:=ℝ)).mpr h
      exact fq.trans (mul_le_mul_of_nonneg_left (by linarith only [hi,r]) x0)
    · have lp' : 0<l := by dsimp only [l]; exact_mod_cast lp
      have r : (81/500:ℝ)/l+(17/500)*u≤v := by simpa only [Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_neg,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,Rat.cast_min] using (Rat.cast_le (K:=ℝ)).mpr h
      have tpos := lp'.trans_le lo
      have scale : (81/500:ℝ)/t≤(81/500:ℝ)/l := div_le_div_of_nonneg_left (by norm_num) lp' lo
      have g' : g≤x*((81/500)/t+(17/500)*t) := by
        apply (le_div_iff₀ tpos).mpr fx |>.trans_eq
        field_simp [tpos.ne']
      exact g'.trans (mul_le_mul_of_nonneg_left (by linarith only [scale,hi,r]) x0)
  have qu : q≤min 2 (10*u^2-8*l^4) := le_min q2 (by
    nlinarith only [qz,pow_le_pow_left₀ t0 hi 2,pow_le_pow_left₀ l0 lo 4])
  apply bin_estimate l0 lo hi ul x0 x1 b0 bg gv (by dsimp only [v]; exact_mod_cast v0)
    (h0 := show 0≤H by dsimp only [H]; exact_mod_cast h0) (by dsimp only [v,H,l]; simpa only [Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_neg,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,Rat.cast_min] using (Rat.cast_le (K:=ℝ)).mpr sh) proj p0 qu raw
  · unfold corrQ capQ at cap
    dsimp only [u,H,v]
    simpa only [Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_neg,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,Rat.cast_min] using (Rat.cast_le (K:=ℝ)).mpr cap
  · unfold corrQ capQ linQ at num
    dsimp only [u,H,v,l]
    simpa only [Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_neg,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,Rat.cast_min] using (Rat.cast_le (K:=ℝ)).mpr num

end
end LengthGrowth.DefectFour
#print axioms LengthGrowth.DefectFour.spectral_barrier
