import Migration.AngularReconstruction

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.AngularGauge

/-- Control of the derivative controls the part of a periodic scalar
observable that is not seen by its mean. The factor P/4 is sharp. -/
theorem periodic_mean_error {P M : ℝ} {f d : ℝ → ℝ} (pp : 0<P)
    (per : Function.Periodic f P) (df : ∀s,HasDerivAt f (d s) s)
    (cap : ∀s,|d s|≤M) (x : ℝ) : |f x-(∫s in (0:ℝ)..P,f s)/P|≤M*(P/4) := by
  let h := P/2
  have hn : 0≤h := by dsimp [h]; linarith
  have cf := continuous_iff_continuousAt.mpr (fun s => (df s).continuousAt)
  have lip (u v : ℝ) : |f u-f v|≤M*|u-v| :=
    (convex_univ (𝕜:=ℝ) (E:=ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun s _ => (df s).differentiableAt) (fun s _ => (df s).deriv ▸ cap s)
      (mem_univ v) (mem_univ u)
  let D := fun s=> (f x-f (x-s))+(f x-f (x+s))
  have cd : Continuous D := (continuous_const.sub (cf.comp (continuous_const.sub continuous_id))).add
    (continuous_const.sub (cf.comp (continuous_const.add continuous_id)))
  have bound (s : ℝ) (hs : s∈Icc 0 h) : |D s|≤(2*M)*s := by
    have l := lip x (x-s)
    have r := lip x (x+s)
    rw [show x-(x-s)=s by ring,abs_of_nonneg hs.1] at l
    rw [show x-(x+s)= -s by ring,abs_neg,abs_of_nonneg hs.1] at r
    exact (abs_add_le _ _).trans (by linarith only [l,r])
  have raw := (intervalIntegral.abs_integral_le_integral_abs (μ:=volume) (f:=D) hn).trans
    (intervalIntegral.integral_mono_on hn (cd.abs.intervalIntegrable ..)
      (g:=fun s =>(2*M)*s) ((continuous_id.const_mul _).intervalIntegrable ..) bound)
  have mean : (∫s in (0:ℝ)..h,D s)=P*f x-(∫s in (0:ℝ)..P,f s) := by
    have ciSub : IntervalIntegrable (fun s => f (x-s)) volume 0 h := (cf.comp (continuous_const.sub continuous_id)).intervalIntegrable ..
    have ciAdd : IntervalIntegrable (fun s => f (x+s)) volume 0 h := (cf.comp (continuous_const.add continuous_id)).intervalIntegrable ..
    have eq (s : ℝ) : D s=(2*f x)-(f (x-s)+f (x+s)) := by dsimp [D]; ring
    simp_rw [eq]
    rw [intervalIntegral.integral_sub (f:=fun _ => 2*f x) (g:=fun s=>f (x-s)+f (x+s))
      intervalIntegrable_const (ciSub.add ciAdd),intervalIntegral.integral_const,sub_zero,smul_eq_mul,
      intervalIntegral.integral_add (f:=fun s=>f (x-s)) (g:=fun s=>f (x+s)) ciSub ciAdd,
      intervalIntegral.integral_comp_sub_left f x,intervalIntegral.integral_comp_add_left f x,sub_zero,add_zero,
      intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable ..) (cf.intervalIntegrable ..)]
    have shift := per.intervalIntegral_add_eq (x-h) 0
    rw [show x+h=(x-h)+P by dsimp [h]; ring,shift]
    dsimp only [h]; ring
  have iid : (∫s in (0:ℝ)..h,s)=h^2/2 := by
    have d (s : ℝ) : HasDerivAt (fun z : ℝ => z^2/2) s s := by
      apply (((hasDerivAt_id s).pow 2).div_const 2).congr_deriv; dsimp; ring
    have ft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=h) (fun s _ => d s)
      (continuous_id.intervalIntegrable ..)
    simpa only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_div,sub_zero] using ft
  rw [mean,intervalIntegral.integral_const_mul,iid] at raw
  rw [show f x-(∫s in (0:ℝ)..P,f s)/P=(P*f x-(∫s in (0:ℝ)..P,f s))/P by field_simp,
    abs_div,abs_of_pos pp]
  apply (div_le_iff₀ pp).mpr
  dsimp only [h] at raw; linarith only [raw]

/-- A rigorous finite-grid height enclosure from uniform mean and slope
errors at two sections. The samples include both endpoints of one period. -/
theorem mesh_separates {P A₀ A₁ e₀ e₁ m₀ m₁ v₀ v₁ lo hi : ℝ}
    {Y₀ Y₁ Z₀ Z₁ DY₀ DY₁ DZ₀ DZ₁ : ℝ → ℝ} {n : ℕ}
    (pp : 0<P) (nn : 0<n)
    (p₀ : Function.Periodic (Y₀-Z₀) P) (p₁ : Function.Periodic (Y₁-Z₁) P)
    (dy₀ : ∀s,HasDerivAt Y₀ (DY₀ s) s) (dy₁ : ∀s,HasDerivAt Y₁ (DY₁ s) s)
    (dz₀ : ∀s,HasDerivAt Z₀ (DZ₀ s) s) (dz₁ : ∀s,HasDerivAt Z₁ (DZ₁ s) s)
    (cap₀ : ∀s,|DY₀ s-DZ₀ s|≤e₀) (cap₁ : ∀s,|DY₁ s-DZ₁ s|≤e₁)
    (mean₀ : |(∫s in (0:ℝ)..P,(Y₀-Z₀) s)/P|≤m₀)
    (mean₁ : |(∫s in (0:ℝ)..P,(Y₁-Z₁) s)/P|≤m₁)
    (speed₀ : ∀s,|DY₀ s|≤v₀) (speed₁ : ∀s,|DY₁ s|≤v₁)
    (initial : ∀i : ℕ,i≤n → Z₀ (i*(P/n))≤lo)
    (terminal : ∀i : ℕ,i≤n → hi≤Z₁ (i*(P/n)))
    (err₀ : lo+(m₀+e₀*(P/4))+v₀*(P/n/2)≤A₀)
    (err₁ : A₁≤hi-(m₁+e₁*(P/4))-v₁*(P/n/2)) (gap : A₀<A₁) :
    ∃ b : ℝ,(∀x∈Icc 0 P,Y₀ x<b) ∧ (∀x∈Icc 0 P,b<Y₁ x) := by
  have ng : (0:ℝ)<n := by exact_mod_cast nn
  let step := P/n
  have sp : 0<step := div_pos pp ng
  have grid (x : ℝ) (hx : x∈Icc 0 P) : ∃i : ℕ,i≤n ∧ |x-i*step|≤step/2 := by
    let i := ⌊x/step+1/2⌋₊
    have xi : 0≤x/step+1/2 := by linarith [div_nonneg hx.1 sp.le]
    have le := Nat.floor_le (a:=x/step+1/2) xi
    have lt := Nat.lt_floor_add_one (x/step+1/2)
    change (i:ℝ)≤x/step+1/2 at le
    change x/step+1/2<(i:ℝ)+1 at lt
    have xn : x/step≤n := (div_le_iff₀ sp).mpr (by dsimp [step]; field_simp; exact hx.2)
    have inn : i≤n := by
      by_contra! bad
      have more : (n:ℝ)+1 ≤ i := by exact_mod_cast bad
      linarith only [xn,le,more]
    refine ⟨i,inn,?_⟩
    rw [abs_le]
    have lo' : (i:ℝ)-1/2≤x/step := by linarith only [le]
    have hi' : x/step≤(i:ℝ)+1/2 := by linarith only [lt]
    have p := (le_div_iff₀ sp).mp lo'
    have q := (div_le_iff₀ sp).mp hi'
    exact ⟨by linarith only [p],by linarith only [q]⟩
  have estimate {Y Z DY DZ : ℝ→ℝ} {e m v : ℝ} (per : Function.Periodic (Y-Z) P)
      (dy : ∀s,HasDerivAt Y (DY s) s) (dz : ∀s,HasDerivAt Z (DZ s) s)
      (cap : ∀s,|DY s-DZ s|≤e) (means : |(∫s in (0:ℝ)..P,(Y-Z) s)/P|≤m)
      (speed : ∀s,|DY s|≤v) (x t : ℝ) (dist : |x-t|≤step/2) :
      |Y x-Z t|≤m+e*(P/4)+v*(step/2) := by
    let z := (∫s in (0:ℝ)..P,(Y-Z) s)/P
    have r := periodic_mean_error pp per (fun t => (dy t).sub (dz t)) cap t
    change |(Y t-Z t)-z|≤e*(P/4) at r
    have q : |Y t-Z t|≤e*(P/4)+m := calc
      _ = |((Y t-Z t)-z)+z| := by rw [sub_add_cancel]
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add r means)
    have lip : |Y x-Y t|≤v*|x-t| := (convex_univ (𝕜:=ℝ) (E:=ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun s _ => (dy s).differentiableAt) (fun s _ => (dy s).deriv ▸ speed s) (mem_univ t) (mem_univ x)
    have vn : 0≤v := (abs_nonneg _).trans (speed x)
    have bd := (abs_sub_le (Y x) (Y t) (Z t)).trans (add_le_add
      (lip.trans (mul_le_mul_of_nonneg_left dist vn)) q)
    linarith only [bd]
  refine ⟨(A₀+A₁)/2,?_,?_⟩
  · intro x hx
    obtain ⟨i,h,dist⟩ := grid x hx
    have error := estimate p₀ dy₀ dz₀ cap₀ mean₀ speed₀ x _ dist
    have e := (abs_le.mp error).2
    linarith only [initial i h,e,err₀,gap]
  · intro x hx
    obtain ⟨i,h,dist⟩ := grid x hx
    have error := estimate p₁ dy₁ dz₁ cap₁ mean₁ speed₁ x _ dist
    have e := (abs_le.mp error).1
    linarith only [terminal i h,e,err₁,gap]

end MigrationGeometry.AngularGauge
#print axioms MigrationGeometry.AngularGauge.mesh_separates
