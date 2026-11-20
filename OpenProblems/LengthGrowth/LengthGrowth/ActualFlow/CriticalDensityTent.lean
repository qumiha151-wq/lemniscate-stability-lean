import LengthGrowth.ActualFlow.CriticalDensityPieces
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The linear collar test on one interval omitting a strict half-amplitude excursion. -/
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.CriticalDensity

private def charge (u F : ℝ → ℝ) (s : ℝ) : ℝ :=
  (3/2:ℝ)*u s^2-2*|F s|-1/2

private theorem charge_cont {u F : ℝ → ℝ} (cu : Continuous u) (cf : Continuous F) :
    Continuous (charge u F) :=
  (((cu.pow 2).const_mul (3/2:ℝ)).sub (cf.abs.const_mul 2)).sub continuous_const

private theorem collar_loss {u r A : ℝ} (hA : 1≤A) (hu : -(1/2:ℝ)≤u) (cap : u≤2*A)
    (hr : 0≤r) (hr1 : r≤1) :
    (3/2:ℝ)*u^2 ≤ r*u^3+1/2+4/(r+1/(2*A))^2 := by
  have pa : 0<2*A := by linarith
  let t := r+1/(2*A)
  have pt : 0<t := add_pos_of_nonneg_of_pos hr (one_div_pos.mpr pa)
  change _ ≤ r*u^3+1/2+4/t^2
  rcases le_or_gt 0 u with pu|nu
  · have small : (1/(2*A))*u≤1 := by
      rw [one_div,mul_comm,← div_eq_mul_inv,div_le_one pa]
      exact cap
    have first : (3/2:ℝ)*u^2-r*u^3 ≤ 3*u^2-t*u^3 := by
      dsimp [t]
      nlinarith only [mul_le_mul_of_nonneg_right small (sq_nonneg u),sq_nonneg u]
    have cubic : (3*u^2-t*u^3)*t^2≤4 := by
      nlinarith only [mul_nonneg (sq_nonneg (t*u-2)) (show 0≤t*u+1 by positivity)]
    have second := (le_div_iff₀ (sq_pos_of_pos pt)).mpr cubic
    linarith only [first,second]
  · have u2 : u^2≤1/4 := by
      nlinarith only [mul_nonneg (show 0≤u+1/2 by linarith) (show 0≤1/2-u by linarith)]
    have u3 : -(1/8:ℝ)≤u^3 := by
      nlinarith only [mul_nonneg (show 0≤u+1/2 by linarith) (sq_nonneg (u-1/4)),hu]
    have r3 : -(1/8:ℝ)≤r*u^3 := by nlinarith only [mul_le_mul_of_nonneg_left u3 hr,hr1]
    linarith only [u2,r3,show 0≤4/t^2 by positivity]

private theorem flat_loss {u : ℝ} (hu : -(1/2:ℝ)≤u) :
    (3/2:ℝ)*u^2≤u^3+1/2 := by
  nlinarith only [mul_nonneg (sq_nonneg (u-1)) (show 0≤u+1/2 by linarith)]

private theorem piece_bound {a b slope : ℝ} {u v F r j G : ℝ → ℝ}
    (hab : a≤b) (du : ∀ s, HasDerivAt u (v s) s)
    (dv : ∀ s, HasDerivAt v (F s-u s^3/2) s) (cF : Continuous F)
    (dr : ∀ s, HasDerivAt r slope s) (dj : ∀ s∈Icc a b, HasDerivAt j (G s) s)
    (cg : ContinuousOn G (Icc a b)) (hr : ∀ s∈Icc a b, r s∈Icc 0 1)
    (loss : ∀ s∈Icc a b, (3/2:ℝ)*u s^2≤r s*u s^3+1/2+G s) :
    (∫ s in a..b, charge u F s) ≤
      j b-j a-2*(r b*v b-slope*u b-(r a*v a-slope*u a)) := by
  have cu := continuous_iff_continuousAt.mpr fun s => (du s).continuousAt
  have cr := continuous_iff_continuousAt.mpr fun s => (dr s).continuousAt
  let w := fun s => G s-2*(r s*(F s-u s^3/2))
  let W := fun s => j s-2*(r s*v s-slope*u s)
  have dw (s) (hs : s∈Icc a b) : HasDerivAt W (w s) s := by
    apply ((dj s hs).sub (((((dr s).mul (dv s)).sub ((du s).const_mul slope))).const_mul 2)).congr_deriv
    dsimp [w]
    ring
  have cw : ContinuousOn w (Icc a b) :=
    cg.sub (((cr.mul (cF.sub ((cu.pow 3).div_const 2))).const_mul 2).continuousOn)
  have p := intervalIntegral.integral_mono_on (μ := volume) hab
    ((charge_cont cu cF).intervalIntegrable a b) (cw.intervalIntegrable_of_Icc hab)
    (fun s hs => show charge u F s≤w s by
      have rf : r s*F s≤|F s| := calc
        _ ≤ r s*|F s| := mul_le_mul_of_nonneg_left (le_abs_self _) (hr s hs).1
        _ ≤ 1*|F s| := mul_le_mul_of_nonneg_right (hr s hs).2 (abs_nonneg _)
        _ = _ := one_mul _
      dsimp [charge,w]
      linarith only [loss s hs,rf])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => dw s (by simpa [uIcc_of_le hab] using hs))
    (cw.intervalIntegrable_of_Icc hab)] at p
  dsimp [W] at p
  linarith only [p]

private theorem collar_bound {a b slope A : ℝ} {u v F r : ℝ → ℝ}
    (hab : a≤b) (hA : 1≤A) (hslope : slope=1 ∨ slope= -1)
    (du : ∀ s, HasDerivAt u (v s) s) (dv : ∀ s, HasDerivAt v (F s-u s^3/2) s)
    (cF : Continuous F) (dr : ∀ s, HasDerivAt r slope s)
    (hr : ∀ s∈Icc a b, r s∈Icc 0 1)
    (hu : ∀ s∈Icc a b, -(1/2:ℝ)≤u s) (cap : ∀ s∈Icc a b, u s≤2*A) :
    (∫ s in a..b, charge u F s) ≤
      8*A-2*(r b*v b-slope*u b-(r a*v a-slope*u a)) := by
  let c := 1/(2*A)
  let j := fun s => -4*slope/(r s+c)
  have pa : 0<2*A := by linarith
  have pc : 0<c := one_div_pos.mpr pa
  have pos (s) (hs : s∈Icc a b) : 0<r s+c := add_pos_of_nonneg_of_pos (hr s hs).1 pc
  have cr := continuous_iff_continuousAt.mpr fun s => (dr s).continuousAt
  have dj (s) (hs : s∈Icc a b) : HasDerivAt j (4/(r s+c)^2) s := by
    apply (((dr s).add_const c).inv (pos s hs).ne' |>.const_mul (-4*slope)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun x => show -4*slope/(r x+c) = _ by
        change -4*slope/(r x+c) = -4*slope*(r x+c)⁻¹
        rw [div_eq_mul_inv]))
      |>.congr_deriv
    rcases hslope with h|h <;> rw [h] <;> ring
  have bound := piece_bound (u:=u) (v:=v) (F:=F) (r:=r) (j:=j) hab du dv cF dr dj
    (continuousOn_const.div ((cr.continuousOn.add continuousOn_const).pow 2)
      (fun s hs => pow_ne_zero 2 (pos s hs).ne')) hr
    (fun s hs => collar_loss hA (hu s hs) (cap s hs) (hr s hs).1 (hr s hs).2)
  have fin (s : ℝ) (hs : s∈Icc a b) : 4/(r s+c)≤8*A := by
    apply (div_le_iff₀ (pos s hs)).mpr
    have eq : (2*A)*c=1 := by dsimp [c]; field_simp
    nlinarith only [eq,mul_nonneg (show 0≤A by linarith) (hr s hs).1]
  have top : j b-j a≤8*A := by
    have ha : a∈Icc a b := ⟨le_rfl,hab⟩
    have hb : b∈Icc a b := ⟨hab,le_rfl⟩
    rcases hslope with h|h
    · simp only [j,h,mul_one,neg_div]
      linarith only [fin a ha,show 0≤4/(r b+c) from div_nonneg (by norm_num) (pos b hb).le]
    · simp only [j,h,mul_neg_one,neg_neg]
      linarith only [fin b hb,show 0≤4/(r a+c) from div_nonneg (by norm_num) (pos a ha).le]
  linarith only [bound,top]

private theorem single_tent {a b A : ℝ} {u v F : ℝ → ℝ}
    (hab : a≤b) (hA : 1≤A)
    (du : ∀ s, HasDerivAt u (v s) s) (dv : ∀ s, HasDerivAt v (F s-u s^3/2) s)
    (cF : Continuous F) (hu : ∀ s∈Icc a b, -(1/2:ℝ)≤u s)
    (cap : ∀ s∈Icc a b, |u s|≤2*A) :
    (∫ s in a..b, charge u F s) ≤ 32*A := by
  let m := min 1 ((b-a)/2)
  let x := a+m
  let y := b-m
  have mp : 0≤m := le_min (by norm_num) (by linarith)
  have m1 : m≤1 := min_le_left _ _
  have mh : m≤(b-a)/2 := min_le_right _ _
  have ax : a≤x := by dsimp [x]; linarith
  have xy : x≤y := by dsimp [x,y]; linarith
  have yb : y≤b := by dsimp [y]; linarith
  have left : Icc a x ⊆ Icc a b := Icc_subset_Icc_right (xy.trans yb)
  have right : Icc y b ⊆ Icc a b := Icc_subset_Icc_left (ax.trans xy)
  have cap' (s) (hs : s∈Icc a b) : u s≤2*A := (abs_le.mp (cap s hs)).2
  have l := collar_bound (u:=u) (v:=v) (F:=F) (r:=fun s => s-a)
    ax hA (Or.inl rfl) du dv cF (fun s => (hasDerivAt_id s).sub_const a)
    (fun s hs => ⟨sub_nonneg.mpr hs.1,by have := hs.2; dsimp [x] at this; linarith⟩)
    (fun s hs => hu s (left hs)) (fun s hs => cap' s (left hs))
  have r := collar_bound (u:=u) (v:=v) (F:=F) (r:=fun s => b-s)
    yb hA (Or.inr rfl) du dv cF (fun s => ((hasDerivAt_id s).const_sub b))
    (fun s hs => ⟨sub_nonneg.mpr hs.2,by have := hs.1; dsimp [y] at this; linarith⟩)
    (fun s hs => hu s (right hs)) (fun s hs => cap' s (right hs))
  have mid : (∫ s in x..y, charge u F s) ≤ -2*(m*v y-m*v x) := by
    rcases le_or_gt 1 ((b-a)/2) with hlong|hshort
    · have hm : m=1 := min_eq_left hlong
      have mid := piece_bound (u:=u) (v:=v) (F:=F) (r:=fun _ => m) (j:=fun _ => 0)
        (G:=fun _ => 0) xy du dv cF (fun s => hasDerivAt_const s m)
        (fun s _ => hasDerivAt_const s 0) continuousOn_const (fun _ _ => ⟨mp,m1⟩)
        (fun s hs => by
          have h := flat_loss (hu s ⟨ax.trans hs.1,hs.2.trans yb⟩)
          simpa only [hm,one_mul,add_zero] using h)
      linarith only [mid]
    · have hm : m=(b-a)/2 := min_eq_right hshort.le
      have e : x=y := by dsimp [x,y]; rw [hm]; ring
      simp [e]
  have cc := charge_cont (continuous_iff_continuousAt.mpr fun s => (du s).continuousAt) cF
  have join := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (cc.intervalIntegrable a x) (cc.intervalIntegrable x y)
  have finish := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (cc.intervalIntegrable a y) (cc.intervalIntegrable y b)
  have xeq : x-a=m := by dsimp [x]; ring
  have yeq : b-y=m := by dsimp [y]; ring
  simp only [xeq,yeq,sub_self,zero_mul,one_mul,neg_one_mul] at l r
  have ea := (abs_le.mp (cap a ⟨le_rfl,hab⟩)).1
  have eb := (abs_le.mp (cap b ⟨hab,le_rfl⟩)).1
  have ex := cap' x ⟨ax,xy.trans yb⟩
  have ey := cap' y ⟨ax.trans xy,yb⟩
  linarith only [l,r,mid,join,finish,ea,eb,ex,ey]

/-- Half-amplitude excursions alone suffice. The number of smaller
oscillations in any of the supplied intervals can be arbitrary. -/
theorem Pieces.tent_mass {k v F : ℝ→ℝ} {n : ℕ} {a b A : ℝ}
    (part : Pieces k (1/2) n a b) (hA : 1≤A)
    (hk : ∀ s, HasDerivAt k (v s) s) (hv : ∀ s, HasDerivAt v (F s-k s^3/2) s)
    (hF : Continuous F) (cap : ∀ s∈Icc a b, |k s|≤2*A) :
    (3/2:ℝ)*(∫ s in a..b, k s^2) ≤ 2*(∫ s in a..b, |F s|)+(b-a)/2+32*(n:ℝ)*A := by
  have ck := continuous_iff_continuousAt.mpr fun s => (hk s).continuousAt
  have cc := charge_cont ck hF
  have H : (∫ s in a..b, charge k F s) ≤ 32*(n:ℝ)*A := by
    induction part with
    | empty => simp
    | @append n a b d prev hbd sign ih =>
      have hab := prev.ordered
      have localCap (s) (hs : s∈Icc b d) := cap s ⟨hab.trans hs.1,hs.2⟩
      have one : (∫ s in b..d, charge k F s)≤32*A := by
        rcases sign with pos|neg
        · exact single_tent hbd hA hk hv hF pos localCap
        · have dv (s) : HasDerivAt (fun x => -v x) (-F s-(-k s)^3/2) s := by
            apply (hv s).neg.congr_deriv
            ring
          have h := single_tent (u:=fun s => -k s) (v:=fun s => -v s) (F:=fun s => -F s)
            hbd hA (fun s => (hk s).neg) dv hF.neg (fun s hs => by have := neg s hs; linarith)
            (fun s hs => by simpa only [abs_neg] using localCap s hs)
          simpa only [charge,abs_neg,neg_sq] using h
      have hprev := ih (fun s hs => cap s ⟨hs.1,hs.2.trans hbd⟩)
      have join := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
        (cc.intervalIntegrable a b) (cc.intervalIntegrable b d)
      push_cast
      linarith only [one,hprev,join]
  have expansion : (∫ s in a..b, charge k F s) =
      (3/2:ℝ)*(∫ s in a..b, k s^2)-2*(∫ s in a..b, |F s|)-(b-a)/2 := by
    unfold charge
    rw [intervalIntegral.integral_sub
      (f:=fun s => (3/2:ℝ)*k s^2-2*|F s|) (g:=fun _ => (1/2:ℝ))
      ((((ck.pow 2).const_mul (3/2:ℝ)).sub (hF.abs.const_mul 2)).intervalIntegrable ..)
      intervalIntegrable_const, intervalIntegral.integral_sub
      (f:=fun s => (3/2:ℝ)*k s^2) (g:=fun s => 2*|F s|)
      (((ck.pow 2).const_mul _).intervalIntegrable ..) ((hF.abs.const_mul 2).intervalIntegrable ..),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const,smul_eq_mul]
    ring
  linarith only [H,expansion]

#print axioms Pieces.tent_mass
end LengthGrowth.ActualFlow.CriticalDensity
