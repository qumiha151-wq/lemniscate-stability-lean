import LengthGrowth.ActualFlow.CriticalDensityMaterial

/-! A complete short-turn curvature lobe has small cubic mass relative
to the force it consumes. The estimates allow arbitrary length. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace LengthGrowth.ActualFlow.MacroscopicTurning

theorem small_turn_cubic {k : ℝ→ℝ} {a b : ℝ} (hk : ContDiff ℝ ∞ k)
    (ab : a≤b) (ka : k a=0) (kb : k b=0)
    (small : (∫s in a..b,|k s|)≤1/4) :
    (∫s in a..b, |k s|^3) ≤ (32/31:ℝ)*(∫s in a..b,|k s|)^2*(∫s in a..b,|FiniteSignWindow.force k s|) := by
  let v:=deriv k
  let f:=FiniteSignWindow.force k
  let θ:=∫s in a..b, |k s|
  let Y:=∫s in a..b, v s^2
  let J:=∫s in a..b, |f s|
  have ck:=hk.continuous
  have hv:= (contDiff_infty_iff_deriv.mp hk).2
  have cv:Continuous v:=hv.continuous
  have cf : Continuous f := FiniteSignWindow.force_continuous hk
  have posθ : 0≤θ:=intervalIntegral.integral_nonneg_of_forall ab (fun s=>abs_nonneg _)
  have posY : 0≤Y:=intervalIntegral.integral_nonneg_of_forall ab (fun s=>sq_nonneg _)
  have posJ : 0≤J:=intervalIntegral.integral_nonneg_of_forall ab (fun s=>abs_nonneg _)
  obtain ⟨w,hw,top⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr ab) ck.abs.continuousOn
  let M:=|k w|
  have mp : 0≤M:=abs_nonneg _
  have mx (x:ℝ) (hx:x∈Icc a b) : |k x|≤M:=top hx
  have moments (j:ℕ) : (∫s in a..b,|k s|^(j+1))≤M^j*θ := by
    rw [←intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ab ((ck.abs.pow _).intervalIntegrable _ _)
      ((ck.abs.const_mul _).intervalIntegrable _ _) (fun s hs=>by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (mx s hs) j) (abs_nonneg _))
  have ft (x y : ℝ) :
      2*(∫s in x..y, k s*v s) = k y^2-k x^2 := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s _
      apply ((((hk.differentiable (by simp)) s).hasDerivAt).pow 2).congr_deriv
      dsimp only [v]
      ring
    · exact ((ck.mul cv).const_mul 2).intervalIntegrable _ _
  have osc : M^3≤θ*Y := by
    have rise:=ft a w
    have fall:=ft w b
    rw [ka] at rise
    rw [kb] at fall
    have cabs:Continuous (fun s=>|k s*v s|):=(ck.mul cv).abs
    have lft:=intervalIntegral.abs_integral_le_integral_abs (μ:=volume) (f:=fun s=>k s*v s) hw.1
    have rgt:=intervalIntegral.abs_integral_le_integral_abs (μ:=volume) (f:=fun s=>k s*v s) hw.2
    have combine:=intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
      (cabs.intervalIntegrable a w) (cabs.intervalIntegrable w b)
    have bound : M^2≤∫s in a..b, |k s*v s| := by
      change |k w|^2≤_
      rw [sq_abs,←combine]
      linarith [((le_abs_self _).trans lft),((neg_le_abs _).trans rgt)]
    have cs:=LengthGrowth.interval_integral_mul_sq_le ck.abs cv.abs ab
    simp only [←abs_mul,sq_abs] at cs
    have mt:=moments 1
    simp only [Nat.reduceAdd,pow_one,sq_abs] at mt
    have mass : (∫s in a..b,|k s*v s|)^2 ≤ (M*θ)*Y :=
      cs.trans (mul_le_mul_of_nonneg_right mt posY)
    have sq:=pow_le_pow_left₀ (sq_nonneg M) bound 2
    rcases eq_or_lt_of_le mp with hz|hp
    · rw [←hz]
      simpa using mul_nonneg posθ posY
    · apply (mul_le_mul_iff_left₀ hp).mp
      nlinarith only [sq,mass]
  have hI (s:ℝ) : HasDerivAt (fun x=>k x*v x) (v s^2+k s*deriv v s) s := by
    apply (((hk.differentiable (by simp)) s).hasDerivAt.mul ((hv.differentiable (by simp)) s).hasDerivAt).congr_deriv
    change v s * v s + k s * deriv v s = _
    ring
  have ibp0 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=b) (fun s _=>hI s)
    (((cv.pow 2).add (ck.mul (contDiff_infty_iff_deriv.mp hv).2.continuous)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add,ka,kb] at ibp0
  case hf => exact (cv.pow 2).intervalIntegrable _ _
  case hg => exact (ck.mul (contDiff_infty_iff_deriv.mp hv).2.continuous).intervalIntegrable _ _
  have forceId : (∫s in a..b,k s*f s) = -Y+(1/2)*∫s in a..b, k s^4 := by
    have point (s:ℝ) : k s*f s=k s*deriv v s+(1/2)*k s^4 := by dsimp [f,v,FiniteSignWindow.force];ring
    simp_rw [point]
    rw [intervalIntegral.integral_add,intervalIntegral.integral_const_mul]
    · dsimp only [Y];linarith only [ibp0]
    · exact (ck.mul (contDiff_infty_iff_deriv.mp hv).2.continuous).intervalIntegrable _ _
    · exact ((ck.pow 4).const_mul _).intervalIntegrable _ _
  have signed : -(M*J)≤∫s in a..b,k s*f s := by
    rw [←neg_mul,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on ab ((cf.abs.const_mul _).intervalIntegrable _ _)
      ((ck.mul cf).intervalIntegrable _ _)
    intro s hs
    have pp:=mul_le_mul_of_nonneg_right (mx s hs) (abs_nonneg (f s))
    rw [←abs_mul] at pp
    change -M * |f s| ≤ k s*f s
    linarith only [neg_abs_le (k s*f s),pp]
  have fourth:=moments 3
  have abs4 (x : ℝ) : |x|^4=x^4 := by
    rw [show (4:ℕ)=2*2 by decide,pow_mul,pow_mul,sq_abs]
  simp only [Nat.reduceAdd,abs4] at fourth
  have θsq : θ^2≤1/16 := by nlinarith only [mul_self_le_mul_self posθ small]
  have ybound : 31*Y≤32*M*J := by
    rw [forceId] at signed
    nlinarith only [signed,fourth,mul_le_mul_of_nonneg_right osc posθ,
      mul_le_mul_of_nonneg_right θsq posY]
  have cub:=moments 2
  change (∫s in a..b,|k s|^3)≤(32/31:ℝ)*θ^2*J
  rcases eq_or_lt_of_le mp with hz|hp
  · rw [←hz] at cub
    nlinarith only [cub,mul_nonneg (sq_nonneg θ) posJ]
  · apply (mul_le_mul_iff_left₀ hp).mp
    nlinarith only [mul_le_mul_of_nonneg_left cub mp,mul_le_mul_of_nonneg_right osc posθ,
      mul_le_mul_of_nonneg_right ybound (sq_nonneg θ)]

/-- The same arc estimate with any prescribed angle threshold up to one quarter radian. -/
theorem small_turn_cubic_of_le {k : ℝ→ℝ} {a b δ : ℝ} (hk : ContDiff ℝ ∞ k)
    (ab : a≤b) (ka : k a=0) (kb : k b=0)
    (angle : (∫s in a..b, |k s|)≤δ) (small : δ≤1/4) :
    (∫s in a..b, |k s|^3) ≤ 3*δ^2*(∫s in a..b,|FiniteSignWindow.force k s|) := by
  have mass := intervalIntegral.integral_nonneg_of_forall (μ:=volume) ab
    (fun s => abs_nonneg (FiniteSignWindow.force k s))
  have turn := intervalIntegral.integral_nonneg_of_forall (μ:=volume) ab (fun s => abs_nonneg (k s))
  apply (small_turn_cubic hk ab ka kb (angle.trans small)).trans
  apply mul_le_mul_of_nonneg_right _ mass
  nlinarith only [pow_le_pow_left₀ turn angle 2,sq_nonneg δ]

end LengthGrowth.ActualFlow.MacroscopicTurning
#print axioms LengthGrowth.ActualFlow.MacroscopicTurning.small_turn_cubic
#print axioms LengthGrowth.ActualFlow.MacroscopicTurning.small_turn_cubic_of_le
