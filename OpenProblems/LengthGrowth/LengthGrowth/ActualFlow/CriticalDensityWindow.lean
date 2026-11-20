import LengthGrowth.ActualFlow.CriticalDensityPieces
import LengthGrowth.ActualFlow.FiniteSignCharge

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.CriticalDensity

private theorem cubic_quarter {x : ℝ} (hx : -(1/4:ℝ) ≤ x) :
    |x|^3 ≤ x^3+1/32 := by
  by_cases h : 0≤x
  · rw [abs_of_nonneg h]; linarith
  rw [abs_of_neg (lt_of_not_ge h)]
  have hn : -x≤1/4 := by linarith
  have p := pow_le_pow_left₀ (neg_nonneg.mpr (le_of_not_ge h)) hn 3
  nlinarith only [p]

theorem Pieces.cubic_quarter_upper {k v F : ℝ→ℝ} {n : ℕ} {a b H : ℝ}
    (p : Pieces k (1/4) n a b) (hk : Continuous k) (hF : Continuous F)
    (hd : ∀s, HasDerivAt v (F s-k s^3/2) s)
    (hv : ∀s∈Icc a b, |v s|≤H) :
    (∫s in a..b, |k s|^3) ≤ 2*(∫s in a..b, |F s|)+4*n*H+(b-a)/32 := by
  induction p with
  | empty => simp
  | @append n a b d prev hbd signs ih =>
    have hab:=prev.ordered
    have old:=ih (fun s hs => hv s ⟨hs.1,hs.2.trans hbd⟩)
    have vb:=abs_le.mp (hv b ⟨hab,hbd⟩)
    have vd:=abs_le.mp (hv d ⟨hab.trans hbd,le_rfl⟩)
    have iF:=hF.intervalIntegrable (μ:=volume) b d
    have ck : Continuous (fun s=>k s^3/2) := (hk.pow 3).div_const (2:ℝ)
    have eq:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=b) (b:=d)
      (fun s _ => hd s) ((hF.sub ck).intervalIntegrable _ _)
    rw [intervalIntegral.integral_sub iF (ck.intervalIntegrable _ _),intervalIntegral.integral_div] at eq
    obtain ⟨σ,hσ,hs⟩ : ∃σ : ℝ, (σ=1 ∨ σ= -1) ∧ ∀s∈Icc b d, |k s|^3≤σ*k s^3+1/32 := by
      rcases signs with hp|hn
      · exact ⟨1,Or.inl rfl,fun s h => by simpa using cubic_quarter (hp s h)⟩
      · refine ⟨-1,Or.inr rfl,fun s h => ?_⟩
        have hl : -(1/4:ℝ)≤ -k s := by linarith [hn s h]
        have e:=cubic_quarter hl
        rw [abs_neg] at e
        linarith only [e]
    have hi:=intervalIntegral.integral_mono_on (μ:=volume) hbd ((hk.abs.pow 3).intervalIntegrable _ _)
      ((((hk.pow 3).const_mul σ).add continuous_const).intervalIntegrable _ _) hs
    change (∫s in b..d, |k s|^3) ≤ ∫s in b..d, σ*k s^3+(1/32:ℝ) at hi
    rw [intervalIntegral.integral_add (f:=fun s=>σ*k s^3) (g:=fun _ => 1/32) (((hk.pow 3).const_mul σ).intervalIntegrable _ _)
      intervalIntegrable_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_const,smul_eq_mul] at hi
    have hh1 := intervalIntegral.integral_mono_on (μ:=volume) hbd iF (hF.abs.intervalIntegrable _ _)
      (fun s _=>le_abs_self (F s))
    have hh2 := intervalIntegral.integral_mono_on (μ:=volume) hbd (hF.neg.intervalIntegrable _ _)
      (hF.abs.intervalIntegrable _ _) (fun s _=>neg_le_abs (F s))
    change (∫s in b..d,-F s)≤_ at hh2
    rw [intervalIntegral.integral_neg] at hh2
    have bound : (∫s in b..d,|k s|^3) ≤ 2*(∫s in b..d,|F s|)+4*H+(d-b)/32 := by
      rcases hσ with rfl|rfl <;> linarith
    rw [←intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (f:=fun s=>|k s|^3)
       ((hk.abs.pow 3).intervalIntegrable a b) ((hk.abs.pow 3).intervalIntegrable b d),
       ←intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (f:=fun s=>|F s|)
       (hF.abs.intervalIntegrable a b) (hF.abs.intervalIntegrable b d)]
    push_cast
    linarith

private theorem scale_quarter {k : ℝ→ℝ} {a z x y : ℝ} {n:ℕ} (ha : 2≤a)
    (p : Pieces k (1/2) n x y) :
    Pieces (FiniteSignWindow.scaled k a z) (1/4) n ((x-z)*a) ((y-z)*a) := by
  have ha0 : 0<a := by linarith
  induction p with
  | empty => exact .empty _
  | @append n b c d h hcd ss ih =>
    refine .append ih (mul_le_mul_of_nonneg_right (by linarith) ha0.le) ?_
    have mem (t:ℝ) (ht:t∈Icc ((c-z)*a) ((d-z)*a)) : z+t/a∈Icc c d := by
      constructor
      · linarith [(le_div_iff₀ ha0).mpr ht.1]
      · linarith [(div_le_iff₀ ha0).mpr ht.2]
    rcases ss with hs|hs
    · exact Or.inl (fun t ht => (le_div_iff₀ ha0).mpr (by linarith [hs _ (mem t ht)]))
    · exact Or.inr (fun t ht => (div_le_iff₀ ha0).mpr (by linarith [hs _ (mem t ht)]))

/-- Force spent by a high-stress window with at most N+1 strong-excursion pieces. -/
theorem charge {k : ℝ→ℝ} (hk : ContDiff ℝ ∞ k) (N : ℕ) {a z : ℝ} (ha : 2≤a)
    (hE : FiniteSignWindow.energy k z=a^4) {n:ℕ} (hn : n≤N+1)
    (part : Pieces k (1/2) n z (z+200*((N:ℝ)+1)/a)) :
    a^2/4 < ∫s in z..(z+200*((N:ℝ)+1)/a),|FiniteSignWindow.force k s| := by
  let K:=FiniteSignWindow.scaled k a z
  let P:=200*((N:ℝ)+1)
  have ha0 : 0<a := by linarith
  have hP : 0≤P := by dsimp [P]; positivity
  have hpk:=scale_quarter (z:=z) ha part
  change Pieces K (1/4) n ((z-z)*a) ((z+P/a-z)*a) at hpk
  rw [sub_self,zero_mul,add_sub_cancel_left,div_mul_cancel₀ _ ha0.ne'] at hpk
  have ku:=FiniteSignWindow.scaled_smooth hk a z
  have hu : Real.sqrt (FiniteSignWindow.energy K 0)=1 := by
    rw [FiniteSignWindow.scaled_energy hk ha0,hE,div_self (pow_ne_zero _ ha0.ne'),Real.sqrt_one]
  have hcost : 1/4 < ∫s in 0..P, |FiniteSignWindow.force K s| := by
    by_contra! hs
    have hh:=FiniteSignGeneralWindow.forced_window_bounds ku hP hu hs
    have ku1:=(contDiff_infty_iff_deriv.mp ku).2
    have hd (s:ℝ) : HasDerivAt (deriv K) (FiniteSignWindow.force K s-K s^3/2) s := by
      simpa [FiniteSignWindow.force] using (ku1.differentiable (by simp) s).hasDerivAt
    have upper:=hpk.cubic_quarter_upper ku.continuous (FiniteSignWindow.force_continuous ku) hd
      (fun s hx => (hh s hx).2)
    have ep : 100*(((2*N+1:ℕ):ℝ)+1)=P := by dsimp [P]; push_cast; ring
    have lower:=FiniteSignGeneralWindow.cubic_integral_gt ku (2*N+1) hu (by rwa [ep])
    rw [ep] at lower
    push_cast at lower
    have hn' : (n:ℝ)≤(N:ℝ)+1 := by exact_mod_cast hn
    dsimp [P] at upper
    dsimp [P] at lower hs
    linarith [Nat.cast_nonneg (α:=ℝ) N]
  rw [FiniteSignWindow.scaled_force_integral hk ha0] at hcost
  have h:=(lt_div_iff₀ (pow_pos ha0 2)).mp hcost
  linarith

end LengthGrowth.ActualFlow.CriticalDensity
#print axioms LengthGrowth.ActualFlow.CriticalDensity.charge
