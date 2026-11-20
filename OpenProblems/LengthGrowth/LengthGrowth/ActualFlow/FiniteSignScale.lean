import LengthGrowth.ActualFlow.FiniteSignPartition
import LengthGrowth.ActualFlow.FiniteSignWindow

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.FiniteSignWindow

def scaled (k : ℝ→ℝ) (a z y : ℝ) := k (z+y/a)/a

theorem scaled_smooth {k : ℝ→ℝ} (hk : ContDiff ℝ ∞ k) (a z : ℝ) :
    ContDiff ℝ ∞ (scaled k a z) :=
  (hk.comp (contDiff_const.add (contDiff_id.div_const a))).div_const a

theorem scaled_deriv {k : ℝ→ℝ} (hk : ContDiff ℝ ∞ k) {a : ℝ} (ha : 0<a) (z : ℝ) :
    deriv (scaled k a z)=fun y=>deriv k (z+y/a)/a^2 := by
  funext y
  have h := (((hk.differentiable (by simp) (z+y/a)).hasDerivAt.comp y
    (((hasDerivAt_id y).div_const a).const_add z)).div_const a).deriv
  change deriv (fun y=>k (z+y/a)/a) y=_
  change deriv (fun y=>k (z+y/a)/a) y=deriv k (z+y/a)*(1/a)/a at h
  rw [h]
  field_simp

theorem scaled_field {k : ℝ→ℝ} (hk : ContDiff ℝ ∞ k) {a : ℝ} (ha : 0<a) (z y : ℝ) :
    force (scaled k a z) y=force k (z+y/a)/a^3 := by
  have hk':=(contDiff_infty_iff_deriv.mp hk).2
  have h := (((hk'.differentiable (by simp) (z+y/a)).hasDerivAt.comp y
    (((hasDerivAt_id y).div_const a).const_add z)).div_const (a^2)).deriv
  change deriv (fun y=>deriv k (z+y/a)/a^2) y=deriv (deriv k) (z+y/a)*(1/a)/a^2 at h
  unfold force
  rw [scaled_deriv hk ha,h]
  unfold scaled
  field_simp

theorem scaled_energy {k : ℝ→ℝ} (hk : ContDiff ℝ ∞ k) {a : ℝ} (ha : 0<a) (z : ℝ) :
    energy (scaled k a z) 0=energy k z/a^4 := by
  unfold energy
  rw [scaled_deriv hk ha]
  simp only [scaled,zero_div,add_zero,div_pow]
  field_simp

theorem scale_pieces {k : ℝ→ℝ} {a z x y : ℝ} {n:ℕ} (ha : 0<a)
    (p : LengthGrowth.FiniteSign.Pieces k n x y) :
    LengthGrowth.FiniteSign.Pieces (scaled k a z) n ((x-z)*a) ((y-z)*a) := by
  induction p with
  | empty => exact .empty _
  | @append n b c d h hcd ss ih =>
    refine .append ih (mul_le_mul_of_nonneg_right (by linarith) ha.le) ?_
    have mem (t:ℝ) (ht:t∈Icc ((c-z)*a) ((d-z)*a)) : z+t/a∈Icc c d := by
      constructor
      · have h: c-z≤t/a := (le_div_iff₀ ha).mpr ht.1
        linarith
      · have h:t/a≤d-z := (div_le_iff₀ ha).mpr ht.2
        linarith
    rcases ss with hs|hs
    · exact Or.inl (fun t ht=>div_nonneg (hs _ (mem t ht)) ha.le)
    · exact Or.inr (fun t ht=>div_nonpos_of_nonpos_of_nonneg (hs _ (mem t ht)) ha.le)

theorem scaled_force_integral {k : ℝ→ℝ} (hk : ContDiff ℝ ∞ k) {a : ℝ} (ha : 0<a) (z P : ℝ) :
    (∫s in 0..P, |force (scaled k a z) s|) = (∫s in z..(z+P/a), |force k s|)/a^2 := by
  simp_rw [scaled_field hk ha,abs_div,abs_of_pos (pow_pos ha 3)]
  rw [intervalIntegral.integral_div]
  let f:=fun x=>|force k (z+x)|
  change (∫s in 0..P, f (s/a))/a^3=_
  have h:=intervalIntegral.integral_comp_mul_left f (inv_ne_zero ha.ne') (a:=0) (b:=P)
  simp only [mul_zero,inv_inv,smul_eq_mul] at h
  simp_rw [div_eq_inv_mul] at ⊢
  rw [h]
  have t:=intervalIntegral.integral_comp_add_left (fun s=>|force k s|) z (a:=0) (b:=a⁻¹*P)
  change (∫s in 0..a⁻¹*P, f s)=_ at t
  rw [t]
  simp only [add_zero]
  field_simp

end LengthGrowth.ActualFlow.FiniteSignWindow
#print axioms LengthGrowth.ActualFlow.FiniteSignWindow.scaled_force_integral
#print axioms LengthGrowth.ActualFlow.FiniteSignWindow.scale_pieces
