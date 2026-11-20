import LengthGrowth.ActualFlow.FiniteSignScale
import LengthGrowth.ActualFlow.FiniteSignGeneralWindow

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.FiniteSignWindow

theorem force_cost_at_unit_energy {k : ℝ→ℝ} (hk : ContDiff ℝ ∞ k) (N : ℕ)
    (hu : Real.sqrt (energy k 0)=1) {n:ℕ} (hn : n≤N+1)
    (part : LengthGrowth.FiniteSign.Pieces k n 0 (100*((N:ℝ)+1))) :
    1/4 < ∫s in 0..(100*((N:ℝ)+1)), |force k s| := by
  by_contra! hsmall
  have h0 : (0:ℝ)≤100*((N:ℝ)+1) := by positivity
  have hk1:=(contDiff_infty_iff_deriv.mp hk).2
  have hd (s:ℝ) : HasDerivAt (deriv k) (force k s-k s^3/2) s := by
    simpa [force] using (hk1.differentiable (by simp) s).hasDerivAt
  have hh:=FiniteSignGeneralWindow.forced_window_bounds hk h0 hu hsmall
  have up:=part.cubic_upper hk.continuous (force_continuous hk) hd (fun s hs=>(hh s hs).2)
  have down:=FiniteSignGeneralWindow.cubic_integral_gt hk N hu hsmall
  have hn':(n:ℝ)≤(N:ℝ)+1:=by exact_mod_cast hn
  linarith

theorem charge {k : ℝ→ℝ} (hk : ContDiff ℝ ∞ k) (N : ℕ) {a z : ℝ} (ha : 0<a)
    (hE : energy k z=a^4) {n:ℕ} (hn : n≤N+1)
    (part : LengthGrowth.FiniteSign.Pieces k n z (z+100*((N:ℝ)+1)/a)) :
    a^2/4 < ∫s in z..(z+100*((N:ℝ)+1)/a),|force k s| := by
  have hpart:=scale_pieces (z:=z) ha part
  have hu : Real.sqrt (energy (scaled k a z) 0)=1 := by
    rw [scaled_energy hk ha,hE,div_self (pow_ne_zero _ ha.ne'),Real.sqrt_one]
  let P:ℝ:=100*((N:ℝ)+1)
  change LengthGrowth.FiniteSign.Pieces _ n ((z-z)*a) ((z+P/a-z)*a) at hpart
  rw [sub_self,zero_mul,add_sub_cancel_left,div_mul_cancel₀ _ ha.ne'] at hpart
  have h:=force_cost_at_unit_energy (scaled_smooth hk a z) N hu hn hpart
  rw [scaled_force_integral hk ha] at h
  have hh:=(lt_div_iff₀ (pow_pos ha 2)).mp h
  linarith

end LengthGrowth.ActualFlow.FiniteSignWindow
#print axioms LengthGrowth.ActualFlow.FiniteSignWindow.charge
