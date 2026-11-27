import LengthGrowth.ActualFlow.DefectFourInvariant
import LengthGrowth.IntervalL2

noncomputable section
open MeasureTheory
namespace LengthGrowth.BendingSublevel

/-- The sharp fourth-moment bound, cut at a zero of the periodic function.
Both integrals and the optimal coefficient are proved from the fundamental
theorem of calculus and interval Cauchy–Schwarz. -/
theorem fourth_moment_of_zero_endpoints {a b : ℝ} (hab : a≤b)
    {u v : ℝ → ℝ} (du : ∀s, HasDerivAt u (v s) s) (cv : Continuous v)
    (ua : u a=0) (ub : u b=0) :
    3*(∫ s in a..b, u s^4)^2 ≤ (∫ s in a..b, u s^2)^3*(∫ s in a..b, v s^2) := by
  let V := ∫ s in a..b, u s^2
  let H := fun x => (∫ s in a..x, u s^2)-V/2
  have cu : Continuous u := continuous_iff_continuousAt.mpr (fun s => (du s).continuousAt)
  have cg := cu.pow 2
  have dh (s : ℝ) : HasDerivAt H (u s^2) s := by
    exact (intervalIntegral.integral_hasDerivAt_right (cg.intervalIntegrable a s)
      cg.stronglyMeasurable.stronglyMeasurableAtFilter cg.continuousAt).sub_const _
  have ch : Continuous H := continuous_iff_continuousAt.mpr (fun s => (dh s).continuousAt)
  have ha : H a = -V/2 := by simp [H, neg_div]
  have hb : H b = V/2 := by dsimp only [H]; change V - V/2 = V/2; ring
  have dprod (s : ℝ) : HasDerivAt (fun x => H x * (u x)^2)
      (u s^4+2*(H s*u s*v s)) s := by
    apply ((dh s).mul ((du s).pow 2)).congr_deriv
    dsimp
    ring
  have cflux := (ch.mul cu).mul cv
  have cterm := (cu.pow 4).add (cflux.const_mul 2)
  have ex := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=b)
    (fun s _ => dprod s) (cterm.intervalIntegrable a b)
  rw [ua,ub] at ex
  have endeq : (∫ s in a..b, u s^4) = -2*(∫ s in a..b, H s*u s*v s) := by
    rw [intervalIntegral.integral_add (f:=fun s => u s^4) (g:=fun s => 2*(H s*u s*v s))
      ((cu.pow 4).intervalIntegrable a b) ((cflux.const_mul 2).intervalIntegrable a b),
      intervalIntegral.integral_const_mul] at ex
    linarith
  have dcube (s : ℝ) : HasDerivAt (fun x => (H x)^3/3) ((H s*u s)^2) s := by
    apply (((dh s).pow 3).div_const 3).congr_deriv
    dsimp
    ring
  have ex3 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=b)
    (fun s _ => dcube s) (((ch.mul cu).pow 2).intervalIntegrable a b)
  rw [ha,hb] at ex3
  have cs := interval_integral_mul_sq_le (ch.mul cu) cv hab
  change (∫ s in a..b, H s*u s*v s)^2 ≤
    (∫ s in a..b, (H s*u s)^2)*(∫ s in a..b,v s^2) at cs
  rw [ex3] at cs
  change 3*(∫ s in a..b,u s^4)^2 ≤ V^3*(∫ s in a..b,v s^2)
  rw [endeq]
  linarith only [cs]

/-- A continuous periodic mean-zero function supplies its own cut via Rolle. -/
theorem periodic_fourth_moment {P : ℝ} (hP : 0<P) {u v : ℝ → ℝ}
    (du : ∀s, HasDerivAt u (v s) s) (cv : Continuous v)
    (pu : Function.Periodic u P) (pv : Function.Periodic v P)
    (avg : (∫ s in 0..P, u s)=0) :
    3*(∫ s in 0..P,u s^4)^2 ≤ (∫ s in 0..P,u s^2)^3*(∫ s in 0..P,v s^2) := by
  let G := fun x => ∫ s in 0..x,u s
  have cu := continuous_iff_continuousAt.mpr (fun s => (du s).continuousAt)
  have dg (s : ℝ) : HasDerivAt G (u s) s :=
    intervalIntegral.integral_hasDerivAt_right (cu.intervalIntegrable 0 s)
      cu.stronglyMeasurable.stronglyMeasurableAtFilter cu.continuousAt
  have cG := continuous_iff_continuousAt.mpr (fun s => (dg s).continuousAt)
  have ends : G 0=G P := by simp [G,avg]
  obtain ⟨z,_,hz⟩ := exists_hasDerivAt_eq_zero hP cG.continuousOn ends (fun s _ => dg s)
  have bound := fourth_moment_of_zero_endpoints (show z≤z+P by linarith)
    du cv hz ((pu z).trans hz)
  have shift (f : ℝ → ℝ) (pf : Function.Periodic f P) (n : ℕ) :
      (∫ s in z..z+P, f s^n) = ∫ s in 0..P,f s^n := by
    have pn : Function.Periodic (fun s => f s^n) P := fun s => congrArg (fun x => x^n) (pf s)
    simpa only [zero_add] using pn.intervalIntegral_add_eq z 0
  rwa [shift u pu 4,shift u pu 2,shift v pv 2] at bound

/-- Applied to the actual arclength curvature of a closed immersion. -/
theorem curvature_fourth_moment (c : ClosedFrenetCurve) (μ : ℝ)
    (avg : (∫ s in 0..c.period,c.curvature s-μ)=0) :
    3*(∫ s in 0..c.period,(c.curvature s-μ)^4)^2 ≤
      (∫ s in 0..c.period,(c.curvature s-μ)^2)^3*(∫ s in 0..c.period,c.curvature₁ s^2) :=
  periodic_fourth_moment c.period_pos (fun s => (c.curvature_deriv s).sub_const μ)
    c.curvature₁_continuous (fun s => congrArg (fun x => x-μ) (c.curvature_periodic s))
    c.curvature₁_periodic avg

end LengthGrowth.BendingSublevel
#print axioms LengthGrowth.BendingSublevel.fourth_moment_of_zero_endpoints
