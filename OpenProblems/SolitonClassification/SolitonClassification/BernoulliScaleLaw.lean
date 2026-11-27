import SolitonClassification.BernoulliOscillator
import Mathlib.Analysis.Calculus.Deriv.Inverse

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.BernoulliGeometry
set_option backward.isDefEq.respectTransparency false

/-- Both support coordinates vanish at an upward inflection. The quartic
oscillator also fixes the similarity dilation and rules out rotation. -/
theorem marker_similarity_data {a b L s₀ : ℝ} (z : PeriodicSupportProfile a b L)
    (hL : 0<L) (dv : ∀s,HasDerivAt z.v (-2/9*z.k s^3) s)
    (hz : z.k s₀=0) (hv : 0<z.v s₀) :
    b=0 ∧ z.p s₀=0 ∧ z.q s₀=0 ∧ a=5/6*z.v s₀^2 := by
  have ha := z.dilation_pos hL
  have force (s : ℝ) : -a*z.p s-b*z.q s=5/18*z.k s^3 := by
    have h := (z.dv s).unique (dv s)
    linear_combination h
  have fs (s : ℝ) : a*z.k s*z.q s-b*(1+z.k s*z.p s)=5/6*z.k s^2*z.v s := by
    have h := (((z.dp s).const_mul (-a)).sub ((z.dq s).const_mul b))
    have eq : (fun t=> -a*z.p t-b*z.q t)=(fun t=>5/18*z.k t^3) := funext force
    change HasDerivAt (fun t=> -a*z.p t-b*z.q t) _ s at h
    rw [eq] at h
    have e := h.unique (((z.dk s).pow 3).const_mul (5/18))
    linear_combination e
  have bz : b=0 := by simpa [hz] using fs s₀
  have pz : z.p s₀=0 := by simpa [bz,hz,ha.ne'] using force s₀
  have relation (s : ℝ) : a*z.k s*z.q s=5/6*z.k s^2*z.v s := by simpa [bz] using fs s
  have sign {s : ℝ} (h : z.k s=0) : z.v s≠0 := by
    intro zero
    have eq := oscillator_unique z.dk dv (p:=fun _=>0) (q:=fun _=>0)
      (fun r=>hasDerivAt_const r 0) (fun r=>by simpa using hasDerivAt_const r (0:ℝ)) h zero
    exact hv.ne' (eq s₀).2
  have weighted (s : ℝ) : a*z.q s=5/6*z.k s*z.v s := by
    by_cases ks : z.k s=0
    · have h := (((z.dk s).const_mul a).mul (z.dq s))
      change HasDerivAt (fun t=>a*z.k t*z.q t) _ s at h
      rw [show (fun t=>a*z.k t*z.q t)=(fun t=>5/6*z.k t^2*z.v t) from funext relation] at h
      have e := h.unique ((((z.dk s).pow 2).const_mul (5/6)).mul (dv s))
      simp only [ks,mul_zero,zero_mul,add_zero] at e ⊢
      have nz := sign ks
      rcases mul_eq_zero.mp (show (a*z.q s)*z.v s=0 by linear_combination e) with aq|v
      · exact aq
      · exact (nz v).elim
    · apply mul_left_cancel₀ ks
      linear_combination relation s
  have qz : z.q s₀=0 := by simpa [hz,ha.ne'] using weighted s₀
  have h := (z.dq s₀).const_mul a
  rw [show (fun t=>a*z.q t)=(fun t=>5/6*z.k t*z.v t) from funext weighted] at h
  have e := h.unique (((z.dk s₀).const_mul (5/6)).mul (dv s₀))
  simp only [hz,zero_mul,mul_zero,add_zero,mul_one] at e
  exact ⟨bz,pz,qz,by linear_combination e⟩

end ClosedSimilarity.BernoulliGeometry
