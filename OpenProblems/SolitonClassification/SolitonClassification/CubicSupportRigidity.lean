import SolitonClassification.SolitonDilation
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Identification of a normalized pure dilation profile from its cubic
support law at a simple inflection. The initial curvature slope is forced. -/
noncomputable section
namespace ClosedSimilarity.PeriodicSupportProfile
open Set Filter Polynomial
open scoped Topology
set_option backward.isDefEq.respectTransparency false

private theorem quartic_zero {a b c d e l u : ℝ} (hl : l<u)
    (h : ∀ x∈Ioo l u, a*x^4+b*x^3+c*x^2+d*x+e=0) :
    a=0 ∧ b=0 ∧ c=0 ∧ d=0 ∧ e=0 := by
  let p : Polynomial ℝ := C a*X^4+C b*X^3+C c*X^2+C d*X+C e
  have hp := p.eq_zero_of_infinite_isRoot ((Set.Ioo_infinite hl).mono (fun x hx => by
    change p.eval x=0
    simpa [p] using h x hx))
  have f (x : ℝ) : a*x^4+b*x^3+c*x^2+d*x+e=0 := by
    simpa [p] using congrArg (Polynomial.eval x) hp
  have h0 := f 0
  have h1 := f 1
  have hn := f (-1)
  have h2 := f 2
  have hm := f (-2)
  norm_num at h0 h1 hn h2 hm
  exact ⟨by linarith,by linarith,by linarith,by linarith,h0⟩

variable {L : ℝ} (z : PeriodicSupportProfile 1 0 L)

/-- A globally cubic support law at a simple inflection forces Bernoulli's
coefficient and the squared slope 6/5. The linear term is allowed at input. -/
theorem cubic_support_at_simple_inflection {a d j c s₀ : ℝ}
    (he : ∀ s, z.p s = a*z.k s^3+d*z.k s^2+j*z.k s+c)
    (hk : z.k s₀=0) (hv : z.v s₀≠0) :
    a= -5/18 ∧ d=0 ∧ j=0 ∧ c=0 ∧ (z.v s₀)^2=6/5 := by
  have dp (s : ℝ) : -z.k s*z.q s =
      a*(3*z.k s^2*z.v s)+d*(2*z.k s*z.v s)+j*z.v s := by
    have ph := (z.dp s)
    rw [show z.p=(fun x => a*z.k x^3+d*z.k x^2+j*z.k x+c) from funext he] at ph
    have h := ph.unique ((((((z.dk s).pow 3).const_mul a).add
      (((z.dk s).pow 2).const_mul d)).add ((z.dk s).const_mul j)).add_const c)
    convert! h using 1; ring
  have hj : j=0 := by
    have h := dp s₀
    simp [hk] at h
    exact h.resolve_right hv
  subst j
  have pe (s : ℝ) : z.p s=a*z.k s^3+d*z.k s^2+c := by simpa using he s
  have dv (s : ℝ) : HasDerivAt z.v (-(z.k s)^3/2-(a*z.k s^3+d*z.k s^2+c)) s := by
    simpa [pe] using z.dv s
  let A := (z.v s₀)^2
  let E := fun s => z.v s^2+(1/4+a/2)*z.k s^4+(2*d/3)*z.k s^3+2*c*z.k s
  have dE (s : ℝ) : HasDerivAt E 0 s := by
    have h₁ := ((dv s).pow 2).add (((z.dk s).pow 4).const_mul (1/4+a/2))
    have h₂ := h₁.add (((z.dk s).pow 3).const_mul (2*d/3))
    have h₃ := h₂.add ((z.dk s).const_mul (2*c))
    convert! h₃ using 1; ring
  have EE (s : ℝ) : E s=A := by
    have h := is_const_of_deriv_eq_zero (fun t => (dE t).differentiableAt)
      (fun t => (dE t).deriv) s s₀
    simpa only [E,hk,zero_pow (by decide : 4≠0),zero_pow (by decide : 3≠0),
      mul_zero,add_zero,A] using h
  have rq (s : ℝ) (hs : z.k s≠0) : z.q s= -(3*a*z.k s+2*d)*z.v s := by
    apply mul_left_cancel₀ hs
    linear_combination -(dp s)
  have poly (s : ℝ) (hs : z.k s≠0) :
      (-a*(5/4+9*a/2))*z.k s^4+(-7*a*d)*z.k s^3+(-2*d^2)*z.k s^2+
        ((1-9*a)*c)*z.k s+(3*a*A-2*d*c+1)=0 := by
    have eq : z.q =ᶠ[𝓝 s] (fun t => -(3*a*z.k t+2*d)*z.v t) := by
      filter_upwards [z.continuous_k.continuousAt.eventually_ne hs] with t ht using rq t ht
    have D := ((((z.dk s).const_mul (3*a)).add_const (2*d)).neg.mul (dv s))
    have hh := (z.dq s).unique (D.congr_of_eventuallyEq eq)
    rw [pe] at hh
    simp only [Pi.neg_apply] at hh
    have hc := EE s
    dsimp only [E] at hc
    linear_combination hh - 3*a*hc
  have hn : ¬∀ s, z.k s=0 := by
    intro h
    have g := z.dk s₀
    rw [show z.k=(fun _ => 0) from funext h] at g
    exact hv (g.unique (hasDerivAt_const _ _))
  obtain ⟨u,hu⟩ := not_forall.mp hn
  have onrange (x : ℝ) (hx : x ∈ uIoo 0 (z.k u)) : ∃ s, z.k s=x ∧ z.k s≠0 := by
    have hz : x≠0 := by
      rcases lt_or_gt_of_ne hu with hh|hh <;> simp [uIoo,hh.le] at hx <;> grind
    have hi := uIoo_subset_uIcc_self hx
    obtain ⟨s,hs⟩ : x∈Set.range z.k := by
      rcases le_total 0 (z.k u) with h|h
      · apply intermediate_value_univ s₀ u z.continuous_k
        simpa [hk,uIcc_of_le h] using hi
      · apply intermediate_value_univ u s₀ z.continuous_k
        simpa [hk,uIcc_of_ge h] using hi
    exact ⟨s,hs,hs ▸ hz⟩
  obtain ⟨h4,_,h2,h1,h0⟩ := quartic_zero (l:=min 0 (z.k u)) (u:=max 0 (z.k u))
    (lt_of_le_of_ne (min_le_max) (by grind)) (fun x hx => by
      obtain ⟨s,hs,hnz⟩ := onrange x hx
      exact hs ▸ poly s hnz)
  have hd : d=0 := by nlinarith [sq_nonneg d]
  subst d
  have ha : a= -5/18 := by
    rcases mul_eq_zero.mp h4 with h|h
    · simp_all
    · linarith
  refine ⟨ha,rfl,rfl,?_,?_⟩ <;> rw [ha] at h0 h1 <;> dsimp [A] at h0 <;> linarith

end ClosedSimilarity.PeriodicSupportProfile
