import SolitonClassification.NoClosedTranslators

/-! The local arclength force in an angle chart, and the polynomial
eliminations for algebraic force data and algebraic evolutes. -/
noncomputable section
namespace ClosedSimilarity
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Only a neighbourhood of the chart point must satisfy the angular
speed relation. In particular the curve may have inflections elsewhere. -/
theorem angular_radius_force_identity {θ u du ddu : ℝ → ℝ} {s : ℝ}
    (hu : ∀ x, HasDerivAt u (du x) x) (hd : ∀ x, HasDerivAt du (ddu x) x)
    (ht : ∀ᶠ t in 𝓝 s, HasDerivAt θ (1/u (θ t)) t) (hn : u (θ s)≠0) :
    (deriv (deriv (fun t => 1/u (θ t))) s+(1/u (θ s))^3/2)*u (θ s)^5 =
      -(u (θ s))*ddu (θ s)+3*du (θ s)^2+u (θ s)^2/2 := by
  have hs := ht.self_of_nhds
  have nonzero := ((hu (θ s)).continuousAt.comp hs.continuousAt).eventually_ne hn
  have dk : deriv (fun t => 1/u (θ t)) =ᶠ[𝓝 s]
      (fun t => -(du (θ t))/u (θ t)^3) := by
    filter_upwards [ht,nonzero] with t hθ hne
    have d := (hasDerivAt_const t (1:ℝ)).div ((hu (θ t)).comp t hθ) hne
    change u (θ t)≠0 at hne
    rw [show deriv (fun v => 1/u (θ v)) t = _ from d.deriv]
    simp only [Function.comp_apply]
    field_simp
    ring
  have dv := (((hd (θ s)).comp s hs).neg).div (((hu (θ s)).comp s hs).pow 3) (pow_ne_zero 3 hn)
  rw [dk.deriv_eq,show deriv (fun t => -(du (θ t))/u (θ t)^3) s = _ from dv.deriv]
  simp only [Pi.pow_apply,Pi.neg_apply,Function.comp_apply]
  field_simp
  ring

theorem angular_force_quintic {u du ddu F c g dg : ℝ}
    (elastic : F*u^5= -u*ddu+3*du^2+u^2/2)
    (slope : du=c*u+g) (accel : ddu=c*du+dg) :
    F*u^5=(2*c^2+1/2)*u^2+(5*c*g-dg)*u+3*g^2 := by
  rw [elastic,accel,slope]
  ring

theorem angular_evolute_sextic {u du ddu F a B : ℝ}
    (elastic : F*u^5= -u*ddu+3*du^2+u^2/2) (force : F=a*u+B) :
    a*u^6+B*u^5-u^2/2+ddu*u-3*du^2=0 := by
  rw [force] at elastic
  linear_combination elastic

end ClosedSimilarity

#print axioms ClosedSimilarity.angular_radius_force_identity
#print axioms ClosedSimilarity.angular_force_quintic
#print axioms ClosedSimilarity.angular_evolute_sextic
