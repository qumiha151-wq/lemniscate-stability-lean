import SolitonClassification.EllipticDefect
import SolitonClassification.EllipticScalarEquation
import SolitonClassification.EllipticNormalization
import SolitonClassification.MeromorphicPoleExtension
import SolitonClassification.BernoulliPhysicalCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Filter Function
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

theorem periodic_elliptic_curvature {a b L : ℝ} (p : PeriodicSupportProfile a b L) (hL : 0<L)
    (e : EllipticExtension p.k) :
    (∃K : ℝ,K≠0 ∧ ∀t,p.k t=K) ∨ (∀t,deriv (deriv p.k) t+2/9*p.k t^3=0) := by
  have rem (z : ℂ) (hn : ¬AnalyticAt ℂ e.extension z) :
      ∃g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z=0 ∧ curvatureDefect e.extension =ᶠ[𝓝[≠] z] g := by
    have neg : meromorphicOrderAt e.extension z<0 :=
      lt_of_not_ge (fun h=>hn ((e.normal z).meromorphicOrderAt_nonneg_iff_analyticAt.mp h))
    lift meromorphicOrderAt e.extension z to ℤ using LT.lt.ne_top neg with n hn'
    obtain ⟨_,_,_,_,g,ag,gz,eq⟩ := pole_extension (p.dilation_pos hL) (e.normal z).meromorphicAt
      hn'.symm (WithTop.coe_lt_zero.mp neg) (residual_germ_of_extension p e z)
    exact ⟨g,ag,gz,eq⟩
  obtain ⟨v,vp,per⟩ := e.periodic_upper
  obtain all|zero := elliptic_defect_dichotomy (fun z=>(e.normal z).meromorphicAt)
    hL vp (e.periodic_real p.periodic_k) per rem
  · have constant (t : ℝ) : p.k t=p.k 0 := by
      apply Complex.ofReal_injective
      exact (e.restrict_real t).symm.trans ((all (t:ℂ)).trans (by
        simpa only [Complex.ofReal_zero] using e.restrict_real 0))
    refine Or.inl ⟨p.k 0,?_,constant⟩
    intro eq
    have kz (t : ℝ) := (constant t).trans eq
    have positive := p.bending_pos_of_period hL
    simp [PeriodicSupportProfile.bending,kz] at positive
  · right
    have d₁ := restriction_derivative e.analytic_real e.restrict_real
    have d₂ := restriction_derivative (fun t=>(e.analytic_real t).deriv) d₁
    intro t
    have eq := zero (t:ℂ) (e.analytic_real t)
    unfold curvatureDefect at eq
    rw [d₂,e.restrict_real] at eq
    have re : deriv (deriv p.k) t+2*(p.k t)^3/9=0 := by exact_mod_cast eq
    linarith

end ClosedSimilarity.MeromorphicCurvature
namespace ClosedSimilarity.ClosedUnitFrenetCurve
open MeromorphicCurvature

/-- Every closed immersed free-elastic similarity profile with elliptic signed
arclength curvature is a circle or a Bernoulli lemniscate, allowing covers.
Only meromorphic continuation, real-axis agreement, and a transverse period
are assumed of its curvature; the differential equation is derived from the
actual position and similarity generator. -/
theorem elliptic_curvature_circle_or_bernoulli (c : ClosedUnitFrenetCurve) (a b vx vy : ℝ)
    (law : ∀s,c.positionForce s= -a*c.normalSupport s-b*c.tangentSupport s+
      vx*c.ty s-vy*c.tx s) (f : ℂ → ℂ) (mer : Meromorphic f)
    (reg : ∀t : ℝ,AnalyticAt ℂ f (t:ℂ)) (realAxis : ∀t : ℝ,f (t:ℂ)=(c.k t:ℂ))
    (v : ℂ) (nv : v.im≠0) (per : ∀x : ℂ,(fun z=>f (z+v)) =ᶠ[𝓝[≠] x] f) :
    (∃(K : ℝ) (O Z : ℂ), K≠0 ∧ Z≠0 ∧ (∀s,c.k s=K) ∧
      ∀s:ℝ,(c.x s:ℂ)+(c.y s:ℂ)*I=O+Z*exp (((K*s:ℝ):ℂ)*I)) ∨
      (b=0 ∧ BernoulliGeometry.IsBernoulliCover c a vx vy) := by
  obtain ⟨e⟩ := exists_normal_extension mer reg realAxis nv per
  by_cases zero : a^2+b^2=0
  · have ha : a=0 := by nlinarith only [zero,sq_nonneg b,sq_nonneg a]
    have hb : b=0 := by nlinarith only [zero,sq_nonneg a,sq_nonneg b]
    exact False.elim (c.no_closed_translator_position_force vx vy (fun s=>by
      simpa [ha,hb] using law s))
  let x₀ := (-a*vx-b*vy)/(a^2+b^2)
  let y₀ := (b*vx-a*vy)/(a^2+b^2)
  let g := c.lowBendingRecenter x₀ y₀
  have shape (s : ℝ) : g.positionForce s= -a*g.normalSupport s-b*g.tangentSupport s := by
    rw [g.positionForce_eq]
    change c.force s=_
    rw [←c.positionForce_eq,law]
    dsimp only [g,lowBendingRecenter,normalSupport,tangentSupport,x₀,y₀]
    field_simp [zero]
    ring
  let p := g.centeredSupportProfile shape
  obtain flat|osc := periodic_elliptic_curvature p c.period_pos e
  · obtain ⟨K,kn,hk⟩ := flat
    obtain ⟨O,Z,zn,pos⟩ := c.low_bending_circle_parametrization K kn hk
    exact Or.inl ⟨K,O,Z,kn,zn,hk,pos⟩
  · exact Or.inr (c.bernoulli_of_cubic_oscillator a b vx vy law osc)

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.elliptic_curvature_circle_or_bernoulli

