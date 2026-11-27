import SolitonClassification.EllipticContinuation
import SolitonClassification.MeromorphicOrdinaryPole
import SolitonClassification.ScalarReconstructionNecessity

noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature

private def elasticForce (k : ℂ → ℂ) (z : ℂ) := deriv (deriv k) z + (k z)^3/2

private theorem analytic_force {k : ℂ → ℂ} {z : ℂ} (an : AnalyticAt ℂ k z) :
    AnalyticAt ℂ (elasticForce k) z :=
  an.deriv.deriv.add ((an.pow 3).div analyticAt_const (by norm_num))

private theorem force_prime {k : ℂ → ℂ} {z : ℂ} (an : AnalyticAt ℂ k z) :
    deriv (elasticForce k) z=deriv (deriv (deriv k)) z+3*k z^2*deriv k z/2 := by
  exact ((an.deriv.deriv.differentiableAt.hasDerivAt.add
    ((an.differentiableAt.hasDerivAt.pow 3).div_const 2)).congr_deriv (by push_cast;ring)).deriv

private theorem force_second {k : ℂ → ℂ} {z : ℂ} (an : AnalyticAt ℂ k z) :
    deriv (deriv (elasticForce k)) z=deriv (deriv (deriv (deriv k))) z+
      (6*k z*(deriv k z)^2+3*k z^2*deriv (deriv k) z)/2 := by
  have germ : deriv (elasticForce k) =ᶠ[𝓝 z]
      (fun w=>deriv (deriv (deriv k)) w+3*k w^2*deriv k w/2) :=
    an.eventually_analyticAt.mono (fun _ h=>force_prime h)
  rw [germ.deriv_eq]
  apply HasDerivAt.deriv
  apply (an.deriv.deriv.deriv.differentiableAt.hasDerivAt.add
    ((((an.differentiableAt.hasDerivAt.pow 2).const_mul 3).mul
      an.deriv.differentiableAt.hasDerivAt).div_const 2)).congr_deriv
  push_cast
  simp only [Pi.pow_apply]
  ring

/-- The real trace of a closed similarity profile already determines the scalar
differential equation wherever the trace is analytic along the real axis. -/
theorem residual_on_real_trace {a b L : ℝ} (p : PeriodicSupportProfile a b L)
    {k : ℂ → ℂ} (ha : ∀t : ℝ,AnalyticAt ℂ k (t:ℂ))
    (rep : ∀t : ℝ,k (t:ℂ)=(p.k t:ℂ)) (s : ℝ) : ordinaryResidual a b k (s:ℂ)=0 := by
  have h₁ := restriction_derivative ha rep
  have h₂ := restriction_derivative (fun t=>(ha t).deriv) h₁
  have hf (t : ℝ) : elasticForce k (t:ℂ)=(ScalarReconstruction.force p.k t:ℂ) := by
    unfold elasticForce ScalarReconstruction.force
    rw [h₂,show k (t:ℂ)=(p.k t:ℂ) from rep t]
    push_cast
    rfl
  have aF (t : ℝ) := analytic_force (ha t)
  have hf₁ := restriction_derivative aF hf
  have hf₂ := restriction_derivative (fun t=>(aF t).deriv) hf₁
  have eq := ScalarReconstruction.scalarEquation_of_periodicSupportProfile p s
  dsimp only [ScalarReconstruction.numerator,ScalarReconstruction.supportDerivative] at eq
  have ce : k (s:ℂ)*deriv (deriv (elasticForce k)) (s:ℂ)-
    deriv k (s:ℂ)*(deriv (elasticForce k) (s:ℂ)+(b:ℂ)) =
    (k (s:ℂ))^2*((a:ℂ)-k (s:ℂ)*elasticForce k (s:ℂ)) := by
    rw [hf₂,hf₁,hf,h₁,show k (s:ℂ)=(p.k s:ℂ) from rep s]
    exact_mod_cast eq
  rw [force_second (ha s),force_prime (ha s)] at ce
  unfold elasticForce at ce
  change ordinaryResidual _ _ k (s:ℂ)=0
  unfold ordinaryResidual ordinaryQuadratic ordinaryQuartic
  linear_combination 2*ce

theorem meromorphicAt_ordinaryResidual {k : ℂ→ℂ} {z : ℂ} (m : MeromorphicAt k z) (a b : ℂ) :
    MeromorphicAt (ordinaryResidual a b k) z := by
  unfold ordinaryResidual ordinaryQuadratic ordinaryQuartic
  fun_prop (disch := assumption)

/-- A meromorphic continuation of the physical scalar equation satisfies the
ordinary complex residual in every punctured neighborhood of the plane. -/
theorem residual_germ_of_meromorphic_trace {a b L : ℝ} (p : PeriodicSupportProfile a b L)
    {k : ℂ → ℂ} (m : Meromorphic k) (ha : ∀t : ℝ,AnalyticAt ℂ k (t:ℂ))
    (rep : ∀t : ℝ,k (t:ℂ)=(p.k t:ℂ)) (z : ℂ) :
    ordinaryResidual a b k =ᶠ[𝓝[≠] z] fun _=>0 := by
  exact real_axis_meromorphic_identity (fun x=>meromorphicAt_ordinaryResidual (m x) a b)
    (residual_on_real_trace p ha rep) z

end ClosedSimilarity.MeromorphicCurvature

