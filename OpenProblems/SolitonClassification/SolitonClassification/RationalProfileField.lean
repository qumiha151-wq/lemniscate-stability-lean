import SolitonClassification.RationalPoleCoefficient
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section
open Polynomial Filter Set
open scoped Polynomial Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.RationalCurvature

/-- The denominator of this representation is nonzero wherever the original
supplied denominator B is nonzero. -/
def RationalOn (B : ℂ[X]) (f : ℂ→ℂ) : Prop :=
  ∃P Q : ℂ[X], ∀z,B.eval z≠0 → Q.eval z≠0 ∧ f z=P.eval z/Q.eval z

namespace RationalOn
variable {B:ℂ[X]} {f g:ℂ→ℂ}

theorem quotient_rep (A B:ℂ[X]) : RationalOn B (quotient A B) :=
  ⟨A,B,fun _ h=>⟨h,rfl⟩⟩

theorem const (c:ℂ) : RationalOn B (fun _=>c) :=
  ⟨C c,1,fun z _=>by simp⟩

theorem id_rep : RationalOn B (fun z=>z) :=
  ⟨X,1,fun z _=>by simp⟩

theorem add (a:RationalOn B f) (b:RationalOn B g) : RationalOn B (fun z=>f z+g z) := by
  obtain ⟨P,Q,h⟩ := a
  obtain ⟨R,S,j⟩ := b
  refine ⟨P*S+R*Q,Q*S,fun z hz=>?_⟩
  obtain ⟨n,e⟩:=h z hz
  obtain ⟨m,d⟩:=j z hz
  simp only [eval_add,eval_mul,e,d]
  exact ⟨mul_ne_zero n m,by field_simp⟩

theorem sub (a:RationalOn B f) (b:RationalOn B g) : RationalOn B (fun z=>f z-g z) := by
  obtain ⟨P,Q,h⟩ := a
  obtain ⟨R,S,j⟩ := b
  refine ⟨P*S-R*Q,Q*S,fun z hz=>?_⟩
  obtain ⟨n,e⟩:=h z hz
  obtain ⟨m,d⟩:=j z hz
  simp only [eval_sub,eval_mul,e,d]
  exact ⟨mul_ne_zero n m,by field_simp⟩

theorem mul (a:RationalOn B f) (b:RationalOn B g) : RationalOn B (fun z=>f z*g z) := by
  obtain ⟨P,Q,h⟩ := a
  obtain ⟨R,S,j⟩ := b
  refine ⟨P*R,Q*S,fun z hz=>?_⟩
  obtain ⟨n,e⟩:=h z hz
  obtain ⟨m,d⟩:=j z hz
  simp only [eval_mul,e,d]
  exact ⟨mul_ne_zero n m,by ring⟩

theorem pow (a:RationalOn B f) (n:ℕ) : RationalOn B (fun z=>f z^n) := by
  obtain ⟨P,Q,h⟩:=a
  refine ⟨P^n,Q^n,fun z hz=>?_⟩
  obtain ⟨v,e⟩:=h z hz
  simp only [eval_pow,e,div_pow]
  exact ⟨pow_ne_zero _ v,trivial⟩

private theorem local_deriv {P Q:ℂ[X]}
    (rep:∀z,B.eval z≠0 → Q.eval z≠0 ∧ f z=P.eval z/Q.eval z)
    {u:ℂ} (hu:B.eval u≠0) :
    HasDerivAt f ((P.derivative.eval u*Q.eval u-P.eval u*Q.derivative.eval u)/(Q.eval u)^2) u := by
  have eq : f=ᶠ[𝓝 u] (fun z=>P.eval z/Q.eval z) := by
    filter_upwards [(B.hasDerivAt u).continuousAt.eventually_ne hu] with z hz using (rep z hz).2
  exact (((P.hasDerivAt u).div (Q.hasDerivAt u) (rep u hu).1).congr_of_eventuallyEq eq)

theorem differentiable (a:RationalOn B f) {u:ℂ} (hu:B.eval u≠0) : DifferentiableAt ℂ f u := by
  obtain ⟨P,Q,h⟩:=a
  exact (local_deriv h hu).differentiableAt

theorem deriv (a:RationalOn B f) : RationalOn B (_root_.deriv f) := by
  obtain ⟨P,Q,h⟩:=a
  refine ⟨P.derivative*Q-P*Q.derivative,Q^2,fun z hz=>?_⟩
  simp only [eval_mul,eval_sub,eval_pow]
  exact ⟨pow_ne_zero _ (h z hz).1,(local_deriv h hz).deriv⟩

theorem euler_rep (a:RationalOn B f) (μ:ℂ) : RationalOn B (euler μ f) :=
  ((const μ).mul id_rep).mul a.deriv

theorem residual_rep (r:RationalOn B f) (μ a b:ℂ) : RationalOn B (residual μ a b f) := by
  have r₁ := r.euler_rep μ
  have r₂ := r₁.euler_rep μ
  have r₃ := r₂.euler_rep μ
  have r₄ := r₃.euler_rep μ
  exact (((((const 2).mul ((r.mul r₄).sub (r₁.mul r₃))).add
    (((const 3).mul ((r.pow 2).mul (r₁.pow 2))).add ((const 5).mul ((r.pow 3).mul r₂)))).add
    (r.pow 6)).sub (((const 2).mul (const a)).mul (r.pow 2))).sub (((const 2).mul (const b)).mul r₁)

end RationalOn
end ClosedSimilarity.RationalCurvature
#print axioms ClosedSimilarity.RationalCurvature.RationalOn.residual_rep
