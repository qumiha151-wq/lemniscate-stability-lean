import SolitonClassification.RationalProfileCircle
import SolitonClassification.ScalarReconstructionNecessity

noncomputable section
open Polynomial Complex Set
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.RationalCurvature
open ScalarReconstruction

private theorem expanded_equation {a b:ℝ} {k k₁ k₂ k₃ k₄:ℝ→ℝ} (law:ScalarEquation k a b)
    (d₀:∀s,HasDerivAt k (k₁ s) s) (d₁:∀s,HasDerivAt k₁ (k₂ s) s)
    (d₂:∀s,HasDerivAt k₂ (k₃ s) s) (d₃:∀s,HasDerivAt k₃ (k₄ s) s) (s:ℝ) :
    2*(k s*k₄ s-k₁ s*k₃ s)+(3*(k s^2*(k₁ s)^2)+5*(k s^3*k₂ s))+
      k s^6-2*a*k s^2-2*b*k₁ s=0 := by
  have eq₁ : deriv k=k₁ := funext (fun t=>(d₀ t).deriv)
  have eq₂ : deriv k₁=k₂ := funext (fun t=>(d₁ t).deriv)
  let g := fun t=>k₃ t+3*(k t)^2*k₁ t/2
  have df (t:ℝ) : HasDerivAt (force k) (g t) t := by
    unfold force;rw [eq₁,eq₂]
    apply ((d₂ t).add (((d₀ t).pow 3).div_const 2)).congr_deriv
    simp only [Nat.cast_ofNat,Nat.reduceSub,g]
  have ef : deriv (force k)=g := funext (fun t=>(df t).deriv)
  have dg : HasDerivAt g (k₄ s+(6*k s*(k₁ s)^2+3*(k s)^2*k₂ s)/2) s := by
    apply ((d₃ s).add (((((d₀ s).pow 2).const_mul 3).mul (d₁ s)).div_const 2)).congr_deriv
    simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,Pi.pow_apply];ring
  have eq := law s
  dsimp only [numerator,supportDerivative] at eq
  rw [ef,dg.deriv,eq₁] at eq
  unfold force at eq
  rw [eq₁,eq₂] at eq
  dsimp only [g] at eq
  linarith only [eq]

/-- The degenerate fourth-order curvature equation of the real closed support
profile extends to the entire complex domain off the displayed denominator. -/
theorem residual_of_periodicSupportProfile {a b L w:ℝ} (z:PeriodicSupportProfile a b L) (hw:w≠0)
    (A B:ℂ[X]) (polefree:∀s,B.eval (wave w s)≠0)
    (rep:∀s,quotient A B (wave w s)=(z.k s:ℂ)) :
    ∀u,B.eval u≠0 → residual ((w:ℂ)*Complex.I) a b (quotient A B) u=0 := by
  let f := quotient A B
  let μ := (w:ℂ)*Complex.I
  have r : RationalOn B f := RationalOn.quotient_rep A B
  let k₁ := deriv z.k
  let k₂ := deriv k₁
  let k₃ := deriv k₂
  let k₄ := deriv k₃
  obtain ⟨d₀,m₁⟩ := along_euler r polefree (show Matches w f z.k from rep)
  obtain ⟨d₁,m₂⟩ := along_euler (r.euler_rep μ) polefree m₁
  obtain ⟨d₂,m₃⟩ := along_euler ((r.euler_rep μ).euler_rep μ) polefree m₂
  obtain ⟨d₃,m₄⟩ := along_euler (((r.euler_rep μ).euler_rep μ).euler_rep μ) polefree m₃
  change Matches w (euler μ f) k₁ at m₁
  change Matches w (D₂ μ f) k₂ at m₂
  change Matches w (D₃ μ f) k₃ at m₃
  change Matches w (D₄ μ f) k₄ at m₄
  apply rational_identity_on_circle hw (r.residual_rep μ a b) polefree
  intro s
  dsimp only [residual,quadratic,quartic]
  rw [m₄ s,m₃ s,m₂ s,m₁ s,show f (wave w s)=(z.k s:ℂ) from rep s]
  exact_mod_cast expanded_equation (scalarEquation_of_periodicSupportProfile z) d₀ d₁ d₂ d₃ s

end ClosedSimilarity.RationalCurvature
#print axioms ClosedSimilarity.RationalCurvature.residual_of_periodicSupportProfile
