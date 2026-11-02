import Lemniscate.PeriodicPrincipalBlochSymmetry
import Lemniscate.PeriodicAnalyticEigenpair

/-! Reflection determines the analytic eigenvalue branch
by local uniqueness of the normalized eigenpair. -/
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped ComplexConjugate Topology

private theorem eigenvalue_even_of_reflection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (C : ℂ → E →L[ℂ] E) (R S : E →L[ℂ] E) (Φ : E →L[ℂ] ℂ)
    (x : E) (μ : ℂ → ℂ) (f : ℂ → E)
    (hμ : Tendsto μ (𝓝 0) (𝓝 (0:ℂ))) (hf : Tendsto f (𝓝 0) (𝓝 x))
    (hSx : S x = x) (hCS : ∀ z u, C z (S u) = S (C (-z) u))
    (hRS : ∀ u, R (S u) = S (R u)) (hΦS : ∀ u, Φ (S u) = Φ u)
    (hsol : ∀ᶠ z in 𝓝 (0:ℂ), C z (f z) = μ z • R (f z) ∧ Φ (f z) = 1)
    (U : Set (ℂ × (ℂ × E))) (hU : IsOpen U) (hU0 : (0,(0,x)) ∈ U)
    (huniq : ∀ z a u, (z,(a,u)) ∈ U → C z u = a • R u → Φ u = 1 →
      a = μ z ∧ u = f z) : ∀ᶠ z in 𝓝 (0:ℂ), μ (-z) = μ z := by
  have hn : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 (0:ℂ)) := by
    simpa only [neg_zero] using continuous_neg.tendsto (0:ℂ)
  have hc : Tendsto (fun z : ℂ => (z,(μ (-z),S (f (-z)))))
      (𝓝 0) (𝓝 (0,(0,x))) := by
    convert! tendsto_id.prodMk ((hμ.comp hn).prodMk
      ((S.continuous.tendsto x).comp (hf.comp hn))) using 1 <;>
      simp only [nhds_prod_eq,hSx]
  filter_upwards [hc (hU.mem_nhds hU0),hn hsol] with z hz hsz
  have heq : C z (S (f (-z))) = μ (-z) • R (S (f (-z))) := by
    rw [hCS,hsz.1,map_smul,← hRS]
  exact (huniq z (μ (-z)) (S (f (-z))) hz heq (by rw [hΦS]; exact hsz.2)).1

variable (T : ℝ) [Fact (0 < T)]

section Branch
variable (h h₁ h₂ : C(AddCircle T, ℂ)) (p : ℝ) (hp : 1 ≤ p)
    (ψ x : CircleL2 T) (μ : ℂ → ℂ) (f : ℂ → CircleL2 T)
    (hμ : AnalyticAt ℂ μ 0) (hf : AnalyticAt ℂ f 0) (hμ0 : μ 0 = 0) (hf0 : f 0 = x)
    (hsol : ∀ᶠ z in 𝓝 (0:ℂ),
      circlePrincipalBlochFamily T h h₁ h₂ p hp z (f z) =
        μ z • circlePrincipalResolvent T (p^4) (by positivity) (f z) ∧
      inner ℂ ψ (circlePrincipalResolvent T (p^4) (by positivity) (f z)) = 1 ∧
      circlePrincipalResolvent T (p^4) (by positivity) (f z) ≠ 0)
    (U : Set (ℂ × (ℂ × CircleL2 T))) (hU : IsOpen U) (hU0 : (0,(0,x)) ∈ U)
    (huniq : ∀ z a u, (z,(a,u)) ∈ U →
      circlePrincipalBlochFamily T h h₁ h₂ p hp z u =
        a • circlePrincipalResolvent T (p^4) (by positivity) u →
      inner ℂ ψ (circlePrincipalResolvent T (p^4) (by positivity) u) = 1 →
      a = μ z ∧ u = f z)

include hμ hf hμ0 hf0 hsol hU hU0 huniq in
theorem circle_analytic_eigenvalue_even
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hψ : circleReflect T ψ = -ψ) (hx : -circleReflect T x = x) :
    ∀ᶠ z in 𝓝 (0:ℂ), μ (-z) = μ z := by
  let C := circlePrincipalBlochFamily T h h₁ h₂ p hp
  let R := circlePrincipalResolvent T (p^4) (by positivity)
  let S : CircleL2 T →L[ℂ] CircleL2 T := -(circleReflectIsometry T).toContinuousLinearMap
  let Φ := (innerSL ℂ ψ).comp R
  have hμt : Tendsto μ (𝓝 0) (𝓝 (0:ℂ)) := by
    simpa only [hμ0] using hμ.continuousAt.tendsto
  have hft : Tendsto f (𝓝 0) (𝓝 x) := by
    simpa only [hf0] using hf.continuousAt.tendsto
  have hs' : ∀ᶠ z in 𝓝 (0:ℂ), C z (f z) = μ z • R (f z) ∧ Φ (f z) = 1 := by
    filter_upwards [hsol] with z hz
    exact ⟨hz.1,hz.2.1⟩
  apply eigenvalue_even_of_reflection C R S Φ x μ f hμt hft hx ?_ ?_ ?_ hs' U hU hU0 huniq
  · intro z u
    exact circle_principal_bloch_family_neg_reflect T h h₁ h₂ hh hh₁ hs p hp z u
  · intro u
    change circlePrincipalResolvent T (p^4) (by positivity) (-circleReflect T u) =
      -circleReflect T (circlePrincipalResolvent T (p^4) (by positivity) u)
    rw [map_neg,circle_principal_resolvent_reflect]
  · intro u
    exact circle_principal_normalization_neg_reflect T _ _ ψ hψ u

end Branch
end Lemniscate
