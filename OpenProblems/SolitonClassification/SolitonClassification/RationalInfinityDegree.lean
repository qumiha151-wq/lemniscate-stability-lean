import SolitonClassification.RationalPoleCoefficient
import Mathlib.Algebra.Polynomial.Reverse

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Polynomial Filter Set
open scoped Topology Polynomial
namespace ClosedSimilarity.RationalCurvature

private theorem reverse_value (P : ℂ[X]) {z : ℂ} (nz : z≠0) :
    P.eval z⁻¹=P.reverse.eval z*(z⁻¹)^P.natDegree := by
  let _ : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero nz)
  simpa only [invOf_eq_inv,inv_inv,eval₂_id] using
    (eval₂_reverse_mul_pow (RingHom.id ℂ) z⁻¹ P).symm

private theorem reverse_zero (P : ℂ[X]) : P.reverse.eval 0=P.leadingCoeff := by
  rw [←coeff_zero_eq_eval_zero,coeff_zero_reverse]

private theorem reciprocal_step {μ x : ℂ} {f g : ℂ→ℂ} (nz : x≠0)
    (hf : AnalyticAt ℂ f x⁻¹) (eq : g=ᶠ[𝓝 x] fun z=>f z⁻¹) :
    euler (-μ) g=ᶠ[𝓝 x] fun z=>euler μ f z⁻¹ := by
  have cinv : ContinuousAt (fun z:ℂ=>z⁻¹) x := continuousAt_inv₀ nz
  filter_upwards [eq.deriv,cinv.tendsto.eventually hf.eventually_analyticAt,
    (continuousAt_id (x:=x)).eventually_ne nz] with z der za zn
  have chain := za.differentiableAt.hasDerivAt.comp z (hasDerivAt_inv zn)
  have ch : deriv (fun u=>f u⁻¹) z=deriv f z⁻¹*(-(z^2)⁻¹) := chain.deriv
  simp only [euler,der,ch]
  field_simp [zn]

private theorem euler_analytic {μ x : ℂ} {f : ℂ→ℂ} (h : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (euler μ f) x := by
  unfold euler
  fun_prop

/-- Inversion changes the sign of the angular frequency and preserves the
full scalar ODE at the corresponding regular point. -/
theorem residual_reciprocal {μ a b x : ℂ} {f : ℂ→ℂ} (nz : x≠0)
    (h : AnalyticAt ℂ f x⁻¹) :
    residual (-μ) a b (fun z=>f z⁻¹) x=residual μ a b f x⁻¹ := by
  have h₁ := reciprocal_step (μ:=μ) nz h (EventuallyEq.refl _ _)
  have h₂ := reciprocal_step (μ:=μ) nz (euler_analytic h) h₁
  have h₃ := reciprocal_step (μ:=μ) nz (euler_analytic (euler_analytic h)) h₂
  have h₄ := reciprocal_step (μ:=μ) nz (euler_analytic (euler_analytic (euler_analytic h))) h₃
  simp only [residual,quadratic,quartic,D₄,D₃,D₂,h₁.eq_of_nhds,h₂.eq_of_nhds,
    h₃.eq_of_nhds,h₄.eq_of_nhds]

/-- A quotient with a higher-degree numerator genuinely has a pole at
infinity. The exponent and coefficient come from its actual polynomials. -/
theorem infinity_jet {A B : ℂ[X]} (bn : B≠0) :
    Jet (fun z=>quotient A B z⁻¹) 0 ((B.natDegree:ℤ)-A.natDegree)
      (A.leadingCoeff/B.leadingCoeff) := by
  have nb : B.reverse.eval 0≠0 := by rw [reverse_zero]; exact leadingCoeff_ne_zero.mpr bn
  refine ⟨fun z=>A.reverse.eval z/B.reverse.eval z,
    ((AnalyticOnNhd.eval_polynomial A.reverse) 0 (mem_univ _)).div
      ((AnalyticOnNhd.eval_polynomial B.reverse) 0 (mem_univ _)) nb,by simp [reverse_zero],?_⟩
  filter_upwards [eventually_mem_nhdsWithin] with z nz
  have zn : z≠0 := nz
  rw [quotient,reverse_value A zn,reverse_value B zn,sub_zero,zpow_sub₀ zn]
  simp only [zpow_natCast,inv_pow,div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem degree_bound_of_residual {A B : ℂ[X]} {μ a b : ℂ} (An : A≠0) (Bn : B≠0)
    (zero : ∀z,B.eval z≠0 → residual μ a b (quotient A B) z=0) : A.natDegree≤B.natDegree := by
  by_contra greater
  have nb : B.reverse.eval 0≠0 := by rw [reverse_zero]; exact leadingCoeff_ne_zero.mpr Bn
  have con : ContinuousAt (fun z=>B.reverse.eval z) (0:ℂ) := ((AnalyticOnNhd.eval_polynomial (𝕜:=ℂ) B.reverse) 0 (mem_univ _)).continuousAt
  have hg : residual (-μ) a b (fun z=>quotient A B z⁻¹)=ᶠ[𝓝[≠] 0] fun _=>0 := by
    filter_upwards [(con.eventually_ne nb).filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with z rev nz
    have zn : z≠0 := nz
    have br : B.eval z⁻¹≠0 := by
      rw [reverse_value B zn]
      exact mul_ne_zero rev (pow_ne_zero _ (inv_ne_zero zn))
    have ha : AnalyticAt ℂ (quotient A B) z⁻¹ :=
      ((AnalyticOnNhd.eval_polynomial A) z⁻¹ (mem_univ _)).div
        ((AnalyticOnNhd.eval_polynomial B) z⁻¹ (mem_univ _)) br
    exact (residual_reciprocal zn ha).trans (zero _ br)
  exact div_ne_zero (leadingCoeff_ne_zero.mpr An) (leadingCoeff_ne_zero.mpr Bn)
    (cannot_pole_at_zero (infinity_jet Bn) hg (by omega))

/-- A polynomial denominator is nonzero throughout a punctured
neighborhood of every point, including each of its own roots. -/
theorem punctured_regular {B : ℂ[X]} (bn : B≠0) (x : ℂ) :
    ∀ᶠ z in 𝓝[≠] x,B.eval z≠0 := by
  obtain ⟨G,fac,nd⟩ := B.exists_eq_pow_rootMultiplicity_mul_and_not_dvd bn x
  have gn : G.eval x≠0 := fun h=>nd (dvd_iff_isRoot.mpr h)
  have cont : ContinuousAt (fun z=>G.eval z) x :=
    ((AnalyticOnNhd.eval_polynomial (𝕜:=ℂ) G) x (mem_univ _)).continuousAt
  filter_upwards [(cont.eventually_ne gn).filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with z ng nz
  have eq := congrArg (Polynomial.eval z) fac
  simp only [eval_mul,eval_pow,eval_sub,eval_X,eval_C] at eq
  rw [eq]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr nz)) ng

theorem residual_germ_of_regular {A B : ℂ[X]} {μ a b : ℂ} (bn : B≠0)
    (zero : ∀z,B.eval z≠0 → residual μ a b (quotient A B) z=0) (x : ℂ) :
    residual μ a b (quotient A B)=ᶠ[𝓝[≠] x] fun _=>0 := by
  filter_upwards [punctured_regular bn x] with z nz
  exact zero _ nz

end ClosedSimilarity.RationalCurvature
