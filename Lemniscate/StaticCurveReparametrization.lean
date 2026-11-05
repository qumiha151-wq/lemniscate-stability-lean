import Lemniscate.BernoulliExpander
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The elastic operator and projected free elastic flow are preserved
by a static orientation-preserving smooth change of parameter. -/
noncomputable section
namespace Lemniscate
open Complex
open scoped ContDiff ComplexConjugate

/-- The curvature, arclength derivative and elastic force of an immersed
curve are geometric under an orientation-preserving change of parameter.
The identities follow from the actual first and second derivative chain
rules; no covariance identity is assumed. -/
theorem oriented_reparametrization_elastic_geometry
    (γ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hγ : ContDiff ℝ ∞ γ) (hχ : ContDiff ℝ ∞ χ)
    (hreg : ∀ s, deriv γ s ≠ 0) (hpos : ∀ s, 0 < deriv χ s) :
    let Γ := γ ∘ χ
    (∀ s, deriv Γ s ≠ 0 ∧
      I*deriv Γ s/(‖deriv Γ s‖:ℂ) =
        I*deriv γ (χ s)/(‖deriv γ (χ s)‖:ℂ)) ∧
    planarSignedCurvature Γ = planarSignedCurvature γ ∘ χ ∧
    (∀ f : ℝ → ℝ, Differentiable ℝ f →
      arclengthDerivative Γ (f ∘ χ) = arclengthDerivative γ f ∘ χ) ∧
    (fun s => arclengthDerivative Γ
        (arclengthDerivative Γ (planarSignedCurvature Γ)) s+
      (1/2:ℝ)*(planarSignedCurvature Γ s)^3) =
      (fun s => arclengthDerivative γ
          (arclengthDerivative γ (planarSignedCurvature γ)) s+
        (1/2:ℝ)*(planarSignedCurvature γ s)^3) ∘ χ := by
  let Γ := γ ∘ χ
  let g := deriv χ
  have hγ₁ := (contDiff_infty_iff_deriv.mp hγ).2
  have hγ₂ := (contDiff_infty_iff_deriv.mp hγ₁).2
  have hχ₁ := (contDiff_infty_iff_deriv.mp hχ).2
  have hχd (s : ℝ) : HasDerivAt χ (g s) s :=
    (hχ.differentiable (by simp) s).hasDerivAt
  have hfirst (s : ℝ) : HasDerivAt Γ ((g s:ℂ)*deriv γ (χ s)) s := by
    simpa only [real_smul] using!
      ((hγ.differentiable (by simp) (χ s)).hasDerivAt.scomp s (hχd s))
  have hderiv : deriv Γ = fun s => (g s:ℂ)*deriv γ (χ s) :=
    funext fun s => (hfirst s).deriv
  have hspeed (s : ℝ) : ‖deriv Γ s‖ = g s*‖deriv γ (χ s)‖ := by
    rw [hderiv,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hpos s)]
  have hsecond (s : ℝ) : HasDerivAt (deriv Γ)
      (((deriv g s:ℝ):ℂ)*deriv γ (χ s)+
        (g s:ℂ)^2*deriv (deriv γ) (χ s)) s := by
    rw [hderiv]
    convert! ((hχ₁.differentiable (by simp) s).hasDerivAt.ofReal_comp).mul
      ((hγ₁.differentiable (by simp) (χ s)).hasDerivAt.scomp s (hχd s)) using 1
    simp only [real_smul,Function.comp_def]
    ring
  have hcurv : planarSignedCurvature Γ = planarSignedCurvature γ ∘ χ := by
    funext s
    have hc : conj ((g s:ℂ)*deriv γ (χ s))*
        (((deriv g s:ℝ):ℂ)*deriv γ (χ s)+
          (g s:ℂ)^2*deriv (deriv γ) (χ s)) =
        ((g s*deriv g s:ℝ):ℂ)*(conj (deriv γ (χ s))*deriv γ (χ s))+
        (((g s)^3:ℝ):ℂ)*(conj (deriv γ (χ s))*deriv (deriv γ) (χ s)) := by
      simp only [map_mul,Complex.conj_ofReal]
      push_cast
      ring
    have hi : (conj ((g s:ℂ)*deriv γ (χ s))*
        (((deriv g s:ℝ):ℂ)*deriv γ (χ s)+
          (g s:ℂ)^2*deriv (deriv γ) (χ s))).im =
        (g s)^3*(conj (deriv γ (χ s))*deriv (deriv γ) (χ s)).im := by
      rw [hc,Complex.conj_mul']
      simp only [← Complex.ofReal_pow,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,mul_zero,
        zero_add,add_zero]
    change (conj (deriv Γ s)*deriv (deriv Γ) s).im/‖deriv Γ s‖^3 =
      (conj (deriv γ (χ s))*deriv (deriv γ) (χ s)).im/‖deriv γ (χ s)‖^3
    rw [hspeed,(hfirst s).deriv,(hsecond s).deriv,hi]
    have hg : g s ≠ 0 := ne_of_gt (hpos s)
    field_simp [hg,norm_ne_zero_iff.mpr (hreg (χ s))]
    <;> ring
  have hD (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
      arclengthDerivative Γ (f ∘ χ) = arclengthDerivative γ f ∘ χ := by
    funext s
    change deriv (f ∘ χ) s/‖deriv Γ s‖ = deriv f (χ s)/‖deriv γ (χ s)‖
    rw [deriv_comp s (hf (χ s)) (hχ.differentiable (by simp) s),hspeed]
    dsimp only [g]
    field_simp [ne_of_gt (hpos s),norm_ne_zero_iff.mpr (hreg (χ s))]
    <;> ring
  have hspeedSmooth : ContDiff ℝ ∞ (fun s => ‖deriv γ s‖) := hγ₁.norm ℝ hreg
  have hk : ContDiff ℝ ∞ (planarSignedCurvature γ) := by
    have hn : ContDiff ℝ ∞
        (fun s => (conj (deriv γ s)*deriv (deriv γ) s).im) :=
      Complex.imCLM.contDiff.comp ((Complex.conjCLE.contDiff.comp hγ₁).mul hγ₂)
    exact hn.div (hspeedSmooth.pow 3)
      (fun s => pow_ne_zero 3 (norm_ne_zero_iff.mpr (hreg s)))
  have hDk : ContDiff ℝ ∞ (arclengthDerivative γ (planarSignedCurvature γ)) :=
    (contDiff_infty_iff_deriv.mp hk).2.div hspeedSmooth
      (fun s => norm_ne_zero_iff.mpr (hreg s))
  refine ⟨?_,hcurv,hD,?_⟩
  · intro s
    have hg : (g s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hpos s))
    refine ⟨by rw [hderiv]; exact mul_ne_zero hg (hreg (χ s)),?_⟩
    rw [hspeed,hderiv]
    push_cast
    field_simp [hg,Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hreg (χ s)))]
    <;> ring
  · rw [hcurv,hD (planarSignedCurvature γ) (hk.differentiable (by simp)),
      hD (arclengthDerivative γ (planarSignedCurvature γ))
        (hDk.differentiable (by simp))]
    rfl

/-- A fixed smooth orientation-preserving change of space parameter
preserves the actual projected free elastic flow. It therefore returns
a reconstructed flow to the original initial parametrization. -/
theorem static_reparametrization_free_elastic_flow
    (Y : ℝ → ℝ → ℂ) (χ : ℝ → ℝ) (S : Set ℝ) (t₀ : ℝ) (V : ℝ → ℂ)
    (hY : ContDiff ℝ ∞ (Y t₀)) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ s, 0 < deriv χ s)
    (hflow : ∀ s,
      let ν := I*deriv (Y t₀) s/(‖deriv (Y t₀) s‖:ℂ)
      HasDerivWithinAt (fun z => Y z s) (V s) S t₀ ∧
      deriv (Y t₀) s ≠ 0 ∧ ‖ν‖ = 1 ∧
      (((conj (V s)*ν).re:ℂ)*ν) =
        -((arclengthDerivative (Y t₀)
            (arclengthDerivative (Y t₀) (planarSignedCurvature (Y t₀))) s+
          (1/2:ℝ)*(planarSignedCurvature (Y t₀) s)^3:ℝ):ℂ)*ν) :
    let γ : ℝ → ℝ → ℂ := fun t s => Y t (χ s)
    ∀ s,
      let ν := I*deriv (γ t₀) s/(‖deriv (γ t₀) s‖:ℂ)
      HasDerivWithinAt (fun z => γ z s) (V (χ s)) S t₀ ∧
      deriv (γ t₀) s ≠ 0 ∧ ‖ν‖ = 1 ∧
      (((conj (V (χ s))*ν).re:ℂ)*ν) =
        -((arclengthDerivative (γ t₀)
            (arclengthDerivative (γ t₀) (planarSignedCurvature (γ t₀))) s+
          (1/2:ℝ)*(planarSignedCurvature (γ t₀) s)^3:ℝ):ℂ)*ν := by
  have hgeom := oriented_reparametrization_elastic_geometry (Y t₀) χ
    hY hχ (fun s => (hflow s).2.1) hpos
  dsimp only
  intro s
  have hnormal := (hgeom.1 s).2
  have hforce := congrArg (fun f : ℝ → ℝ => f s) hgeom.2.2.2
  dsimp only [Function.comp_def] at hnormal hforce
  refine ⟨(hflow (χ s)).1,(hgeom.1 s).1,?_,?_⟩
  · rw [hnormal]
    exact (hflow (χ s)).2.2.1
  · rw [hnormal,hforce]
    exact (hflow (χ s)).2.2.2

end Lemniscate
