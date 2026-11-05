import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Complex.RealDeriv

/-! Orientation-preserving parameter changes are constant shifts after
passing to the actual arclength coordinates. -/
noncomputable section
namespace Lemniscate
open Filter

/-- Two parametrizations of the same oriented curve have equal lengths,
and their arclength coordinates differ by one constant shift. -/
theorem oriented_reparametrization_arclength_shift
    (γ η : ℝ → ℂ) (A B χ : ℝ ≃o ℝ)
    (hγ : Differentiable ℝ γ) (hχ : Differentiable ℝ (χ : ℝ → ℝ))
    (hχpos : ∀ s, 0<deriv (χ : ℝ → ℝ) s)
    (hcurve : ∀ s, γ (χ s)=η s)
    (hA : ∀ u, HasDerivAt (A : ℝ → ℝ) ‖deriv γ u‖ u)
    (hB : ∀ s, HasDerivAt (B : ℝ → ℝ) ‖deriv η s‖ s)
    (P Q L M : ℝ)
    (hAdeck : ∀ u, A (u+P)=A u+L)
    (hBdeck : ∀ s, B (s+Q)=B s+M)
    (hχdeck : ∀ s, χ (s+Q)=χ s+P) :
    ∃ c : ℝ, L=M ∧ ∀ s, χ s=A.symm (B s+c) := by
  let F : ℝ → ℝ := fun s => A (χ s)-B s
  have hzero (s : ℝ) : HasDerivAt F 0 s := by
    have hchain := (hγ (χ s)).hasDerivAt.scomp s (hχ s).hasDerivAt
    have hη : HasDerivAt η ((deriv (χ : ℝ → ℝ) s) • deriv γ (χ s)) s :=
      hchain.congr_of_eventuallyEq (Eventually.of_forall (fun x => (hcurve x).symm))
    have hspeed : ‖deriv η s‖=deriv (χ : ℝ → ℝ) s*‖deriv γ (χ s)‖ := by
      rw [hη.deriv,norm_smul,Real.norm_eq_abs,abs_of_pos (hχpos s)]
    have hd := ((hA (χ s)).comp s (hχ s).hasDerivAt).sub (hB s)
    apply hd.congr_deriv
    rw [hspeed]
    ring
  have hconst (s : ℝ) : F s=F 0 :=
    is_const_of_deriv_eq_zero (fun x => (hzero x).differentiableAt)
      (fun x => (hzero x).deriv) s 0
  let c := F 0
  have hshift (s : ℝ) : A (χ s)=B s+c := by
    have hh := hconst s
    change A (χ s)-B s=c at hh
    linarith only [hh]
  have hχQ : χ Q=χ 0+P := by simpa only [zero_add] using hχdeck 0
  have hBQ : B Q=B 0+M := by simpa only [zero_add] using hBdeck 0
  have hlength : L=M := by
    have hQ := hshift Q
    rw [hχQ,hAdeck,hBQ] at hQ
    linarith only [hQ,hshift 0]
  refine ⟨c,hlength,?_⟩
  intro s
  apply A.injective
  rw [A.apply_symm_apply,hshift]

end Lemniscate
