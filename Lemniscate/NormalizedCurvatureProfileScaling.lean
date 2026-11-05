import Lemniscate.NormalizedCurvatureProfileEntry
import Lemniscate.PeriodicCurveDilation
import Mathlib.Data.Real.Pointwise

/-! Changing the normalization length and the reference curvature by one
positive dilation leaves the intrinsic curvature-profile error unchanged.
The integral identity and the real sInf scaling formula require no
regularity, integrability, periodicity, or attainment hypotheses.

-/
noncomputable section
namespace Lemniscate
open Set MeasureTheory
open scoped Pointwise

private theorem normalized_curvature_scaling
    (a ℓ P : ℝ) (γ : ℝ → ℂ) (x : ℝ) :
    normalizedImmersionCurvature (a*ℓ) P γ x =
      normalizedImmersionCurvature ℓ P γ (x/a)/a := by
  let L : ℝ := ∫ u in (0:ℝ)..P, ‖deriv γ u‖
  let κ : ℝ → ℝ := fun s => planarSignedCurvature γ
    (Function.invFun (fun u => ∫ v in (0:ℝ)..u, ‖deriv γ v‖) s)
  change κ ((L/(a*ℓ))*x)*(L/(a*ℓ)) = (κ ((L/ℓ)*(x/a))*(L/ℓ))/a
  have hcoeff : L/(a*ℓ) = (L/ℓ)/a := div_mul_eq_div_div_swap L a ℓ
  have harg : (L/(a*ℓ))*x = (L/ℓ)*(x/a) := by
    rw [hcoeff]
    simp only [div_eq_mul_inv]
    ring
  rw [harg,hcoeff]
  simp only [div_eq_mul_inv]
  ring

/-- The intrinsic curvature-profile error is unchanged by simultaneously
dilating the normalization length and the reference signed curvature. -/
theorem normalized_curvature_profile_error_scaling
    (a ℓ P : ℝ) (ha : 0 < a) (γ : ℝ → ℂ) (k : ℝ → ℝ) :
    normalizedCurvatureProfileError (a*ℓ) P γ (fun x => k (x/a)/a) =
      normalizedCurvatureProfileError ℓ P γ k := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp only [normalizedCurvatureProfileError,mul_zero,zero_mul]
  let f : ℝ → ℝ := normalizedImmersionCurvature ℓ P γ
  let J : ℝ → ℝ := fun σ => ∫ x in (0:ℝ)..ℓ, (f x-k (x+σ))^2
  let Ja : ℝ → ℝ := fun θ => ∫ x in (0:ℝ)..(a*ℓ),
    (normalizedImmersionCurvature (a*ℓ) P γ x-k ((x+θ)/a)/a)^2
  have hweighted (σ : ℝ) : (a*ℓ)*Ja (a*σ) = ℓ*J σ := by
    calc
      _ = (a*ℓ)*(∫ x in (0:ℝ)..(a*ℓ), ((f (x/a)-k (x/a+σ))/a)^2) := by
        apply congrArg (fun z : ℝ => (a*ℓ)*z)
        apply intervalIntegral.integral_congr
        intro x _
        have harg : (x+a*σ)/a = x/a+σ := by field_simp [ha.ne'] <;> ring
        change (normalizedImmersionCurvature (a*ℓ) P γ x-k ((x+a*σ)/a)/a)^2 =
          ((f (x/a)-k (x/a+σ))/a)^2
        rw [normalized_curvature_scaling a ℓ P γ x,harg,← sub_div]
      _ = ℓ*J σ := dilated_curvature_integral a ℓ ha (fun x => k (x+σ)) f
  have hcov (σ : ℝ) : Ja (a*σ) = a⁻¹*J σ := by
    apply mul_left_cancel₀ (mul_ne_zero ha.ne' hℓ)
    calc
      (a*ℓ)*Ja (a*σ) = ℓ*J σ := hweighted σ
      _ = (a*ℓ)*(a⁻¹*J σ) := by field_simp [ha.ne'] <;> ring
  have hrange : Set.range Ja = a⁻¹ • Set.range J := by
    ext y
    constructor
    · rintro ⟨θ,rfl⟩
      apply Set.mem_smul_set.mpr
      refine ⟨J (θ/a),⟨θ/a,rfl⟩,?_⟩
      change a⁻¹*J (θ/a) = Ja θ
      have harg : a*(θ/a) = θ := by field_simp [ha.ne'] <;> ring
      exact (hcov (θ/a)).symm.trans (congrArg Ja harg)
    · intro hy
      obtain ⟨z,⟨σ,rfl⟩,hz⟩ := Set.mem_smul_set.mp hy
      change a⁻¹*J σ = y at hz
      exact ⟨a*σ,(hcov σ).trans hz⟩
  have hinf : sInf (Set.range Ja) = a⁻¹*sInf (Set.range J) := by
    rw [hrange]
    simpa only [smul_eq_mul] using
      Real.sInf_smul_of_nonneg (inv_pos.mpr ha).le (Set.range J)
  change (a*ℓ)*sInf (Set.range Ja) = ℓ*sInf (Set.range J)
  rw [hinf]
  field_simp [ha.ne'] <;> ring

end Lemniscate
