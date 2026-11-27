import SolitonClassification.GraphProfileEquation

/-! At a reflected crossing the stress identity gives a quadratic error in
curvature for the exceptional slope. The estimate works for an arbitrary
small seam slope, without assuming that it decays at the perturbation rate. -/
noncomputable section
namespace ClosedSimilarity.CrossingTangencies

/-- The physical stress identity and orthogonality to the seam at a
tangency determine the seam slope from stress and signed curvature. -/
theorem slope_at_tangency {β tx ty wx wy k : ℝ}
    (ht : tx ≠ 0) (hw : wy ≠ 0)
    (stress : wx*tx+wy*ty = k^2/2) (tangent : β*tx+ty=0) :
    β = wx/wy - (1/(2*tx*wy))*k^2 := by
  field_simp
  linear_combination 2*wy*tangent - 2*stress

/-- Tangency improves a small slope to a slope of order ε, with a
quadratic error relative to the stress direction. -/
theorem tangency_accuracy {D ε β w q k : ℝ} (hD : 1≤D) (he : 0≤ε)
    (smallE : 4*D^3*ε≤1) (smallB : 4*D^3*|β|≤1)
    (hw : |w|≤D*ε) (hq : |q|≤D) (hk : |k|≤D*(|β|+ε))
    (ht : β=w-q*k^2) :
    |β|≤3*D*ε ∧ |β-w|≤16*D^5*ε^2 := by
  have pos : 0≤D := by linarith
  have hk2 : |q*k^2|≤D^3*(|β|+ε)^2 := by
    rw [abs_mul,abs_pow]
    calc
      |q| * |k|^2 ≤ D * (D*(|β|+ε))^2 :=
        mul_le_mul hq (pow_le_pow_left₀ (abs_nonneg _) hk 2) (sq_nonneg _) pos
      _ = _ := by ring
  have small : D^3*(|β|+ε)^2 ≤ (|β|+ε)/2 := by
    have h₁ := mul_nonneg (sub_nonneg.mpr smallB) (abs_nonneg β)
    have h₂ := mul_nonneg (sub_nonneg.mpr smallE) he
    have h₃ := mul_nonneg (pow_nonneg pos 3) (sq_nonneg (|β|-ε))
    nlinarith only [h₁,h₂,h₃]
  have aux : |β| ≤ D*ε+(|β|+ε)/2 := by
    calc
      |β| = |w-q*k^2| := congrArg abs ht
      _ ≤ |w|+|q*k^2| := abs_sub _ _
      _ ≤ D*ε+(|β|+ε)/2 := add_le_add hw (hk2.trans small)
  have hβ : |β| ≤ 3*D*ε := by nlinarith [mul_nonneg (sub_nonneg.mpr hD) he]
  refine ⟨hβ,?_⟩
  have bound : |β|+ε ≤ 4*D*ε := by nlinarith [mul_nonneg (sub_nonneg.mpr hD) he]
  calc
    |β-w| = |q*k^2| := by rw [show β-w= -(q*k^2) by linarith only [ht],abs_neg]
    _ ≤ D^3*(|β|+ε)^2 := hk2
    _ ≤ D^3*(4*D*ε)^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (add_nonneg (abs_nonneg _) he) bound 2) (pow_nonneg pos 3)
    _ = _ := by ring

/-- A common physical seam slope cannot give tangency in both windows
when their stress directions differ by more than the two error bounds. -/
theorem distinct_stress_excludes_simultaneous_tangency {D ε β w₁ q₁ k₁ w₂ q₂ k₂ : ℝ}
    (hD : 1≤D) (he : 0≤ε) (smallE : 4*D^3*ε≤1) (smallB : 4*D^3*|β|≤1)
    (hw₁ : |w₁|≤D*ε) (hq₁ : |q₁|≤D) (hk₁ : |k₁|≤D*(|β|+ε))
    (hw₂ : |w₂|≤D*ε) (hq₂ : |q₂|≤D) (hk₂ : |k₂|≤D*(|β|+ε))
    (gap : 32*D^5*ε^2 < |w₁-w₂|) :
    ¬ (β=w₁-q₁*k₁^2 ∧ β=w₂-q₂*k₂^2) := by
  rintro ⟨t₁,t₂⟩
  have a := (tangency_accuracy hD he smallE smallB hw₁ hq₁ hk₁ t₁).2
  have b := (tangency_accuracy hD he smallE smallB hw₂ hq₂ hk₂ t₂).2
  have triangle := abs_sub_le w₁ β w₂
  rw [abs_sub_comm w₁ β] at triangle
  linarith

end ClosedSimilarity.CrossingTangencies

#print axioms ClosedSimilarity.CrossingTangencies.distinct_stress_excludes_simultaneous_tangency
