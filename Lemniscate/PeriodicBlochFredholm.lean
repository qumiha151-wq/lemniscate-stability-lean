import Lemniscate.PeriodicBlochCompactResolvent
import Lemniscate.PeriodicFredholmAlternative

/-! The genuine bounded-inverse spectrum of the Bloch operator on its fixed
H4 domain. Compact resolvent implies that every spectral point is an
eigenvalue. At alpha=0 this is exactly the previously defined spectrum. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

def circleBlochResolventSet (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ) : Set ℂ :=
  {w | ∃ R : CircleL2 T →L[ℂ] CircleL2 T, CircleBlochInverseIdentities T h h₁ h₂ α w R}

def circleBlochSpectrum (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ) : Set ℂ :=
  (circleBlochResolventSet T h h₁ h₂ α)ᶜ

theorem circle_bloch_spectrum_at_zero (h h₁ h₂ : C(AddCircle T, ℂ)) :
    circleBlochSpectrum T h h₁ h₂ 0 = circleSpectrum T h h₁ h₂ := by
  simp only [circleBlochSpectrum,circleSpectrum,circleBlochResolventSet,circleResolventSet,
    CircleBlochInverseIdentities,CircleInverseIdentities,circleBlochComplexShift,circleComplexShift,
    circle_bloch_at_zero]

set_option maxHeartbeats 1000000 in
private theorem bloch_shift_alternative (h h₁ h₂ : C(AddCircle T, ℂ)) (α r : ℝ)
    (R : CircleL2 T →L[ℂ] CircleL2 T) (hcompact : IsCompactOperator R)
    (hR : CircleBlochInverseIdentities T h h₁ h₂ α (r:ℂ) R) (w : ℂ) :
    (∃ u : circleH4Domain T, (u:CircleL2 T) ≠ 0 ∧ circleBlochComplexShift T h h₁ h₂ α w u = 0) ∨
    (∃ S : CircleL2 T →L[ℂ] CircleL2 T,
      IsCompactOperator S ∧ CircleBlochInverseIdentities T h h₁ h₂ α w S) := by
  let F : CircleL2 T →L[ℂ] CircleL2 T := ((r:ℂ)-w) • R
  have hF : IsCompactOperator F := by
    change IsCompactOperator (((r:ℂ)-w) • (R : CircleL2 T → CircleL2 T))
    exact hcompact.smul _
  have hshift (u : circleH4Domain T) : circleBlochComplexShift T h h₁ h₂ α w u =
      circleBlochComplexShift T h h₁ h₂ α (r:ℂ) u+(w-(r:ℂ)) • (u:CircleL2 T) := by
    simp only [circleBlochComplexShift,LinearMap.sub_apply,LinearMap.smul_apply,Submodule.subtype_apply]
    module
  have hfactor (u : circleH4Domain T) : circleBlochComplexShift T h h₁ h₂ α w u =
      (1-F) (circleBlochComplexShift T h h₁ h₂ α (r:ℂ) u) := by
    rw [hshift]
    simp only [sub_apply,one_apply_eq_self,F,smul_apply,hR.2]
    module
  rcases hF.hasEigenvalue_or_mem_resolventSet (by norm_num : (1:ℂ) ≠ 0) with he | hr
  · left
    obtain ⟨v,hv⟩ := he.exists_hasEigenvector
    have hfv : F v = v := by
      have h := hv.apply_eq_smul
      change F v = (1:ℂ) • v at h
      simpa only [one_smul] using h
    obtain ⟨u,hu,hinv⟩ := hR.1 v
    refine ⟨u,?_,?_⟩
    · intro hz
      have hu0 : u = 0 := Subtype.ext hz
      rw [hu0,map_zero] at hinv
      exact hv.2 hinv.symm
    · rw [hshift,hinv,hu]
      have h := hfv
      change ((r:ℂ)-w) • R v = v at h
      calc
        _ = v-((r:ℂ)-w) • R v := by module
        _ = 0 := sub_eq_zero.mpr h.symm
  · right
    have hunit : IsUnit (1-F) := by
      simpa only [spectrum.mem_resolventSet_iff,map_one] using hr
    obtain ⟨U,hU⟩ := hunit
    let Q : CircleL2 T →L[ℂ] CircleL2 T := ↑U⁻¹
    have hright (v : CircleL2 T) : (1-F) (Q v) = v := by
      rw [← hU]
      simpa only [mul_apply_eq_comp,one_apply_eq_self,Q] using
        congrArg (fun L : CircleL2 T →L[ℂ] CircleL2 T => L v) (Units.mul_inv U)
    have hleft (v : CircleL2 T) : Q ((1-F) v) = v := by
      rw [← hU]
      simpa only [mul_apply_eq_comp,one_apply_eq_self,Q] using
        congrArg (fun L : CircleL2 T →L[ℂ] CircleL2 T => L v) (Units.inv_mul U)
    refine ⟨R.comp Q,hcompact.comp_clm Q,?_,?_⟩
    · intro f
      obtain ⟨u,hu,hinv⟩ := hR.1 (Q f)
      refine ⟨u,hu,?_⟩
      rw [hshift,hinv,hu]
      have h := hright f
      simp only [sub_apply,one_apply_eq_self,F,smul_apply] at h
      calc
        _ = Q f-((r:ℂ)-w) • R (Q f) := by module
        _ = f := h
    · intro u
      change R (Q (circleBlochComplexShift T h h₁ h₂ α w u)) = (u:CircleL2 T)
      rw [hfactor,hleft,hR.2]

theorem circle_bloch_spectrum_iff_eigenvector (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : ‖h‖ ≤ 1) (hh₁ : ‖h₁‖ ≤ 2) (hh₂ : ‖h₂‖ ≤ 4)
    (α : ℝ) (hz : ‖(α:ℂ)*circleFrequencyFactor T 1‖ ≤ 1) (w : ℂ) :
    w ∈ circleBlochSpectrum T h h₁ h₂ α ↔
      ∃ u : circleH4Domain T, (u:CircleL2 T) ≠ 0 ∧
        circleBlochOperator T h h₁ h₂ α u = w • (u:CircleL2 T) := by
  constructor
  · intro hw
    obtain ⟨r,_,R,hcompact,hR⟩ := circle_bloch_compact_resolvent_exists T h h₁ h₂ hh hh₁ hh₂ α hz
    rcases bloch_shift_alternative T h h₁ h₂ α r R hcompact hR w with he | hr
    · obtain ⟨u,hune,hu⟩ := he
      refine ⟨u,hune,?_⟩
      change w • (u:CircleL2 T)-circleBlochOperator T h h₁ h₂ α u = 0 at hu
      exact (sub_eq_zero.mp hu).symm
    · obtain ⟨S,_,hS⟩ := hr
      exact False.elim (hw ⟨S,hS⟩)
  · rintro ⟨u,hune,hu⟩ ⟨R,hR⟩
    have hi := hR.2 u
    have hs : circleBlochComplexShift T h h₁ h₂ α w u = 0 := by
      change w • (u:CircleL2 T)-circleBlochOperator T h h₁ h₂ α u = 0
      rw [hu,sub_self]
    rw [hs,map_zero] at hi
    exact hune hi.symm

end Lemniscate
