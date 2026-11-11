import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A scalar criterion for migration by positive homothety

This file proves a geometric implication only. It does not construct a
free-elastic-flow expander or assume that an arbitrary profile solves that PDE.
For a height profile `y`, the translated initial height is `p + y s`, and
the height after dilation by `rho` about the untranslated origin is
`p + rho * y s`.
-/

namespace FreeElasticFlow

/-- A uniformly bounded profile strictly below the expansion centre can be
translated above the horizontal axis and then dilated entirely below it.
The formula works for every index type, with no finiteness assumption. -/
theorem oneSidedProfile_migrates {ι : Type*} (y : ι → ℝ) (a b : ℝ)
    (hbound : ∀ s, a ≤ y s ∧ y s ≤ b) (hb : b < 0) :
    ∃ p rho : ℝ, -a < p ∧ 1 < rho ∧
      ∀ s, 0 < p + y s ∧ p + rho * y s < 0 := by
  let p : ℝ := 1 + |a|
  have hp : 0 < p := by
    dsimp [p]
    linarith [abs_nonneg a]
  have hpa : -a < p := by
    dsimp [p]
    linarith [neg_le_abs a]
  let rho : ℝ := 1 + (p + 1) / (-b)
  have hrho : 1 < rho := by
    have hdiv : 0 < (p + 1) / (-b) :=
      div_pos (by linarith) (by linarith)
    dsimp [rho]
    linarith
  have hproduct : rho * b = b - (p + 1) := by
    dsimp [rho]
    field_simp [ne_of_lt hb]
    ring
  refine ⟨p, rho, hpa, hrho, ?_⟩
  intro s
  obtain ⟨hlo, hhi⟩ := hbound s
  constructor
  · linarith
  · have hscaled : rho * y s ≤ rho * b :=
      mul_le_mul_of_nonneg_left hhi (by linarith)
    linarith

/-- Two strict half-plane inequalities at scales `1` and `rho > 1`
force each profile point to lie below the expansion centre. -/
theorem migration_forces_negative_profile {ι : Type*} (y : ι → ℝ)
    (p rho : ℝ) (hrho : 1 < rho)
    (hmigrate : ∀ s, 0 < p + y s ∧ p + rho * y s < 0) :
    ∀ s, y s < 0 := by
  intro s
  obtain ⟨hbefore, hafter⟩ := hmigrate s
  by_contra h
  have hy : 0 ≤ y s := le_of_not_gt h
  nlinarith

/-- In particular, whenever the profile has an attained maximum, migration
forces that maximum to be strictly negative. Compact continuous nonempty
profiles have such a maximum, but no topological assumption is needed here. -/
theorem migration_forces_negative_attained_maximum {ι : Type*} (y : ι → ℝ)
    (p rho b : ℝ) (hrho : 1 < rho)
    (hmigrate : ∀ s, 0 < p + y s ∧ p + rho * y s < 0)
    (hattained : ∃ s, y s = b) : b < 0 := by
  obtain ⟨s, hs⟩ := hattained
  have hnegative := migration_forces_negative_profile y p rho hrho hmigrate s
  simpa only [hs] using hnegative

/-- For a bounded profile with attained maximum `b`, existence of a translated
homothetic migration is equivalent to strict one-sidedness `b < 0`. -/
theorem boundedProfile_migration_iff {ι : Type*} (y : ι → ℝ) (a b : ℝ)
    (hbound : ∀ s, a ≤ y s ∧ y s ≤ b)
    (hattained : ∃ s, y s = b) :
    (∃ p rho : ℝ, -a < p ∧ 1 < rho ∧
      ∀ s, 0 < p + y s ∧ p + rho * y s < 0) ↔ b < 0 := by
  constructor
  · rintro ⟨p, rho, _, hrho, hmigrate⟩
    exact migration_forces_negative_attained_maximum
      y p rho b hrho hmigrate hattained
  · exact oneSidedProfile_migrates y a b hbound

end FreeElasticFlow

#print axioms FreeElasticFlow.oneSidedProfile_migrates
#print axioms FreeElasticFlow.migration_forces_negative_profile
#print axioms FreeElasticFlow.migration_forces_negative_attained_maximum
#print axioms FreeElasticFlow.boundedProfile_migration_iff
