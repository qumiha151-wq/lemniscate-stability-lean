import LengthGrowth.ActualFlow.AbsoluteCurvatureCS
import LengthGrowth.ActualFlow.ConditionalQuarterGrowth
import LengthGrowth.EnergyFromLength

/-! An exact reduction for a single given forward normal free elastic flow.
The equivalent boundedness properties below are not asserted to hold.
All constants may depend on the entire given flow/initial curve. -/

noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

def HasBoundedAbsoluteCurvature : Prop :=
  ∃ A : ℝ, ∀ t, 0 ≤ t → c.absoluteCurvature t ≤ A

def HasBoundedEnergyLength : Prop :=
  ∃ K : ℝ, ∀ t, 0 ≤ t → c.energy t * c.length t ≤ K

def HasQuarterLengthBound : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ t, 0 ≤ t →
    c.length t ≤ K * FreeElasticScalar.fourthRoot (1 + t)

def HasQuarterEnergyBound : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∀ t, 0 ≤ t →
    c.energy t ≤ B / FreeElasticScalar.fourthRoot (1 + t)

theorem bounded_absoluteCurvature_of_bounded_energyLength
    (h : c.HasBoundedEnergyLength) : c.HasBoundedAbsoluteCurvature := by
  obtain ⟨K, hK⟩ := h
  have hK0 : 0 ≤ K := (mul_nonneg (c.energy_nonneg 0) (c.length_nonneg 0)).trans
    (hK 0 (by rfl))
  refine ⟨Real.sqrt (2 * K), ?_⟩
  intro t ht
  have hcs := c.absoluteCurvature_sq_le ht
  have hp := hK t ht
  have hs := Real.sq_sqrt (show 0 ≤ 2 * K by positivity)
  have hn := Real.sqrt_nonneg (2 * K)
  have hA := c.absoluteCurvature_lower ht
  nlinarith

theorem quarter_length_of_bounded_absoluteCurvature (hflow : c.IsNormalFEF)
    (h : c.HasBoundedAbsoluteCurvature) : c.HasQuarterLengthBound := by
  obtain ⟨A, hA⟩ := h
  have hAp := c.absoluteCurvature_cap_pos hA
  let C := 64 * A * Real.sqrt A
  have hC : 0 < C := by dsimp [C]; positivity
  have hL0 := c.length_pos (t := 0) (by rfl)
  refine ⟨c.length 0 + C, by positivity, ?_⟩
  intro t ht
  have hi := c.conditional_quarter_increment hflow hA ht
  have hmono := FreeElasticScalar.fourthRoot_mono (show t ≤ 1 + t by linarith)
  have hq : 1 ≤ FreeElasticScalar.fourthRoot (1 + t) := by
    simpa [FreeElasticScalar.fourthRoot] using
      FreeElasticScalar.fourthRoot_mono (show (1 : ℝ) ≤ 1 + t by linarith)
  have hm := mul_le_mul_of_nonneg_left hmono hC.le
  have hz := mul_le_mul_of_nonneg_left hq hL0.le
  dsimp only [C] at hm ⊢
  nlinarith

theorem quarter_energy_of_quarter_length (hflow : c.IsNormalFEF)
    (h : c.HasQuarterLengthBound) : c.HasQuarterEnergyBound := by
  obtain ⟨K, hK, hbound⟩ := h
  let a : ℝ := 1 / 2097152
  have ha : 0 < a := by norm_num [a]
  refine ⟨c.energy 0 + K ^ 3 / (4 * a), by
    have hE0 := c.energy_pos (t := 0) (by rfl)
    positivity, ?_⟩
  intro t ht
  exact FreeElasticScalar.energy_decay_of_quarter_length
    c.length c.energy c.dissipation a K ha hK c.energy_continuousOn
    (fun s hs => c.length_pos hs) (fun s hs => c.energy_pos hs)
    (fun s hs => c.energy_hasDerivAt_normal hflow hs)
    (fun s hs => c.weak_virial hs.le) hbound t ht

theorem bounded_energyLength_of_quarter_length (hflow : c.IsNormalFEF)
    (h : c.HasQuarterLengthBound) : c.HasBoundedEnergyLength := by
  obtain ⟨K, hK, hbound⟩ := h
  let a : ℝ := 1 / 2097152
  have ha : 0 < a := by norm_num [a]
  refine ⟨K * (c.energy 0 + K ^ 3 / (4 * a)), ?_⟩
  intro t ht
  exact FreeElasticScalar.energy_length_cap_of_quarter_length
    c.length c.energy c.dissipation a K ha hK c.energy_continuousOn
    (fun s hs => c.length_pos hs) (fun s hs => c.energy_pos hs)
    (fun s hs => c.energy_hasDerivAt_normal hflow hs)
    (fun s hs => c.weak_virial hs.le) hbound t ht

theorem quarter_length_of_quarter_energy (hflow : c.IsNormalFEF)
    (h : c.HasQuarterEnergyBound) : c.HasQuarterLengthBound := by
  obtain ⟨B, hB, hbound⟩ := h
  have hL0 := c.length_pos (t := 0) (by rfl)
  refine ⟨c.length 0 + 4 * B, by positivity, ?_⟩
  intro t ht
  have hw := FreeElasticScalar.weighted_length_zero_shift
    c.length c.energy c.lengthRate c.dissipation B 1 hB.le (by norm_num)
    c.length_continuousOn c.energy_continuousOn (fun s _ => c.energy_nonneg s)
    (fun s _ => c.dissipation_nonneg s)
    (fun s hs => c.length_hasDerivAt_normal hflow hs)
    (fun s hs => c.energy_hasDerivAt_normal hflow hs)
    (fun s hs => c.lengthRate_sq_le hs.le)
    (fun s hs => by simpa only [add_comm] using hbound s hs) t ht
  have he := mul_nonneg (Real.sqrt_nonneg t) (c.energy_nonneg t)
  have hmono := FreeElasticScalar.fourthRoot_mono (show t ≤ 1 + t by linarith)
  have hq : 1 ≤ FreeElasticScalar.fourthRoot (1 + t) := by
    simpa [FreeElasticScalar.fourthRoot] using
      FreeElasticScalar.fourthRoot_mono (show (1 : ℝ) ≤ 1 + t by linarith)
  have hm := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 4 * B by positivity)
  have hz := mul_le_mul_of_nonneg_left hq hL0.le
  nlinarith

theorem quarter_length_iff_bounded_absoluteCurvature (hflow : c.IsNormalFEF) :
    c.HasQuarterLengthBound ↔ c.HasBoundedAbsoluteCurvature :=
  ⟨fun h => c.bounded_absoluteCurvature_of_bounded_energyLength
    (c.bounded_energyLength_of_quarter_length hflow h),
   c.quarter_length_of_bounded_absoluteCurvature hflow⟩

theorem quarter_length_iff_bounded_energyLength (hflow : c.IsNormalFEF) :
    c.HasQuarterLengthBound ↔ c.HasBoundedEnergyLength :=
  ⟨c.bounded_energyLength_of_quarter_length hflow,
    fun h => c.quarter_length_of_bounded_absoluteCurvature hflow
      (c.bounded_absoluteCurvature_of_bounded_energyLength h)⟩

theorem quarter_length_iff_quarter_energy (hflow : c.IsNormalFEF) :
    c.HasQuarterLengthBound ↔ c.HasQuarterEnergyBound :=
  ⟨c.quarter_energy_of_quarter_length hflow, c.quarter_length_of_quarter_energy hflow⟩

end LengthGrowth.ActualFlow.ForwardImmersion

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf n || (`FreeElasticScalar).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  logInfo m!"Actual growth equivalence: {count} declarations; standard axioms only."
