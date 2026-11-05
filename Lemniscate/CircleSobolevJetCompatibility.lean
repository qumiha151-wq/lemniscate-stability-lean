import Lemniscate.CircleSobolevJetLift
import Lemniscate.PeriodicSobolevTruncation
import Lemniscate.NormalGraphSobolevFlow

/-! The lifted physical jets are the actual low-order Sobolev coordinates,
including the fourth derivative retained in L2. -/
noncomputable section
namespace Lemniscate
open Complex
variable (T : ℝ) [Fact (0<T)]

theorem circle_sobolev_physical_jet_compatibility (m : ℕ)
    (f : CircleSobolevSpace T (m+5)) :
    let f4 := circleSobolevTruncation T 4 (m+5) (by omega) f
    (∀ j : Fin 4, circleClassicalJetValue T m
      (circleSobolevPhysicalJetLift T m f j.castSucc) =
        circleNormalGraphCoordinates T f4 j) ∧
    circleContinuousL2 T (circleClassicalJetValue T m
      (circleSobolevPhysicalJetLift T m f 4)) =
        (4:ℂ) • circleSobolevCoordinate T 4 4 f4 := by
  dsimp only
  have hjet (j : Fin 4) :
      circleSobolevClassicalJet T (m+4) f
        ⟨j.val,by omega⟩ =
      circleSobolevContinuousJet T
        (circleSobolevTruncation T 4 (m+5) (by omega) f) j := by
    apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 T _ = circleContinuousL2 T _
    rw [circle_sobolev_classical_jet_l2,circle_sobolev_classical_jet_l2,
      circle_sobolev_truncation_coordinate]
    rfl
  constructor
  · intro j
    rw [circle_sobolev_physical_jet_lift_value]
    change (((Real.sqrt 2)^j.val:ℝ):ℂ) •
        circleSobolevClassicalJet T (m+4) f ⟨j.val,by omega⟩ = _
    rw [hjet j,circle_normal_graph_coordinates]
    have hs : (Real.sqrt 2)^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
    fin_cases j <;> norm_num [hs,pow_succ,Complex.ofReal_mul]
    all_goals rfl
  · rw [circle_sobolev_physical_jet_lift_value,circle_continuous_l2_smul,
      circle_sobolev_classical_jet_l2,circle_sobolev_truncation_coordinate]
    have hs : (Real.sqrt 2)^4=(4:ℝ) := by
      nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),sq_nonneg ((Real.sqrt 2)^2-2)]
    change (((Real.sqrt 2)^4:ℝ):ℂ) • _ = _
    rw [hs]
    rfl

end Lemniscate
