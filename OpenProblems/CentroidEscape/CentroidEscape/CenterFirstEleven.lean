import CentroidEscape.CenterFirstTen
import CentroidEscape.CenterCompactStep010

/-! Connect the independently checked eleventh polynomial step to the frozen ten-step segment. -/
namespace CentroidEscape.CenterCompactData.FirstEleven
open MetricStability CenterBlockData
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

noncomputable def terminalData : FixedTaylorState := ⟨#[Step010.endpointData], #[]⟩

noncomputable def eleventhStages : ℕ → FixedTaylorState
  | 0 => Step010.stepData
  | _ => terminalData

theorem eleventhChecked : Order60SegmentValid mesh stepTime 1 eleventhStages := by
  intro j hj
  have hz : j=0 := by omega
  subst j
  change checkOrderTaylorData mesh 60 Step010.stepData=true ∧
    (∀ i : Fin 7, terminalData.coefficient 0 i=
      (evaluateFixedTaylorOrder mesh 60 stepTime Step010.stepData)[i.val]) ∧
    checkBallCanonicalMargin (fun i=>(Step010.stepData.coefficient 0 i).toRational mesh)=true
  refine ⟨Step010.allStagesChecked, ?_, Step010.initialMarginCheck⟩
  intro i
  change Step010.endpointData[i.val]=_
  rw [← Step010.endpointCorrect]

theorem boundary : ∀ i : Fin 7,
    (CenterBlockData.FirstTen.stages 10).coefficient 0 i=(eleventhStages 0).coefficient 0 i := by
  intro i
  change Step009.endpointData[i.val]=Step010.stepData.coefficient 0 i
  rw [Step010.inputCoefficient]
  have he : Step009.endpointData=Step010.inputData := by decide +kernel
  rw [he]

noncomputable def stages : ℕ → FixedTaylorState :=
  appendTaylorStages 10 CenterBlockData.FirstTen.stages eleventhStages

theorem checked : Order60SegmentValid mesh stepTime 11 stages :=
  Order60SegmentValid.append CenterBlockData.FirstTen.checked eleventhChecked boundary

end CentroidEscape.CenterCompactData.FirstEleven

#print axioms CentroidEscape.CenterCompactData.FirstEleven.checked
