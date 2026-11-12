import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.CenterStep000
import CentroidEscape.CenterStep001
import CentroidEscape.CenterStep002
import CentroidEscape.CenterStep003
import CentroidEscape.CenterStep004

namespace CentroidEscape.CenterBlockData.Block000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step001.inputData=Step000.endpointData := by decide +kernel

theorem glue1 : Step002.inputData=Step001.endpointData := by decide +kernel

theorem glue2 : Step003.inputData=Step002.endpointData := by decide +kernel

theorem glue3 : Step004.inputData=Step003.endpointData := by decide +kernel

noncomputable def terminalData : FixedTaylorState := ⟨#[Step004.endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step000.stepData
  | 1=>Step001.stepData
  | 2=>Step002.stepData
  | 3=>Step003.stepData
  | 4=>Step004.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step000.stepData=true ∧
      (∀ i : Fin 7, Step001.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step000.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step000.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step000.allStagesChecked,?_,Step000.initialMarginCheck⟩
    intro i
    rw [Step001.inputCoefficient,← Step000.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step001.stepData=true ∧
      (∀ i : Fin 7, Step002.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step001.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step001.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step001.allStagesChecked,?_,Step001.initialMarginCheck⟩
    intro i
    rw [Step002.inputCoefficient,← Step001.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step002.stepData=true ∧
      (∀ i : Fin 7, Step003.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step002.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step002.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step002.allStagesChecked,?_,Step002.initialMarginCheck⟩
    intro i
    rw [Step003.inputCoefficient,← Step002.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step003.stepData=true ∧
      (∀ i : Fin 7, Step004.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step003.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step003.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step003.allStagesChecked,?_,Step003.initialMarginCheck⟩
    intro i
    rw [Step004.inputCoefficient,← Step003.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step004.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step004.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step004.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step004.allStagesChecked,?_,Step004.initialMarginCheck⟩
    intro i
    change Step004.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step004.stepData)[i.val]
    rw [← Step004.endpointCorrect]

end CentroidEscape.CenterBlockData.Block000
