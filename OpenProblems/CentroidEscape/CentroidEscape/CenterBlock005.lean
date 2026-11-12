import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.CenterStep005
import CentroidEscape.CenterStep006
import CentroidEscape.CenterStep007
import CentroidEscape.CenterStep008
import CentroidEscape.CenterStep009

namespace CentroidEscape.CenterBlockData.Block005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step006.inputData=Step005.endpointData := by decide +kernel

theorem glue1 : Step007.inputData=Step006.endpointData := by decide +kernel

theorem glue2 : Step008.inputData=Step007.endpointData := by decide +kernel

theorem glue3 : Step009.inputData=Step008.endpointData := by decide +kernel

noncomputable def terminalData : FixedTaylorState := ⟨#[Step009.endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step005.stepData
  | 1=>Step006.stepData
  | 2=>Step007.stepData
  | 3=>Step008.stepData
  | 4=>Step009.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step005.stepData=true ∧
      (∀ i : Fin 7, Step006.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step005.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step005.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step005.allStagesChecked,?_,Step005.initialMarginCheck⟩
    intro i
    rw [Step006.inputCoefficient,← Step005.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step006.stepData=true ∧
      (∀ i : Fin 7, Step007.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step006.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step006.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step006.allStagesChecked,?_,Step006.initialMarginCheck⟩
    intro i
    rw [Step007.inputCoefficient,← Step006.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step007.stepData=true ∧
      (∀ i : Fin 7, Step008.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step007.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step007.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step007.allStagesChecked,?_,Step007.initialMarginCheck⟩
    intro i
    rw [Step008.inputCoefficient,← Step007.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step008.stepData=true ∧
      (∀ i : Fin 7, Step009.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step008.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step008.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step008.allStagesChecked,?_,Step008.initialMarginCheck⟩
    intro i
    rw [Step009.inputCoefficient,← Step008.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step009.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step009.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step009.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step009.allStagesChecked,?_,Step009.initialMarginCheck⟩
    intro i
    change Step009.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step009.stepData)[i.val]
    rw [← Step009.endpointCorrect]

end CentroidEscape.CenterBlockData.Block005
