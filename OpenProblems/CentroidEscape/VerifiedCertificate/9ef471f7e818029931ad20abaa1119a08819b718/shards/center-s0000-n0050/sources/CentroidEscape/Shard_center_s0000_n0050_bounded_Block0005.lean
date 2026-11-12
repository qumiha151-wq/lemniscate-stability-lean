import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0000_n0050_bounded_Step0025
import CentroidEscape.Shard_center_s0000_n0050_bounded_Step0026
import CentroidEscape.Shard_center_s0000_n0050_bounded_Step0027
import CentroidEscape.Shard_center_s0000_n0050_bounded_Step0028
import CentroidEscape.Shard_center_s0000_n0050_bounded_Step0029

namespace CentroidEscape.CertificateShards.Shard_center_s0000_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0026.inputData=Step0025.endpointData := by decide +kernel

theorem glue1 : Step0027.inputData=Step0026.endpointData := by decide +kernel

theorem glue2 : Step0028.inputData=Step0027.endpointData := by decide +kernel

theorem glue3 : Step0029.inputData=Step0028.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0025.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0029.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0025.stepData
  | 1=>Step0026.stepData
  | 2=>Step0027.stepData
  | 3=>Step0028.stepData
  | 4=>Step0029.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0025.stepData=true ∧
      (∀ i : Fin 7, Step0026.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0025.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0025.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0025.allStagesChecked,?_,Step0025.initialMarginCheck⟩
    intro i
    rw [Step0026.inputCoefficient,← Step0025.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0026.stepData=true ∧
      (∀ i : Fin 7, Step0027.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0026.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0026.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0026.allStagesChecked,?_,Step0026.initialMarginCheck⟩
    intro i
    rw [Step0027.inputCoefficient,← Step0026.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0027.stepData=true ∧
      (∀ i : Fin 7, Step0028.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0027.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0027.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0027.allStagesChecked,?_,Step0027.initialMarginCheck⟩
    intro i
    rw [Step0028.inputCoefficient,← Step0027.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0028.stepData=true ∧
      (∀ i : Fin 7, Step0029.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0028.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0028.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0028.allStagesChecked,?_,Step0028.initialMarginCheck⟩
    intro i
    rw [Step0029.inputCoefficient,← Step0028.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0029.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0029.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0029.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0029.allStagesChecked,?_,Step0029.initialMarginCheck⟩
    intro i
    change Step0029.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0029.stepData)[i.val]
    rw [← Step0029.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0025.stepData.coefficient 0 i=Step0025.inputData[i.val]
  exact Step0025.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0000_n0050_bounded.Block0005
