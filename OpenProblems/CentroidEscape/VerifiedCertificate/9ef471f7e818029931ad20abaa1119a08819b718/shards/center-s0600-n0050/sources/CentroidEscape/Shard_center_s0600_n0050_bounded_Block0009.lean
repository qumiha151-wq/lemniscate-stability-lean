import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0645
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0646
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0647
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0648
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0649

namespace CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0646.inputData=Step0645.endpointData := by decide +kernel

theorem glue1 : Step0647.inputData=Step0646.endpointData := by decide +kernel

theorem glue2 : Step0648.inputData=Step0647.endpointData := by decide +kernel

theorem glue3 : Step0649.inputData=Step0648.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0645.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0649.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0645.stepData
  | 1=>Step0646.stepData
  | 2=>Step0647.stepData
  | 3=>Step0648.stepData
  | 4=>Step0649.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0645.stepData=true ∧
      (∀ i : Fin 7, Step0646.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0645.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0645.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0645.allStagesChecked,?_,Step0645.initialMarginCheck⟩
    intro i
    rw [Step0646.inputCoefficient,← Step0645.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0646.stepData=true ∧
      (∀ i : Fin 7, Step0647.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0646.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0646.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0646.allStagesChecked,?_,Step0646.initialMarginCheck⟩
    intro i
    rw [Step0647.inputCoefficient,← Step0646.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0647.stepData=true ∧
      (∀ i : Fin 7, Step0648.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0647.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0647.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0647.allStagesChecked,?_,Step0647.initialMarginCheck⟩
    intro i
    rw [Step0648.inputCoefficient,← Step0647.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0648.stepData=true ∧
      (∀ i : Fin 7, Step0649.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0648.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0648.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0648.allStagesChecked,?_,Step0648.initialMarginCheck⟩
    intro i
    rw [Step0649.inputCoefficient,← Step0648.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0649.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0649.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0649.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0649.allStagesChecked,?_,Step0649.initialMarginCheck⟩
    intro i
    change Step0649.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0649.stepData)[i.val]
    rw [← Step0649.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0645.stepData.coefficient 0 i=Step0645.inputData[i.val]
  exact Step0645.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.Block0009
